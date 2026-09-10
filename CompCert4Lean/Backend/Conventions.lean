import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Config
import CompCert4Lean.Backend.Locations
import CompCert4Lean.X86.Conventions1

/-!
# Backend calling conventions

Definition-bearing translation of CompCert's `backend/Conventions.v`. Proof
declarations assigned to later proof migration are represented by exact
transparent proposition descriptors. The processor-dependent convention API's
immutable compiler configuration is threaded through every source definition
that observes argument placement or the callee-save classification.
-/

namespace CompCert4Lean.Backend.Conventions

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zGe := ZArith.BinInt.Z.ge
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zMax := ZArith.BinInt.Z.max

private abbrev listFoldLeft {A B : Type} (f : A → B → A)
    (l : List B) (a0 : A) : A :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.fold_left f l a0

private abbrev listForallb {A : Type} (f : A → Bool) (l : List A) : Bool :=
  CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb f l

private abbrev locArguments :=
  CompCert4Lean.X86.Conventions1.loc_arguments

private abbrev locArgumentAcceptable :=
  CompCert4Lean.X86.Conventions1.loc_argument_acceptable

private abbrev isCalleeSave :=
  CompCert4Lean.X86.Conventions1.is_callee_save

private abbrev locResult :=
  CompCert4Lean.X86.Conventions1.loc_result

/-! ## Acceptable argument locations -/

def loc_arguments_acceptable_2Statement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature) (l : loc),
    l ∈ regs_of_rpairs (locArguments cfg s) →
      locArgumentAcceptable cfg l

/-! ## Stack size of function arguments -/

def max_outgoing_1 (accu : Z) : loc → Z
  | .S .Outgoing ofs ty =>
      zMax accu (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))
  | _ => accu

def max_outgoing_2 (accu : Z) : rpair loc → Z
  | .One l => max_outgoing_1 accu l
  | .Twolong l1 l2 => max_outgoing_1 (max_outgoing_1 accu l1) l2

def size_arguments (cfg : CompilerConfig) (s : signature) : Z :=
  listFoldLeft max_outgoing_2 (locArguments cfg s) z0

def fold_max_outgoing_aboveStatement : Prop :=
  ∀ (l : List (rpair loc)) (n : Z),
    zGe (listFoldLeft max_outgoing_2 l n) n

def loc_arguments_boundedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature) (ofs : Z) (ty : typ),
    S Outgoing ofs ty ∈ regs_of_rpairs (locArguments cfg s) →
      zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))
        (size_arguments cfg s)

/-! ## Location of function parameters -/

def parameter_of_argument : loc → loc
  | .S .Outgoing n ty => .S .Incoming n ty
  | l => l

def loc_parameters (cfg : CompilerConfig) (s : signature) : List (rpair loc) :=
  (locArguments cfg s).map (map_rpair parameter_of_argument)

def incoming_slot_in_parametersStatement : Prop :=
  ∀ (cfg : CompilerConfig) (ofs : Z) (ty : typ) (sg : signature),
    S Incoming ofs ty ∈ regs_of_rpairs (loc_parameters cfg sg) →
      S Outgoing ofs ty ∈ regs_of_rpairs (locArguments cfg sg)

/-! ## Tail calls -/

def tailcall_possible (cfg : CompilerConfig) (s : signature) : Prop :=
  ∀ l, l ∈ regs_of_rpairs (locArguments cfg s) →
    match l with
    | .R _ => True
    | .S _ _ _ => False

def tailcall_is_possible (cfg : CompilerConfig) (sg : signature) : Bool :=
  listForallb
    (fun l =>
      match l with
      | .R _ => true
      | .S _ _ _ => false)
    (regs_of_rpairs (locArguments cfg sg))

def tailcall_is_possible_correctStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature),
    tailcall_is_possible cfg s = true → tailcall_possible cfg s

def zero_size_arguments_tailcall_possibleStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature),
    size_arguments cfg sg = z0 → tailcall_possible cfg sg

/-! ## Callee-save locations -/

def callee_save_loc (cfg : CompilerConfig) : loc → Prop
  | .R r => isCalleeSave cfg r = true
  | .S sl _ _ => sl ≠ Outgoing

def agree_callee_save (cfg : CompilerConfig) (ls1 ls2 : Locmap.t) : Prop :=
  ∀ l, callee_save_loc cfg l → ls1 l = ls2 l

/-! ## Assigning result locations -/

def locmap_get_set_loc_resultStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature) (v : val) (rs : Locmap.t)
      (l : loc),
    (match l with
      | .R r => isCalleeSave cfg r = true
      | .S _ _ _ => True) →
      Locmap.setpair (locResult sg) v rs l = rs l

def locmap_get_set_loc_result_callee_saveStatement : Prop :=
  ∀ (cfg : CompilerConfig) (sg : signature) (v : val) (rs : Locmap.t)
      (l : loc),
    callee_save_loc cfg l →
      Locmap.setpair (locResult sg) v rs l = rs l

end CompCert4Lean.Backend.Conventions

namespace CompCert4Lean.Backend.Conventions

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev ProofZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev proofIntOfZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ
private abbrev proofZLe := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
private abbrev proofZGe := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.ge
private abbrev proofZMax := CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max

private theorem proof_zle_max_left (x y : ProofZ) : proofZLe x (proofZMax x y) := by
  change proofIntOfZ x ≤ proofIntOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max x y)
  by_cases h : proofIntOfZ x ≤ proofIntOfZ y
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h]
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h]

private theorem proof_zle_max_right (x y : ProofZ) : proofZLe y (proofZMax x y) := by
  change proofIntOfZ y ≤ proofIntOfZ
    (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max x y)
  by_cases h : proofIntOfZ x ≤ proofIntOfZ y
  · simp [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h]
  · have hxy : proofIntOfZ y ≤ proofIntOfZ x := by omega
    simpa [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max, h] using hxy

private theorem proof_zle_trans {x y z : ProofZ}
    (hxy : proofZLe x y) (hyz : proofZLe y z) : proofZLe x z := by
  change proofIntOfZ x ≤ proofIntOfZ y at hxy
  change proofIntOfZ y ≤ proofIntOfZ z at hyz
  change proofIntOfZ x ≤ proofIntOfZ z
  exact Int.le_trans hxy hyz

private theorem proof_zge_trans {x y z : ProofZ}
    (hxy : proofZGe x y) (hyz : proofZGe y z) : proofZGe x z := by
  change proofIntOfZ y ≤ proofIntOfZ x at hxy
  change proofIntOfZ z ≤ proofIntOfZ y at hyz
  change proofIntOfZ z ≤ proofIntOfZ x
  exact Int.le_trans hyz hxy

private theorem proof_max_outgoing_1_above
    (accu : ProofZ) (l : CompCert4Lean.Backend.Locations.loc) :
    proofZGe (max_outgoing_1 accu l) accu := by
  cases l with
  | R r =>
      change proofIntOfZ accu ≤ proofIntOfZ accu
      exact Int.le_refl _
  | S sl ofs ty =>
      cases sl with
      | Local =>
          change proofIntOfZ accu ≤ proofIntOfZ accu
          exact Int.le_refl _
      | Incoming =>
          change proofIntOfZ accu ≤ proofIntOfZ accu
          exact Int.le_refl _
      | Outgoing =>
          change proofIntOfZ accu ≤ proofIntOfZ
            (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.max accu
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
                (CompCert4Lean.Backend.Locations.typesize ty)))
          exact proof_zle_max_left accu _

private theorem proof_fold_max_outgoing_above_aux : fold_max_outgoing_aboveStatement := by
  intro l n
  induction l generalizing n with
  | nil => change proofIntOfZ n ≤ proofIntOfZ n; exact Int.le_refl _
  | cons p ps ih =>
      change proofZGe (List.foldl max_outgoing_2 n (p :: ps)) n
      simp only [List.foldl]
      have hp : proofZGe (max_outgoing_2 n p) n := by
        cases p with
        | One l => exact proof_max_outgoing_1_above n l
        | Twolong l1 l2 =>
            change proofZGe (max_outgoing_1 (max_outgoing_1 n l1) l2) n
            exact proof_zge_trans (proof_max_outgoing_1_above _ l2)
              (proof_max_outgoing_1_above n l1)
      exact proof_zge_trans (ih (max_outgoing_2 n p)) hp

private theorem proof_target_le_max_outgoing_2
    (ofs : ProofZ) (ty : typ) (p : rpair CompCert4Lean.Backend.Locations.loc)
    (n : ProofZ)
    (h : S Outgoing ofs ty ∈ regs_of_rpair p) :
    proofZLe
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
        (CompCert4Lean.Backend.Locations.typesize ty))
      (max_outgoing_2 n p) := by
  cases p with
  | One l =>
      simp [regs_of_rpair] at h
      subst l
      exact proof_zle_max_right n _
  | Twolong l1 l2 =>
      simp [regs_of_rpair] at h
      rcases h with h | h
      · subst l1
        change proofZLe
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
            (CompCert4Lean.Backend.Locations.typesize ty))
          (max_outgoing_1 (max_outgoing_1 n (S Outgoing ofs ty)) l2)
        apply proof_zle_trans (proof_zle_max_right n _)
        exact proof_max_outgoing_1_above _ l2
      · subst l2
        change proofZLe
          (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
            (CompCert4Lean.Backend.Locations.typesize ty))
          (max_outgoing_1 (max_outgoing_1 n l1) (S Outgoing ofs ty))
        exact proof_zle_max_right _ _

private theorem proof_target_le_fold
    (ofs : ProofZ) (ty : typ) (l : List (rpair CompCert4Lean.Backend.Locations.loc))
    (n : ProofZ)
    (h : S Outgoing ofs ty ∈ regs_of_rpairs l) :
    proofZLe
      (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
        (CompCert4Lean.Backend.Locations.typesize ty))
      (listFoldLeft max_outgoing_2 l n) := by
  induction l generalizing n with
  | nil => exact (_root_.List.not_mem_nil h).elim
  | cons p ps ih =>
      change S Outgoing ofs ty ∈ regs_of_rpair p ++ regs_of_rpairs ps at h
      rcases (_root_.List.mem_append.mp h) with hp | hps
      · change proofZLe _ (listFoldLeft max_outgoing_2 (p :: ps) n)
        change proofZLe _ (listFoldLeft max_outgoing_2 ps (max_outgoing_2 n p))
        apply proof_zle_trans (proof_target_le_max_outgoing_2 ofs ty p n hp)
        exact proof_fold_max_outgoing_above_aux ps (max_outgoing_2 n p)
      · change proofZLe _ (listFoldLeft max_outgoing_2 ps (max_outgoing_2 n p))
        exact ih (max_outgoing_2 n p) hps
 
theorem fold_max_outgoing_above : fold_max_outgoing_aboveStatement :=
  proof_fold_max_outgoing_above_aux

theorem loc_arguments_bounded : loc_arguments_boundedStatement := by
  intro cfg s ofs ty h
  exact proof_target_le_fold ofs ty (locArguments cfg s) z0 h

private theorem proof_no_incoming_win64 :
    ∀ (tys : List typ) (r ofs : ProofZ) (xofs : ProofZ) (xty : typ),
      S Incoming xofs xty ∉
        regs_of_rpairs (CompCert4Lean.X86.Conventions1.loc_arguments_win64 tys r ofs) := by
  intro tys
  induction tys with
  | nil =>
      intro r ofs xofs xty h
      simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64,
        regs_of_rpairs] at h
  | cons ty tys ih =>
      intro r ofs xofs xty h
      cases ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.int_param_regs_win64 r with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ h
          | some ireg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ h
      | Tfloat | Tsingle =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.float_param_regs_win64 r with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ h
          | some freg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ h

private theorem proof_no_incoming_elf64 :
    ∀ (tys : List typ) (ir fr ofs : ProofZ) (xofs : ProofZ) (xty : typ),
      S Incoming xofs xty ∉
        regs_of_rpairs (CompCert4Lean.X86.Conventions1.loc_arguments_elf64 tys ir fr ofs) := by
  intro tys
  induction tys with
  | nil =>
      intro ir fr ofs xofs xty h
      simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64,
        regs_of_rpairs] at h
  | cons ty tys ih =>
      intro ir fr ofs xofs xty h
      cases ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.int_param_regs_elf64 ir with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ _ h
          | some ireg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ _ h
      | Tfloat | Tsingle =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.float_param_regs_elf64 fr with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ _ h
          | some freg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · simpa [regs_of_rpair] using h
              · exact ih _ _ _ _ _ h

private theorem proof_no_incoming_arguments :
    ∀ (cfg : CompilerConfig) (s : signature) (xofs : ProofZ) (xty : typ),
      S Incoming xofs xty ∉ regs_of_rpairs (locArguments cfg s) := by
  intro cfg s xofs xty h
  change S Incoming xofs xty ∈
    regs_of_rpairs (CompCert4Lean.X86.Conventions1.loc_arguments cfg s) at h
  simp only [CompCert4Lean.X86.Conventions1.loc_arguments,
    CompCert4Lean.X86_64.Archi.ptr64, ↓reduceIte] at h
  split at h <;> rename_i habi
  · exact proof_no_incoming_win64 _ _ _ _ _ h
  · exact proof_no_incoming_elf64 _ _ _ _ _ _ h

private theorem proof_regs_map_parameter :
    ∀ (l : List (rpair CompCert4Lean.Backend.Locations.loc)),
      regs_of_rpairs (l.map (map_rpair parameter_of_argument)) =
        List.map parameter_of_argument (regs_of_rpairs l) := by
  intro l
  induction l with
  | nil => rfl
  | cons p ps ih =>
      cases p <;> simp [map_rpair, regs_of_rpair, regs_of_rpairs, ih]

private theorem proof_list_map_mem_inv {A B : Type} (f : A → B)
    (l : List A) (y : B) (h : y ∈ List.map f l) :
    ∃ x, y = f x ∧ x ∈ l := by
  induction l with
  | nil => exact (_root_.List.not_mem_nil h).elim
  | cons a l ih =>
      simp only [List.map, _root_.List.mem_cons] at h
      rcases h with h | h
      · exact ⟨a, h, _root_.List.Mem.head l⟩
      · rcases ih h with ⟨x, hx, hxl⟩
        exact ⟨x, hx, _root_.List.Mem.tail a hxl⟩

theorem incoming_slot_in_parameters : incoming_slot_in_parametersStatement := by
  intro cfg ofs ty sg h
  have hmap : S Incoming ofs ty ∈
      List.map parameter_of_argument (regs_of_rpairs (locArguments cfg sg)) := by
    rw [← proof_regs_map_parameter (locArguments cfg sg)]
    exact h
  obtain ⟨x, hx, hmem⟩ := proof_list_map_mem_inv parameter_of_argument
    (regs_of_rpairs (locArguments cfg sg)) (S Incoming ofs ty) hmap
  cases x with
  | R r => cases hx
  | S sl pos typx =>
      cases sl with
      | Local => cases hx
      | Incoming =>
          exfalso
          exact proof_no_incoming_arguments cfg sg pos typx hmem
      | Outgoing =>
          cases hx
          exact hmem

end CompCert4Lean.Backend.Conventions
