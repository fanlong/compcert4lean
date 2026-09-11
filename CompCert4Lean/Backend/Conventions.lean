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

namespace CompCert4Lean.Backend.Conventions

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev ConvZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev convZ0 : ConvZ := .Z0
private abbrev convZ1 := ZArith.BinInt.Z.of_nat 1
private abbrev convZ2 := ZArith.BinInt.Z.of_nat 2
private abbrev convZAdd := ZArith.BinInt.Z.add
private abbrev convZMul := ZArith.BinInt.Z.mul
private abbrev convZLe := ZArith.BinInt.Z.le
private abbrev convZDivide := ZArith.BinInt.Z.divide
private abbrev convIntOfZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ

private theorem conv_zle_zero_refl : convZLe convZ0 convZ0 := by
  change convIntOfZ convZ0 ≤ convIntOfZ convZ0
  exact Int.le_refl _

private theorem conv_zle_add_two (ofs : ConvZ) (h : convZLe convZ0 ofs) :
    convZLe convZ0 (convZAdd ofs convZ2) := by
  change 0 ≤ convIntOfZ ofs at h
  change 0 ≤ convIntOfZ (convZAdd ofs convZ2)
  simp only [convZAdd, ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change 0 ≤ convIntOfZ ofs + 2
  omega

private theorem conv_zdivide_zero (a : ConvZ) : convZDivide a convZ0 := by
  refine ⟨convZ0, ?_⟩
  change convZ0 = convZMul a convZ0
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change convIntOfZ convZ0 =
    convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (convIntOfZ a * convIntOfZ convZ0))
  calc
    convIntOfZ convZ0 = 0 := by rfl
    _ = convIntOfZ a * convIntOfZ convZ0 := by
      have hz : convIntOfZ convZ0 = 0 := by rfl
      rw [hz]
      simp
    _ = convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (convIntOfZ a * convIntOfZ convZ0)) := by
      symm
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _

private theorem conv_zdivide_add_two (ofs : ConvZ) (h : convZDivide convZ2 ofs) :
    convZDivide convZ2 (convZAdd ofs convZ2) := by
  rcases h with ⟨k, hk⟩
  refine ⟨convZAdd k convZ1, ?_⟩
  rw [hk]
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change convIntOfZ (convZAdd (convZMul convZ2 k) convZ2) =
    convIntOfZ (convZMul convZ2 (convZAdd k convZ1))
  change convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (convIntOfZ convZ2 * convIntOfZ k)) + convIntOfZ convZ2)) =
    convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (convIntOfZ convZ2 * convIntOfZ
        (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
          (convIntOfZ k + convIntOfZ convZ1))))
  simp only [convIntOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  have h1 : convIntOfZ convZ1 = 1 := by rfl
  have h2 : convIntOfZ convZ2 = 2 := by rfl
  simp only [h1, h2]
  omega

private theorem conv_zdivide_one (ofs : ConvZ) : convZDivide convZ1 ofs := by
  refine ⟨ofs, ?_⟩
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change convIntOfZ ofs =
    convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (convIntOfZ convZ1 * convIntOfZ ofs))
  calc
    convIntOfZ ofs = convIntOfZ convZ1 * convIntOfZ ofs := by
      have hz : convIntOfZ convZ1 = 1 := by rfl
      rw [hz]
      simp
    _ = convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
        (convIntOfZ convZ1 * convIntOfZ ofs)) := by
      exact CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt _ |>.symm

private theorem conv_typealign_divide (ty : typ) (ofs : ConvZ)
    (h : convZDivide convZ2 ofs) :
    convZDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs := by
  cases ty with
  | Tint => exact conv_zdivide_one ofs
  | Tlong => exact h
  | Tfloat => exact conv_zdivide_one ofs
  | Tsingle => exact conv_zdivide_one ofs
  | Tany32 => exact conv_zdivide_one ofs
  | Tany64 => exact conv_zdivide_one ofs

private theorem conv_stack_acceptable (cfg : CompCert4Lean.Config.CompilerConfig)
    (ofs : ConvZ) (ty : typ) (hnonneg : convZLe convZ0 ofs)
    (hdiv : convZDivide convZ2 ofs) :
    CompCert4Lean.X86.Conventions1.loc_argument_acceptable cfg
      (S Outgoing ofs ty) := by
  change convZLe convZ0 ofs ∧
    convZDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs
  exact ⟨hnonneg, conv_typealign_divide ty ofs hdiv⟩

private theorem conv_stack_head
    (cfg : CompCert4Lean.Config.CompilerConfig) (ofs : ConvZ) (ty : typ)
    (l : loc) (h : l ∈ regs_of_rpair (One (S Outgoing ofs ty)))
    (hnonneg : convZLe convZ0 ofs) (hdiv : convZDivide convZ2 ofs) :
    CompCert4Lean.X86.Conventions1.loc_argument_acceptable cfg l := by
  have hl : l = S Outgoing ofs ty := by
    simpa [regs_of_rpair] using h
  subst l
  exact conv_stack_acceptable cfg ofs ty hnonneg hdiv

private theorem conv_register_head
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg) (l : loc)
    (h : l ∈ regs_of_rpair (One (R r)))
    (hsave : CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false) :
    CompCert4Lean.X86.Conventions1.loc_argument_acceptable cfg l := by
  have hl : l = R r := by
    simpa [regs_of_rpair] using h
  subst l
  exact hsave

private theorem conv_win64_int_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (h : r ∈ CompCert4Lean.X86.Conventions1.int_param_regs_win64) :
    CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false := by
  simp [CompCert4Lean.X86.Conventions1.int_param_regs_win64] at h
  rcases h with h | h | h | h
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl

private theorem conv_win64_float_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (h : r ∈ CompCert4Lean.X86.Conventions1.float_param_regs_win64) :
    CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false := by
  simp [CompCert4Lean.X86.Conventions1.float_param_regs_win64] at h
  rcases h with h | h | h | h
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl

private theorem conv_elf64_int_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (habi : ¬ CompCert4Lean.X86_64.Archi.win64 cfg = true)
    (h : r ∈ CompCert4Lean.X86.Conventions1.int_param_regs_elf64) :
    CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false := by
  simp [CompCert4Lean.X86.Conventions1.int_param_regs_elf64] at h
  rcases h with h | h | h | h | h | h
  · subst r; simp [CompCert4Lean.X86.Conventions1.is_callee_save,
      CompCert4Lean.X86_64.Archi.ptr64, habi]
  · subst r; simp [CompCert4Lean.X86.Conventions1.is_callee_save,
      CompCert4Lean.X86_64.Archi.ptr64, habi]
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl

private theorem conv_list_nth_z_in {A : Type} :
    ∀ (l : List A) (n : ConvZ) (x : A),
      CompCert4Lean.Lib.Coqlib.list_nth_z l n = some x → x ∈ l := by
  intro l
  induction l with
  | nil =>
      intro n x h
      simp [CompCert4Lean.Lib.Coqlib.list_nth_z] at h
  | cons a l ih =>
      intro n x h
      simp only [CompCert4Lean.Lib.Coqlib.list_nth_z] at h
      split at h <;> rename_i hn
      · simp at h
        subst x
        exact _root_.List.Mem.head l
      · exact _root_.List.Mem.tail a (ih _ _ h)

private theorem conv_elf64_float_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (h : r ∈ CompCert4Lean.X86.Conventions1.float_param_regs_elf64) :
    CompCert4Lean.X86.Conventions1.is_callee_save cfg r = false := by
  simp [CompCert4Lean.X86.Conventions1.float_param_regs_elf64] at h
  rcases h with h | h | h | h | h | h | h | h
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl
  · subst r; rfl

private theorem conv_win64_arguments_acceptable :
    ∀ (cfg : CompCert4Lean.Config.CompilerConfig)
      (tys : List typ) (r ofs : ConvZ) (l : loc),
      l ∈ regs_of_rpairs
        (CompCert4Lean.X86.Conventions1.loc_arguments_win64 tys r ofs) →
      convZLe convZ0 ofs → convZDivide convZ2 ofs →
      CompCert4Lean.X86.Conventions1.loc_argument_acceptable cfg l := by
  intro cfg tys
  induction tys with
  | nil =>
      intro r ofs l h
      simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64,
        regs_of_rpairs] at h
  | cons ty tys ih =>
      intro r ofs l h hnonneg hdiv
      cases ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.int_param_regs_win64 r with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_stack_head cfg ofs _ l h hnonneg hdiv
              · exact ih _ _ _ h (conv_zle_add_two ofs hnonneg)
                  (conv_zdivide_add_two ofs hdiv)
          | some ireg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_register_head cfg ireg l h
                  (conv_win64_int_caller_save cfg ireg
                    (conv_list_nth_z_in _ _ _ hn))
              · exact ih _ _ _ h hnonneg hdiv
      | Tfloat | Tsingle =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.float_param_regs_win64 r with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_stack_head cfg ofs _ l h hnonneg hdiv
              · exact ih _ _ _ h (conv_zle_add_two ofs hnonneg)
                  (conv_zdivide_add_two ofs hdiv)
          | some freg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_win64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_register_head cfg freg l h
                  (conv_win64_float_caller_save cfg freg
                    (conv_list_nth_z_in _ _ _ hn))
              · exact ih _ _ _ h hnonneg hdiv

private theorem conv_elf64_arguments_acceptable :
    ∀ (cfg : CompCert4Lean.Config.CompilerConfig)
      (_habi : ¬ CompCert4Lean.X86_64.Archi.win64 cfg = true)
      (tys : List typ) (ir fr ofs : ConvZ) (l : loc),
      l ∈ regs_of_rpairs
        (CompCert4Lean.X86.Conventions1.loc_arguments_elf64 tys ir fr ofs) →
      convZLe convZ0 ofs → convZDivide convZ2 ofs →
      CompCert4Lean.X86.Conventions1.loc_argument_acceptable cfg l := by
  intro cfg habi tys
  induction tys with
  | nil =>
      intro ir fr ofs l h
      simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64,
        regs_of_rpairs] at h
  | cons ty tys ih =>
      intro ir fr ofs l h hnonneg hdiv
      cases ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.int_param_regs_elf64 ir with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_stack_head cfg ofs _ l h hnonneg hdiv
              · exact ih _ _ _ _ h (conv_zle_add_two ofs hnonneg)
                  (conv_zdivide_add_two ofs hdiv)
          | some ireg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_register_head cfg ireg l h
                  (conv_elf64_int_caller_save cfg ireg habi
                    (conv_list_nth_z_in _ _ _ hn))
              · exact ih _ _ _ _ h hnonneg hdiv
      | Tfloat | Tsingle =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z
              CompCert4Lean.X86.Conventions1.float_param_regs_elf64 fr with
          | none =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_stack_head cfg ofs _ l h hnonneg hdiv
              · exact ih _ _ _ _ h (conv_zle_add_two ofs hnonneg)
                  (conv_zdivide_add_two ofs hdiv)
          | some freg =>
              simp [CompCert4Lean.X86.Conventions1.loc_arguments_elf64, hn,
                regs_of_rpairs] at h
              rcases h with h | h
              · exact conv_register_head cfg freg l h
                  (conv_elf64_float_caller_save cfg freg
                    (conv_list_nth_z_in _ _ _ hn))
              · exact ih _ _ _ _ h hnonneg hdiv

theorem loc_arguments_acceptable_2 : loc_arguments_acceptable_2Statement := by
  intro cfg s l h
  change l ∈ regs_of_rpairs
    (CompCert4Lean.X86.Conventions1.loc_arguments cfg s) at h
  simp only [CompCert4Lean.X86.Conventions1.loc_arguments,
    CompCert4Lean.X86_64.Archi.ptr64, ↓reduceIte] at h
  split at h <;> rename_i habi
  · exact conv_win64_arguments_acceptable cfg _ convZ0 convZ0 l h
      conv_zle_zero_refl (conv_zdivide_zero convZ2)
  · have habi' : ¬ CompCert4Lean.X86_64.Archi.win64 cfg = true := by
      exact habi
    exact conv_elf64_arguments_acceptable cfg habi' _ convZ0 convZ0 convZ0 l h
      conv_zle_zero_refl (conv_zdivide_zero convZ2)

end CompCert4Lean.Backend.Conventions

namespace CompCert4Lean.Backend.Conventions

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private theorem conv_loc_result_caller_save (cfg : CompilerConfig) (sg : signature) :
    forall_rpair (fun r => isCalleeSave cfg r = false) (locResult sg) := by
  change forall_rpair (fun r => isCalleeSave cfg r = false)
    (CompCert4Lean.X86.Conventions1.loc_result sg)
  unfold CompCert4Lean.X86.Conventions1.loc_result
  simp only [CompCert4Lean.X86_64.Archi.ptr64, ↓reduceIte]
  unfold CompCert4Lean.X86.Conventions1.loc_result_64
  cases hres : CompCert4Lean.Common.AST.proj_sig_res sg <;>
    simp [hres, CompCert4Lean.Common.AST.forall_rpair,
      CompCert4Lean.X86.Conventions1.is_callee_save]

private theorem conv_setpair_callee_save
    (cfg : CompilerConfig) (p : rpair mreg) (v : val) (rs : Locmap.t)
    (l : loc) (hp : forall_rpair (fun r => isCalleeSave cfg r = false) p)
    (hl : match l with
      | .R r => isCalleeSave cfg r = true
      | .S _ _ _ => True) :
    Locmap.setpair p v rs l = rs l := by
  have hdiff : ∀ r, isCalleeSave cfg r = false → Loc.diff (R r) l := by
    intro r hr
    cases l with
    | R r' =>
        change r ≠ r'
        intro heq
        subst r'
        change isCalleeSave cfg r = true at hl
        have hft : false = true := hr.symm.trans hl
        cases hft
    | S sl ofs ty => trivial
  cases p with
  | One r =>
      have hr : isCalleeSave cfg r = false := hp
      change Locmap.set (R r) v rs l = rs l
      exact Locmap.gso (R r) v rs l (hdiff r hr)
  | Twolong hi lo =>
      rcases hp with ⟨hhi, hlo⟩
      change Locmap.set (R lo) (Val.loword v)
          (Locmap.set (R hi) (Val.hiword v) rs) l = rs l
      calc
        Locmap.set (R lo) (Val.loword v)
            (Locmap.set (R hi) (Val.hiword v) rs) l =
            (Locmap.set (R hi) (Val.hiword v) rs) l :=
          Locmap.gso (R lo) (Val.loword v)
            (Locmap.set (R hi) (Val.hiword v) rs) l (hdiff lo hlo)
        _ = rs l := Locmap.gso (R hi) (Val.hiword v) rs l (hdiff hi hhi)

theorem locmap_get_set_loc_result : locmap_get_set_loc_resultStatement := by
  intro cfg sg v rs l hl
  exact conv_setpair_callee_save cfg (locResult sg) v rs l
    (conv_loc_result_caller_save cfg sg) hl

theorem locmap_get_set_loc_result_callee_save :
    locmap_get_set_loc_result_callee_saveStatement := by
  intro cfg sg v rs l hl
  apply locmap_get_set_loc_result cfg sg v rs l
  cases l with
  | R r => exact hl
  | S sl ofs ty => trivial

end CompCert4Lean.Backend.Conventions

namespace CompCert4Lean.Backend.Conventions

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Values
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

theorem tailcall_is_possible_correct : tailcall_is_possible_correctStatement := by
  intro cfg s h
  unfold tailcall_is_possible at h
  have hall :=
    (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.forallb_forall _ _).mp h
  intro l hl
  cases l with
  | R r => trivial
  | S sl ofs ty =>
      have hf := hall (S sl ofs ty) hl
      simp at hf

theorem zero_size_arguments_tailcall_possible :
    zero_size_arguments_tailcall_possibleStatement := by
  intro cfg sg hzero l hl
  have haccept := loc_arguments_acceptable_2 cfg sg l hl
  cases l with
  | R r => trivial
  | S sl ofs ty =>
      cases sl with
      | Local =>
          simpa [CompCert4Lean.X86.Conventions1.loc_argument_acceptable] using haccept
      | Incoming =>
          simpa [CompCert4Lean.X86.Conventions1.loc_argument_acceptable] using haccept
      | Outgoing =>
          have hacc :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.le
                  (.Z0 : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z) ofs ∧
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.divide
                  (CompCert4Lean.Backend.Locations.typealign ty) ofs := by
            simpa [CompCert4Lean.X86.Conventions1.loc_argument_acceptable] using haccept
          have hnonneg := hacc.1
          change 0 ≤ intOfZ ofs at hnonneg
          have hb := loc_arguments_bounded cfg sg ofs ty hl
          rw [hzero] at hb
          change intOfZ
              (CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add ofs
                (CompCert4Lean.Backend.Locations.typesize ty)) ≤ 0 at hb
          have hpos := CompCert4Lean.Backend.Locations.typesize_pos ty
          change 0 < intOfZ (CompCert4Lean.Backend.Locations.typesize ty) at hpos
          simp only [CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.add,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt] at hb
          omega

end CompCert4Lean.Backend.Conventions
