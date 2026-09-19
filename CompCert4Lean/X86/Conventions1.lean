import CompCert4Lean.Config
import CompCert4Lean.Backend.Locations

/-!
# x86 calling conventions

Definition-bearing translation of CompCert's `x86/Conventions1.v`. Proof
declarations assigned to later proof migration are represented by exact
transparent proposition descriptors. The source `Archi.win64` parameter is
threaded through the accepted immutable compiler-configuration interface.
-/

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zDivide := ZArith.BinInt.Z.divide

private abbrev z1 : Z := zOfNat 1
private abbrev z2 : Z := zOfNat 2

/-! ## Classification of machine registers -/

def is_callee_save (cfg : CompilerConfig) : mreg → Bool
  | .AX | .CX | .DX => false
  | .BX | .BP => true
  | .SI | .DI => !CompCert4Lean.X86_64.Archi.ptr64 ||
      CompCert4Lean.X86_64.Archi.win64 cfg
  | .R8 | .R9 | .R10 | .R11 => false
  | .R12 | .R13 | .R14 | .R15 => true
  | .X0 | .X1 | .X2 | .X3 | .X4 | .X5 | .X6 | .X7 => false
  | .X8 | .X9 | .X10 | .X11 | .X12 | .X13 | .X14 | .X15 =>
      CompCert4Lean.X86_64.Archi.win64 cfg
  | .FP0 => false

def destroyed_at_call (cfg : CompilerConfig) : List mreg :=
  all_mregs.filter (fun r => !(is_callee_save cfg r))

/-! ## Location of function results -/

def loc_result_32 (s : signature) : rpair mreg :=
  match proj_sig_res s with
  | .Tint | .Tany32 => .One AX
  | .Tfloat | .Tsingle => .One FP0
  | .Tany64 => .One X0
  | .Tlong => .Twolong DX AX

def loc_result_64 (s : signature) : rpair mreg :=
  match proj_sig_res s with
  | .Tint | .Tlong | .Tany32 | .Tany64 => .One AX
  | .Tfloat | .Tsingle => .One X0

def loc_result : signature → rpair mreg :=
  if CompCert4Lean.X86_64.Archi.ptr64 then loc_result_64 else loc_result_32

def loc_result_typeStatement : Prop :=
  ∀ sig : signature,
    subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true

def loc_result_caller_saveStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature),
    forall_rpair (fun r => is_callee_save cfg r = false) (loc_result s)

def loc_result_pairStatement : Prop :=
  ∀ sg : signature,
    match loc_result sg with
    | .One _ => True
    | .Twolong r1 r2 =>
        r1 ≠ r2 ∧ proj_sig_res sg = Tlong ∧
          subtype Tint (mreg_type r1) = true ∧
          subtype Tint (mreg_type r2) = true ∧
          CompCert4Lean.X86_64.Archi.ptr64 = false

def loc_result_extenStatement : Prop :=
  ∀ s1 s2 : signature,
    s1.sig_res = s2.sig_res → loc_result s1 = loc_result s2

/-! ## Location of function arguments -/

def loc_arguments_32 : List typ → Z → List (rpair loc)
  | [], _ => []
  | ty :: tys, ofs =>
      (match ty with
      | .Tlong =>
          .Twolong (.S Outgoing (zAdd ofs z1) Tint) (.S Outgoing ofs Tint)
      | _ => .One (.S Outgoing ofs ty)) ::
        loc_arguments_32 tys
          (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))

def int_param_regs_elf64 : List mreg :=
  [DI, SI, DX, CX, R8, R9]

def float_param_regs_elf64 : List mreg :=
  [X0, X1, X2, X3, X4, X5, X6, X7]

def loc_arguments_elf64 :
    List typ → Z → Z → Z → List (rpair loc)
  | [], _, _, _ => []
  | ty :: tys, ir, fr, ofs =>
      match ty with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z int_param_regs_elf64 ir with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_elf64 tys ir fr (zAdd ofs z2)
          | some ireg =>
              .One (.R ireg) ::
                loc_arguments_elf64 tys (zAdd ir z1) fr ofs
      | .Tfloat | .Tsingle =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z float_param_regs_elf64 fr with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_elf64 tys ir fr (zAdd ofs z2)
          | some freg =>
              .One (.R freg) ::
                loc_arguments_elf64 tys ir (zAdd fr z1) ofs

def int_param_regs_win64 : List mreg :=
  [CX, DX, R8, R9]

def float_param_regs_win64 : List mreg :=
  [X0, X1, X2, X3]

def loc_arguments_win64 : List typ → Z → Z → List (rpair loc)
  | [], _, _ => []
  | ty :: tys, r, ofs =>
      match ty with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z int_param_regs_win64 r with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_win64 tys r (zAdd ofs z2)
          | some ireg =>
              .One (.R ireg) ::
                loc_arguments_win64 tys (zAdd r z1) ofs
      | .Tfloat | .Tsingle =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z float_param_regs_win64 r with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_win64 tys r (zAdd ofs z2)
          | some freg =>
              .One (.R freg) ::
                loc_arguments_win64 tys (zAdd r z1) ofs

def loc_arguments (cfg : CompilerConfig) (s : signature) : List (rpair loc) :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    if CompCert4Lean.X86_64.Archi.win64 cfg then
      loc_arguments_win64 (proj_sig_args s) z0 z0
    else
      loc_arguments_elf64 (proj_sig_args s) z0 z0 z0
  else
    loc_arguments_32 (proj_sig_args s) z0

def loc_argument_acceptable (cfg : CompilerConfig) : loc → Prop
  | .R r => is_callee_save cfg r = false
  | .S .Outgoing ofs ty =>
      zLe z0 ofs ∧ zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs
  | _ => False

def loc_argument_32_charact (ofs : Z) : loc → Prop
  | .S .Outgoing ofs' ty =>
      zLe ofs ofs' ∧ CompCert4Lean.Backend.Locations.typealign ty = z1
  | _ => False

def loc_argument_elf64_charact (ofs : Z) : loc → Prop
  | .R r => r ∈ int_param_regs_elf64 ∨ r ∈ float_param_regs_elf64
  | .S .Outgoing ofs' _ => zLe ofs ofs' ∧ zDivide z2 ofs'
  | _ => False

def loc_argument_win64_charact (ofs : Z) : loc → Prop
  | .R r => r ∈ int_param_regs_win64 ∨ r ∈ float_param_regs_win64
  | .S .Outgoing ofs' _ => zLe ofs ofs' ∧ zDivide z2 ofs'
  | _ => False

def loc_arguments_32_charactStatement : Prop :=
  ∀ (tyl : List typ) (ofs : Z) (p : rpair loc),
    p ∈ loc_arguments_32 tyl ofs →
      forall_rpair (loc_argument_32_charact ofs) p

def loc_arguments_elf64_charactStatement : Prop :=
  ∀ (tyl : List typ) (ir fr ofs : Z) (p : rpair loc),
    p ∈ loc_arguments_elf64 tyl ir fr ofs → zDivide z2 ofs →
      forall_rpair (loc_argument_elf64_charact ofs) p

def loc_arguments_win64_charactStatement : Prop :=
  ∀ (tyl : List typ) (r ofs : Z) (p : rpair loc),
    p ∈ loc_arguments_win64 tyl r ofs → zDivide z2 ofs →
      forall_rpair (loc_argument_win64_charact ofs) p

def loc_arguments_acceptableStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature) (p : rpair loc),
    p ∈ loc_arguments cfg s →
      forall_rpair (loc_argument_acceptable cfg) p

def loc_arguments_mainStatement : Prop :=
  ∀ cfg : CompilerConfig, loc_arguments cfg signature_main = []

/-! ## Normalization of function results and parameters -/

def return_value_needs_normalization : xtype → Bool
  | .Xint8signed | .Xint8unsigned | .Xint16signed | .Xint16unsigned => true
  | _ => false

def parameter_needs_normalization (_t : xtype) : Bool :=
  false

end CompCert4Lean.X86.Conventions1

namespace CompCert4Lean.X86.Conventions1

theorem loc_result_type : loc_result_typeStatement := by
  intro sig
  cases h : sig.sig_res <;>
    simp [loc_result, loc_result_64, loc_result_32,
      CompCert4Lean.Common.AST.proj_sig_res,
      CompCert4Lean.Common.AST.proj_xtype,
      CompCert4Lean.Common.AST.Tptr,
      CompCert4Lean.Common.AST.typ_rpair,
      CompCert4Lean.X86_64.Archi.ptr64,
      CompCert4Lean.X86.Machregs.mreg_type,
      CompCert4Lean.Common.AST.subtype, h]

theorem loc_result_caller_save : loc_result_caller_saveStatement := by
  intro cfg sig
  cases h : sig.sig_res <;>
    simp [loc_result, loc_result_64, loc_result_32,
      CompCert4Lean.Common.AST.proj_sig_res,
      CompCert4Lean.Common.AST.proj_xtype,
      CompCert4Lean.Common.AST.Tptr,
      CompCert4Lean.Common.AST.forall_rpair,
      CompCert4Lean.X86_64.Archi.ptr64,
      CompCert4Lean.X86.Machregs.mreg_type,
      is_callee_save, h]

theorem loc_result_pair : loc_result_pairStatement := by
  intro sig
  cases h : sig.sig_res <;>
    simp [loc_result, loc_result_64, loc_result_32,
      CompCert4Lean.Common.AST.proj_sig_res,
      CompCert4Lean.Common.AST.proj_xtype,
      CompCert4Lean.Common.AST.Tptr,
      CompCert4Lean.X86_64.Archi.ptr64, h]

theorem loc_result_exten : loc_result_extenStatement := by
  intro s1 s2 h
  cases s1 with
  | mk args1 res1 cc1 =>
    cases s2 with
    | mk args2 res2 cc2 =>
      cases h
      rfl

end CompCert4Lean.X86.Conventions1

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev ConvZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev convZ0 : ConvZ := .Z0
private abbrev convZAdd := ZArith.BinInt.Z.add
private abbrev convZLe := ZArith.BinInt.Z.le
private abbrev convIntOfZ := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ

private theorem conv_zle_trans (a b c : ConvZ)
    (hab : convZLe a b) (hbc : convZLe b c) : convZLe a c := by
  change convIntOfZ a ≤ convIntOfZ b at hab
  change convIntOfZ b ≤ convIntOfZ c at hbc
  change convIntOfZ a ≤ convIntOfZ c
  omega

private theorem conv_zle_refl (a : ConvZ) : convZLe a a := by
  change convIntOfZ a ≤ convIntOfZ a
  exact Int.le_refl _

private theorem conv_zle_add_one (ofs : ConvZ) :
    convZLe ofs (convZAdd ofs (ZArith.BinInt.Z.of_nat 1)) := by
  change convIntOfZ ofs ≤ convIntOfZ
    (convZAdd ofs (ZArith.BinInt.Z.of_nat 1))
  simp only [convZAdd, ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change intOfZ ofs ≤ intOfZ ofs + 1
  omega

private theorem conv_zle_add_typesize (ofs : ConvZ) (ty : typ) :
    convZLe ofs (convZAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) := by
  change convIntOfZ ofs ≤ convIntOfZ
    (convZAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))
  simp only [convZAdd, ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change intOfZ ofs ≤ intOfZ ofs + intOfZ
    (CompCert4Lean.Backend.Locations.typesize ty)
  have hpos := CompCert4Lean.Backend.Locations.typesize_pos ty
  change 0 < intOfZ (CompCert4Lean.Backend.Locations.typesize ty) at hpos
  omega

theorem loc_arguments_32_charact : loc_arguments_32_charactStatement := by
  have X : ∀ (ofs1 ofs2 : ConvZ) (l : loc),
      loc_argument_32_charact ofs2 l → convZLe ofs1 ofs2 →
        loc_argument_32_charact ofs1 l := by
    intro ofs1 ofs2 l hl hofs
    cases l with
    | R r => cases hl
    | S sl pos ty =>
        cases sl with
        | Local => cases hl
        | Incoming => cases hl
        | Outgoing =>
            exact ⟨conv_zle_trans ofs1 ofs2 pos hofs hl.1, hl.2⟩
  have Y : ∀ (ofs1 ofs2 : ConvZ) (p : rpair loc),
      forall_rpair (loc_argument_32_charact ofs2) p →
      convZLe ofs1 ofs2 → forall_rpair (loc_argument_32_charact ofs1) p := by
    intro ofs1 ofs2 p hp hofs
    cases p with
    | One l => exact X ofs1 ofs2 l hp hofs
    | Twolong l1 l2 => exact ⟨X ofs1 ofs2 l1 hp.1 hofs, X ofs1 ofs2 l2 hp.2 hofs⟩
  intro tyl
  induction tyl with
  | nil =>
      intro ofs p hp
      simp [loc_arguments_32] at hp
  | cons ty tys ih =>
      intro ofs p hp
      cases ty <;> simp [loc_arguments_32] at hp
      all_goals
        rcases hp with rfl | hp
        · simp [forall_rpair, loc_argument_32_charact,
            CompCert4Lean.Backend.Locations.typealign,
            ZArith.BinInt.Z.of_nat,
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ,
            conv_zle_refl] <;>
            try exact conv_zle_add_one ofs
        · exact Y ofs _ p (ih _ _ hp) (by
            apply conv_zle_add_typesize)

end CompCert4Lean.X86.Conventions1

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev convZ1 : ConvZ := ZArith.BinInt.Z.of_nat 1
private abbrev convZ2 : ConvZ := ZArith.BinInt.Z.of_nat 2
private abbrev convZMul := ZArith.BinInt.Z.mul
private abbrev convZDivide := ZArith.BinInt.Z.divide

private theorem conv_zdivide_zero (a : ConvZ) : convZDivide a convZ0 := by
  refine ⟨convZ0, ?_⟩
  change convZ0 = convZMul a convZ0
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change convIntOfZ convZ0 =
    convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (convIntOfZ a * convIntOfZ convZ0))
  simp only [convIntOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change (0 : Int) = intOfZ a * 0
  simp

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

private theorem conv_zle_add_two (ofs : ConvZ) (h : convZLe convZ0 ofs) :
    convZLe convZ0 (convZAdd ofs convZ2) := by
  change 0 ≤ intOfZ ofs at h
  change 0 ≤ intOfZ (convZAdd ofs convZ2)
  simp only [convZAdd, ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change 0 ≤ intOfZ ofs + 2
  omega

private theorem conv_zle_of_add_two (ofs : ConvZ) :
    convZLe ofs (convZAdd ofs convZ2) := by
  change intOfZ ofs ≤ intOfZ (convZAdd ofs convZ2)
  simp only [convZAdd, ZArith.BinInt.Z.add,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change intOfZ ofs ≤ intOfZ ofs + 2
  omega

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

private theorem conv_loc_argument_elf64_mono
    (ofs1 ofs2 : ConvZ) (l : loc)
    (hl : loc_argument_elf64_charact ofs2 l) (hle : convZLe ofs1 ofs2) :
    loc_argument_elf64_charact ofs1 l := by
  cases l with
  | R r => exact hl
  | S sl pos ty =>
      cases sl with
      | Local => cases hl
      | Incoming => cases hl
      | Outgoing =>
          exact ⟨conv_zle_trans ofs1 ofs2 pos hle hl.1, hl.2⟩

private theorem conv_forall_rpair_elf64_mono
    (ofs1 ofs2 : ConvZ) (p : rpair loc)
    (hp : forall_rpair (loc_argument_elf64_charact ofs2) p)
    (hle : convZLe ofs1 ofs2) :
    forall_rpair (loc_argument_elf64_charact ofs1) p := by
  cases p with
  | One l => exact conv_loc_argument_elf64_mono ofs1 ofs2 l hp hle
  | Twolong l1 l2 =>
      exact ⟨conv_loc_argument_elf64_mono ofs1 ofs2 l1 hp.1 hle,
        conv_loc_argument_elf64_mono ofs1 ofs2 l2 hp.2 hle⟩

theorem loc_arguments_elf64_charact : loc_arguments_elf64_charactStatement := by
  intro tyl
  induction tyl with
  | nil =>
      intro ir fr ofs p hp hdiv
      simp [loc_arguments_elf64] at hp
  | cons ty tys ih =>
      intro ir fr ofs p hp hdiv
      cases ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z int_param_regs_elf64 ir with
          | none =>
              simp [loc_arguments_elf64, hn] at hp
              rcases hp with rfl | hp
              · exact ⟨conv_zle_refl ofs, hdiv⟩
              · exact conv_forall_rpair_elf64_mono ofs
                  (convZAdd ofs convZ2) p
                  (ih _ _ _ p hp (conv_zdivide_add_two ofs hdiv))
                  (conv_zle_of_add_two ofs)
          | some ireg =>
              simp [loc_arguments_elf64, hn] at hp
              rcases hp with rfl | hp
              · simp [forall_rpair, loc_argument_elf64_charact]
                exact Or.inl (conv_list_nth_z_in _ _ _ hn)
              · exact ih _ _ _ p hp hdiv
      | Tfloat | Tsingle =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z float_param_regs_elf64 fr with
          | none =>
              simp [loc_arguments_elf64, hn] at hp
              rcases hp with rfl | hp
              · exact ⟨conv_zle_refl ofs, hdiv⟩
              · exact conv_forall_rpair_elf64_mono ofs
                  (convZAdd ofs convZ2) p
                  (ih _ _ _ p hp (conv_zdivide_add_two ofs hdiv))
                  (conv_zle_of_add_two ofs)
          | some freg =>
              simp [loc_arguments_elf64, hn] at hp
              rcases hp with rfl | hp
              · simp [forall_rpair, loc_argument_elf64_charact]
                exact Or.inr (conv_list_nth_z_in _ _ _ hn)
              · exact ih _ _ _ p hp hdiv

end CompCert4Lean.X86.Conventions1

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private theorem conv_zdivide_one (ofs : ConvZ) : convZDivide convZ1 ofs := by
  refine ⟨ofs, ?_⟩
  apply CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_injective
  change convIntOfZ ofs =
    convIntOfZ (CompCert4Lean.Foundation.Numbers.Rocq.Coq.zOfInt
      (convIntOfZ convZ1 * convIntOfZ ofs))
  simp only [convIntOfZ,
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ_zOfInt]
  change intOfZ ofs = 1 * intOfZ ofs
  simp

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

private theorem conv_loc_argument_win64_mono
    (ofs1 ofs2 : ConvZ) (l : loc)
    (hl : loc_argument_win64_charact ofs2 l) (hle : convZLe ofs1 ofs2) :
    loc_argument_win64_charact ofs1 l := by
  cases l with
  | R r => exact hl
  | S sl pos ty =>
      cases sl with
      | Local => cases hl
      | Incoming => cases hl
      | Outgoing =>
          exact ⟨conv_zle_trans ofs1 ofs2 pos hle hl.1, hl.2⟩

private theorem conv_forall_rpair_win64_mono
    (ofs1 ofs2 : ConvZ) (p : rpair loc)
    (hp : forall_rpair (loc_argument_win64_charact ofs2) p)
    (hle : convZLe ofs1 ofs2) :
    forall_rpair (loc_argument_win64_charact ofs1) p := by
  cases p with
  | One l => exact conv_loc_argument_win64_mono ofs1 ofs2 l hp hle
  | Twolong l1 l2 =>
      exact ⟨conv_loc_argument_win64_mono ofs1 ofs2 l1 hp.1 hle,
        conv_loc_argument_win64_mono ofs1 ofs2 l2 hp.2 hle⟩

private theorem conv_win64_int_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (h : r ∈ int_param_regs_win64) : is_callee_save cfg r = false := by
  simp [int_param_regs_win64] at h
  rcases h with h | h | h | h <;> subst r <;> rfl

private theorem conv_win64_float_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (h : r ∈ float_param_regs_win64) : is_callee_save cfg r = false := by
  simp [float_param_regs_win64] at h
  rcases h with h | h | h | h <;> subst r <;> rfl

private theorem conv_elf64_int_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig)
    (habi : ¬ CompCert4Lean.X86_64.Archi.win64 cfg = true)
    (r : mreg) (h : r ∈ int_param_regs_elf64) : is_callee_save cfg r = false := by
  simp [int_param_regs_elf64] at h
  rcases h with h | h | h | h | h | h <;> subst r
  all_goals
    simp [is_callee_save, CompCert4Lean.X86_64.Archi.ptr64, habi]

private theorem conv_elf64_float_caller_save
    (cfg : CompCert4Lean.Config.CompilerConfig) (r : mreg)
    (h : r ∈ float_param_regs_elf64) : is_callee_save cfg r = false := by
  simp [float_param_regs_elf64] at h
  rcases h with h | h | h | h | h | h | h | h <;> subst r <;> rfl

private theorem conv_32_charact_acceptable
    (cfg : CompCert4Lean.Config.CompilerConfig) (ofs : ConvZ) (l : loc)
    (hbase : convZLe convZ0 ofs) (h : loc_argument_32_charact ofs l) :
    loc_argument_acceptable cfg l := by
  cases l with
  | R r => cases h
  | S sl pos ty =>
      cases sl with
      | Local => cases h
      | Incoming => cases h
      | Outgoing =>
          rcases h with ⟨hle, halign⟩
          refine ⟨conv_zle_trans convZ0 ofs pos hbase hle, ?_⟩
          rw [halign]
          exact conv_zdivide_one pos

private theorem conv_elf64_charact_acceptable
    (cfg : CompCert4Lean.Config.CompilerConfig) (ofs : ConvZ) (l : loc)
    (hbase : convZLe convZ0 ofs) (h : loc_argument_elf64_charact ofs l)
    (habi : ¬ CompCert4Lean.X86_64.Archi.win64 cfg = true) :
    loc_argument_acceptable cfg l := by
  cases l with
  | R r =>
      rcases h with hi | hf
      · exact conv_elf64_int_caller_save cfg habi r hi
      · exact conv_elf64_float_caller_save cfg r hf
  | S sl pos ty =>
      cases sl with
      | Local => cases h
      | Incoming => cases h
      | Outgoing =>
          rcases h with ⟨hle, hdiv⟩
          exact ⟨conv_zle_trans convZ0 ofs pos hbase hle,
            conv_typealign_divide ty pos hdiv⟩

private theorem conv_win64_charact_acceptable
    (cfg : CompCert4Lean.Config.CompilerConfig) (ofs : ConvZ) (l : loc)
    (hbase : convZLe convZ0 ofs) (h : loc_argument_win64_charact ofs l) :
    loc_argument_acceptable cfg l := by
  cases l with
  | R r =>
      rcases h with hi | hf
      · exact conv_win64_int_caller_save cfg r hi
      · exact conv_win64_float_caller_save cfg r hf
  | S sl pos ty =>
      cases sl with
      | Local => cases h
      | Incoming => cases h
      | Outgoing =>
          rcases h with ⟨hle, hdiv⟩
          exact ⟨conv_zle_trans convZ0 ofs pos hbase hle,
            conv_typealign_divide ty pos hdiv⟩

theorem loc_arguments_win64_charact : loc_arguments_win64_charactStatement := by
  intro tyl
  induction tyl with
  | nil =>
      intro r ofs p hp hdiv
      simp [loc_arguments_win64] at hp
  | cons ty tys ih =>
      intro r ofs p hp hdiv
      cases ty with
      | Tint | Tlong | Tany32 | Tany64 =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z int_param_regs_win64 r with
          | none =>
              simp [loc_arguments_win64, hn] at hp
              rcases hp with rfl | hp
              · exact ⟨conv_zle_refl ofs, hdiv⟩
              · exact conv_forall_rpair_win64_mono ofs
                  (convZAdd ofs convZ2) p
                  (ih _ _ p hp (conv_zdivide_add_two ofs hdiv))
                  (conv_zle_of_add_two ofs)
          | some ireg =>
              simp [loc_arguments_win64, hn] at hp
              rcases hp with rfl | hp
              · simp [forall_rpair, loc_argument_win64_charact]
                exact Or.inl (conv_list_nth_z_in _ _ _ hn)
              · exact ih _ _ p hp hdiv
      | Tfloat | Tsingle =>
          cases hn : CompCert4Lean.Lib.Coqlib.list_nth_z float_param_regs_win64 r with
          | none =>
              simp [loc_arguments_win64, hn] at hp
              rcases hp with rfl | hp
              · exact ⟨conv_zle_refl ofs, hdiv⟩
              · exact conv_forall_rpair_win64_mono ofs
                  (convZAdd ofs convZ2) p
                  (ih _ _ p hp (conv_zdivide_add_two ofs hdiv))
                  (conv_zle_of_add_two ofs)
          | some freg =>
              simp [loc_arguments_win64, hn] at hp
              rcases hp with rfl | hp
              · simp [forall_rpair, loc_argument_win64_charact]
                exact Or.inr (conv_list_nth_z_in _ _ _ hn)
              · exact ih _ _ p hp hdiv

end CompCert4Lean.X86.Conventions1

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

theorem loc_arguments_acceptable : loc_arguments_acceptableStatement := by
  intro cfg s p hp
  simp only [loc_arguments, CompCert4Lean.X86_64.Archi.ptr64, ↓reduceIte] at hp
  split at hp <;> rename_i habi
  · have hc := loc_arguments_win64_charact (proj_sig_args s) convZ0 convZ0 p hp
      (conv_zdivide_zero convZ2)
    cases p with
    | One l =>
        exact conv_win64_charact_acceptable cfg convZ0 l
          (conv_zle_refl convZ0) hc
    | Twolong l1 l2 =>
        exact ⟨conv_win64_charact_acceptable cfg convZ0 l1
            (conv_zle_refl convZ0) hc.1,
          conv_win64_charact_acceptable cfg convZ0 l2
            (conv_zle_refl convZ0) hc.2⟩
  · have habi' : ¬ CompCert4Lean.X86_64.Archi.win64 cfg = true := by
      exact habi
    have hc := loc_arguments_elf64_charact (proj_sig_args s) convZ0 convZ0 convZ0 p hp
      (conv_zdivide_zero convZ2)
    cases p with
    | One l =>
        exact conv_elf64_charact_acceptable cfg convZ0 l
          (conv_zle_refl convZ0) hc habi'
    | Twolong l1 l2 =>
        exact ⟨conv_elf64_charact_acceptable cfg convZ0 l1
            (conv_zle_refl convZ0) hc.1 habi',
          conv_elf64_charact_acceptable cfg convZ0 l2
            (conv_zle_refl convZ0) hc.2 habi'⟩
end CompCert4Lean.X86.Conventions1

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

theorem loc_arguments_main : loc_arguments_mainStatement := by
  intro cfg
  unfold loc_arguments
  cases hwin : CompCert4Lean.X86_64.Archi.win64 cfg <;>
    simp [hwin, loc_arguments_win64, loc_arguments_elf64,
      loc_arguments_32, CompCert4Lean.Common.AST.proj_sig_args,
      CompCert4Lean.Common.AST.signature_main,
      CompCert4Lean.X86_64.Archi.ptr64]

end CompCert4Lean.X86.Conventions1
