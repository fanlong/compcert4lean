import CompCert4Lean.Config
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Backend.Bounds
import CompCert4Lean.Common.Memdata
import CompCert4Lean.Common.Separation
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.X86_64.Archi

/-! Definition translation of `x86/Stacklayout.v`. -/

namespace CompCert4Lean.X86.Stacklayout

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Common.Separation
open CompCert4Lean.Lib.Coqlib

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.mem

private abbrev z0 : Z := .Z0
private abbrev z4 : Z := ZArith.BinInt.Z.of_nat 4
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev z32 : Z := ZArith.BinInt.Z.of_nat 32
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMul := ZArith.BinInt.Z.mul
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zDivide := ZArith.BinInt.Z.divide

/-! ## Activation-record layout definitions -/

def fe_ofs_arg (cfg : CompilerConfig) : Z :=
  if CompCert4Lean.X86_64.Archi.win64 cfg then z32 else z0

def make_env (cfg : CompilerConfig) (b : bounds cfg) : frame_env :=
  let w := if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4
  let olink := align (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing)) w
  let ocs := zAdd olink w
  let ol := align (size_callee_save_area cfg b ocs) z8
  let ostkdata := align (zAdd ol (zMul z4 b.bound_local)) z8
  let oretaddr := align (zAdd ostkdata b.bound_stack_data) w
  let sz := zAdd oretaddr w
  { fe_size := sz
    fe_ofs_link := olink
    fe_ofs_retaddr := oretaddr
    fe_ofs_local := ol
    fe_ofs_callee_save := ocs
    fe_stack_data := ostkdata
    fe_used_callee_save := b.used_callee_save }

/-! ## Statement descriptors for later proof migration -/

def frame_env_separatedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg)
    (_bound_local_pos : bound_local_pos cfg b)
    (_bound_outgoing_pos : bound_outgoing_pos cfg b)
    (_bound_stack_data_pos : bound_stack_data_pos cfg b)
    (_used_callee_save_norepet : used_callee_save_norepet cfg b)
    (_used_callee_save_prop : used_callee_save_prop cfg b)
    (sp : block) (m : mem) (P : massert),
    let fe := make_env cfg b
    (sepconj
      (range sp z0 (fe_stack_data fe))
      (sepconj
        (range sp (zAdd (fe_stack_data fe) b.bound_stack_data) (fe_size fe))
        P)).m_pred m →
    (sepconj
      (range sp (fe_ofs_local fe)
        (zAdd (fe_ofs_local fe) (zMul z4 b.bound_local)))
      (sepconj
        (range sp (fe_ofs_arg cfg)
          (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing)))
        (sepconj
          (range sp (fe_ofs_link fe)
            (zAdd (fe_ofs_link fe) (size_chunk Mptr)))
          (sepconj
            (range sp (fe_ofs_retaddr fe)
              (zAdd (fe_ofs_retaddr fe) (size_chunk Mptr)))
            (sepconj
              (range sp (fe_ofs_callee_save fe)
                (size_callee_save_area cfg b (fe_ofs_callee_save fe)))
              P))))).m_pred m

def frame_env_rangeStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg)
    (_bound_local_pos : bound_local_pos cfg b)
    (_bound_outgoing_pos : bound_outgoing_pos cfg b)
    (_bound_stack_data_pos : bound_stack_data_pos cfg b)
    (_used_callee_save_norepet : used_callee_save_norepet cfg b)
    (_used_callee_save_prop : used_callee_save_prop cfg b),
    let fe := make_env cfg b
    zLe z0 (fe_stack_data fe) ∧
      zLe (zAdd (fe_stack_data fe) b.bound_stack_data) (fe_size fe)

def frame_env_alignedStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg)
    (_bound_local_pos : bound_local_pos cfg b)
    (_bound_outgoing_pos : bound_outgoing_pos cfg b)
    (_bound_stack_data_pos : bound_stack_data_pos cfg b)
    (_used_callee_save_norepet : used_callee_save_norepet cfg b)
    (_used_callee_save_prop : used_callee_save_prop cfg b),
    let fe := make_env cfg b
    zDivide z8 (fe_ofs_arg cfg) ∧
      zDivide z8 (fe_ofs_local fe) ∧
      zDivide z8 (fe_stack_data fe) ∧
      zDivide (align_chunk Mptr) (fe_ofs_link fe) ∧
      zDivide (align_chunk Mptr) (fe_ofs_retaddr fe)

end CompCert4Lean.X86.Stacklayout

namespace CompCert4Lean.X86.Stacklayout

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Common.AST
open CompCert4Lean.X86.Machregs
open CompCert4Lean.Lib.Coqlib

private abbrev z1 : Z := .Zpos .xH
private abbrev zGt := ZArith.BinInt.Z.gt

private def sl_intDivEucl (a b : Int) : Int :=
  if b = 0 then 0
  else if 0 < b then Int.ediv a b
  else
    let d := -b
    let q := Int.ediv a d
    let r := Int.emod a d
    if r = 0 then -q else -(q + 1)

private theorem sl_zDiv_from_int (x y : Z) :
    ZArith.BinInt.Z.div x y = zOfInt (sl_intDivEucl (intOfZ x) (intOfZ y)) := by
  cases x <;> cases y <;> rfl

private theorem sl_align_le (x y : Z) (hy : zGt y z0) :
    zLe x (align x y) := by
  change intOfZ x ≤ intOfZ (ZArith.BinInt.Z.mul
    (ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add x y) z1) y) y)
  rw [sl_zDiv_from_int]
  simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have hyInt : 0 < intOfZ y := hy
  have hy0 : intOfZ y ≠ 0 := Int.ne_of_gt hyInt
  simp only [sl_intDivEucl, hy0, if_false, if_pos hyInt]
  have hu := (Int.ediv_emod_unique hyInt).mp
    (show Int.ediv (intOfZ x + intOfZ y - 1) (intOfZ y) =
        Int.ediv (intOfZ x + intOfZ y - 1) (intOfZ y) ∧
      (intOfZ x + intOfZ y - 1) % intOfZ y =
        (intOfZ x + intOfZ y - 1) % intOfZ y from ⟨rfl, rfl⟩)
  have hz1 : intOfZ z1 = 1 := by rfl
  have hbound : intOfZ x ≤ intOfZ y *
      ((intOfZ x + intOfZ y - 1).ediv (intOfZ y)) := by
    omega
  simpa [Int.mul_comm, hz1] using hbound

private theorem sl_typesize_pos (ty : typ) : zGt (typesize ty) z0 := by
  cases ty <;>
    simp only [typesize, zGt, ZArith.BinInt.Z.lt, intOfZ,
      ZArith.BinInt.Z.of_nat, zOfInt]
  all_goals exact Int.natCast_pos.mpr (posToNat_positive _)

private theorem sl_zle_trans {x y z : Z} :
    zLe x y → zLe y z → zLe x z := by
  intro hxy hyz
  change intOfZ x ≤ intOfZ y at hxy
  change intOfZ y ≤ intOfZ z at hyz
  change intOfZ x ≤ intOfZ z
  exact Int.le_trans hxy hyz

private theorem sl_zle_refl (x : Z) : zLe x x := by
  change intOfZ x ≤ intOfZ x
  exact Int.le_refl _

private theorem sl_zofnat_nonneg (n : Nat) : zLe z0 (ZArith.BinInt.Z.of_nat n) := by
  change 0 ≤ intOfZ (ZArith.BinInt.Z.of_nat n)
  cases n with
  | zero => exact Int.le_refl _
  | succ n =>
      simp only [ZArith.BinInt.Z.of_nat, zOfInt, intOfZ]
      exact Int.le_of_lt (Int.natCast_pos.mpr (posToNat_positive _))

private theorem sl_zofnat_pos (n : Nat) (hn : 0 < n) :
    zGt (ZArith.BinInt.Z.of_nat n) z0 := by
  change 0 < intOfZ (ZArith.BinInt.Z.of_nat n)
  cases n with
  | zero => omega
  | succ n =>
      simp only [ZArith.BinInt.Z.of_nat, zOfInt, intOfZ]
      exact Int.natCast_pos.mpr (posToNat_positive _)

private theorem sl_size_callee_save_area_incr (l : List mreg) (ofs : Z) :
    zLe ofs (size_callee_save_area_rec l ofs) := by
  induction l generalizing ofs with
  | nil => exact sl_zle_refl ofs
  | cons r l ih =>
      simp only [size_callee_save_area_rec]
      have hty := sl_typesize_pos (mreg_type r)
      have hstep := sl_align_le ofs (typesize (mreg_type r)) hty
      have hty0 : zLe z0 (typesize (mreg_type r)) := by
        change intOfZ z0 ≤ intOfZ (typesize (mreg_type r))
        exact Int.le_of_lt (show intOfZ z0 < intOfZ (typesize (mreg_type r)) from hty)
      have hadd : zLe (align ofs (typesize (mreg_type r)))
          (zAdd (align ofs (typesize (mreg_type r))) (typesize (mreg_type r))) := by
        change intOfZ (align ofs (typesize (mreg_type r))) ≤
          intOfZ (zAdd (align ofs (typesize (mreg_type r))) (typesize (mreg_type r)))
        simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
        exact Int.le_add_of_nonneg_right
          (show 0 ≤ intOfZ (typesize (mreg_type r)) from hty0)
      exact sl_zle_trans hstep (sl_zle_trans hadd (ih _))

theorem frame_env_range : frame_env_rangeStatement := by
  intro cfg b _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
    _used_callee_save_norepet _used_callee_save_prop
  let w : Z := if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4
  let olink : Z := align
    (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing)) w
  let ocs : Z := zAdd olink w
  let ol : Z := align (size_callee_save_area cfg b ocs) z8
  let ostkdata : Z := align (zAdd ol (zMul z4 b.bound_local)) z8
  let oretaddr : Z := align (zAdd ostkdata b.bound_stack_data) w
  let fe : frame_env :=
    { fe_size := zAdd oretaddr w
      fe_ofs_link := olink
      fe_ofs_retaddr := oretaddr
      fe_ofs_local := ol
      fe_ofs_callee_save := ocs
      fe_stack_data := ostkdata
      fe_used_callee_save := b.used_callee_save }
  dsimp [make_env]
  change zLe z0 ostkdata ∧ zLe (zAdd ostkdata b.bound_stack_data)
    (zAdd oretaddr w)
  have hw : zGt w z0 := by
    dsimp [w]
    exact sl_zofnat_pos 8 (by omega)
  have harg : zLe z0 (fe_ofs_arg cfg) := by
    unfold fe_ofs_arg
    cases h : CompCert4Lean.X86_64.Archi.win64 cfg
    · exact sl_zle_refl z0
    · simpa [h] using sl_zofnat_nonneg 32
  have hout : zLe z0 (zMul z4 b.bound_outgoing) := by
    change 0 ≤ intOfZ (zMul z4 b.bound_outgoing)
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    have hb : 0 ≤ intOfZ b.bound_outgoing := _bound_outgoing_pos
    exact Int.mul_nonneg (sl_zofnat_nonneg 4) hb
  have hlocal : zLe z0 (zMul z4 b.bound_local) := by
    change 0 ≤ intOfZ (zMul z4 b.bound_local)
    simp only [zMul, ZArith.BinInt.Z.mul, intOfZ_zOfInt]
    have hb : 0 ≤ intOfZ b.bound_local := _bound_local_pos
    exact Int.mul_nonneg (sl_zofnat_nonneg 4) hb
  have holink0 : zLe z0 olink := by
    apply sl_zle_trans ?_ (sl_align_le _ _ hw)
    change zLe z0 (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing))
    change intOfZ z0 ≤ intOfZ (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing))
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    have ha : 0 ≤ intOfZ (fe_ofs_arg cfg) := harg
    have ho : 0 ≤ intOfZ (zMul z4 b.bound_outgoing) := hout
    exact Int.add_nonneg ha ho
  have hocs0 : zLe z0 ocs := by
    change zLe z0 (zAdd olink w)
    change intOfZ z0 ≤ intOfZ (zAdd olink w)
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    have ho : 0 ≤ intOfZ olink := holink0
    have hw0 : 0 ≤ intOfZ w := Int.le_of_lt (show intOfZ z0 < intOfZ w from hw)
    exact Int.add_nonneg ho hw0
  have harea : zLe ocs (size_callee_save_area cfg b ocs) :=
    sl_size_callee_save_area_incr b.used_callee_save ocs
  have hocsl : zLe ocs ol :=
    sl_zle_trans harea (sl_align_le _ _ (sl_zofnat_pos 8 (by omega)))
  have hol0 : zLe z0 ol := sl_zle_trans hocs0 hocsl
  have hostk0 : zLe z0 ostkdata := by
    apply sl_zle_trans ?_ (sl_align_le _ _ (sl_zofnat_pos 8 (by omega)))
    change zLe z0 (zAdd ol (zMul z4 b.bound_local))
    change intOfZ z0 ≤ intOfZ (zAdd ol (zMul z4 b.bound_local))
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    have ho : 0 ≤ intOfZ ol := hol0
    have hl : 0 ≤ intOfZ (zMul z4 b.bound_local) := hlocal
    exact Int.add_nonneg ho hl
  have hret : zLe (zAdd ostkdata b.bound_stack_data) oretaddr :=
    sl_align_le _ _ hw
  have hstack : zLe z0 b.bound_stack_data := _bound_stack_data_pos
  have hright : zLe (zAdd ostkdata b.bound_stack_data) (zAdd oretaddr w) := by
    apply sl_zle_trans hret
    change zLe oretaddr (zAdd oretaddr w)
    change intOfZ oretaddr ≤ intOfZ (zAdd oretaddr w)
    simp only [zAdd, ZArith.BinInt.Z.add, intOfZ_zOfInt]
    have hw0 : 0 ≤ intOfZ w := Int.le_of_lt (show intOfZ z0 < intOfZ w from hw)
    omega
  exact ⟨hostk0, hright⟩

end CompCert4Lean.X86.Stacklayout

namespace CompCert4Lean.X86.Stacklayout

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Memdata
open CompCert4Lean.Lib.Coqlib

private theorem sl_align_divides (x y : Z) :
    zDivide y (align x y) := by
  unfold zDivide align ZArith.BinInt.Z.divide
  refine ⟨ZArith.BinInt.Z.div
    (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add x y) (Zpos xH)) y, ?_⟩
  simp only [ZArith.BinInt.Z.mul]
  exact congrArg zOfInt (Int.mul_comm _ _)

theorem frame_env_aligned : frame_env_alignedStatement := by
  intro cfg b _bound_local_pos _bound_outgoing_pos _bound_stack_data_pos
    _used_callee_save_norepet _used_callee_save_prop
  let fe := make_env cfg b
  have harg : zDivide z8 (fe_ofs_arg cfg) := by
    unfold fe_ofs_arg
    cases h : CompCert4Lean.X86_64.Archi.win64 cfg <;>
      refine ⟨?_, ?_⟩
    · exact z0
    · apply intOfZ_injective
      change (0 : Int) = intOfZ
        (ZArith.BinInt.Z.mul z8 z0)
      simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      rfl
    · exact ZArith.BinInt.Z.of_nat 4
    · apply intOfZ_injective
      change intOfZ z32 = intOfZ
        (ZArith.BinInt.Z.mul z8 (ZArith.BinInt.Z.of_nat 4))
      simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
      rfl
  dsimp [fe, make_env]
  refine ⟨harg, ?_, ?_, ?_, ?_⟩
  · change zDivide z8 (align
      (size_callee_save_area cfg b
        (zAdd
          (align (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing))
            (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))
          (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))) z8)
    exact sl_align_divides
      (size_callee_save_area cfg b
        (zAdd
          (align (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing))
            (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))
          (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))) z8
  · change zDivide z8 (align
      (zAdd
        (align (size_callee_save_area cfg b
          (zAdd
            (align (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing))
              (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))
            (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))) z8)
        (zMul z4 b.bound_local)) z8)
    exact sl_align_divides
      (zAdd
        (align (size_callee_save_area cfg b
          (zAdd
            (align (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing))
              (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))
            (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4))) z8)
        (zMul z4 b.bound_local)) z8
  · change zDivide (align_chunk Mptr) (fe_ofs_link fe)
    rw [show align_chunk Mptr = z8 by rfl]
    exact sl_align_divides
      (zAdd (fe_ofs_arg cfg) (zMul z4 b.bound_outgoing)) z8
  · change zDivide (align_chunk Mptr) (fe_ofs_retaddr fe)
    rw [show align_chunk Mptr = z8 by rfl]
    exact sl_align_divides
      (zAdd (fe_stack_data fe) b.bound_stack_data)
      (if CompCert4Lean.X86_64.Archi.ptr64 then z8 else z4)

end CompCert4Lean.X86.Stacklayout
