import CompCert4Lean.Config
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.ValueDomain
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Globalenvs
import CompCert4Lean.Common.Memory
import CompCert4Lean.Common.Values
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.X86.Op
import CompCert4Lean.X86_64.Archi

/-!
# Static x86 operator evaluation

Definition-bearing translation of CompCert's `x86/ValueAOp.v`.  The
soundness declarations are represented by exact proposition descriptors for
the later proof-migration phase.
-/

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev block := CompCert4Lean.Common.Values.block

private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

private abbrev zOfNat := ZArith.BinInt.Z.of_nat

def eval_static_condition (cfg : CompilerConfig) (cond : condition)
    (vl : List aval) : abool :=
  match cond, vl with
  | .Ccomp c, [v1, v2] => cmp_bool c v1 v2
  | .Ccompu c, [v1, v2] => cmpu_bool cfg c v1 v2
  | .Ccompimm c n, [v1] => cmp_bool c v1 (I n)
  | .Ccompuimm c n, [v1] => cmpu_bool cfg c v1 (I n)
  | .Ccompl c, [v1, v2] => cmpl_bool c v1 v2
  | .Ccomplu c, [v1, v2] => cmplu_bool cfg c v1 v2
  | .Ccomplimm c n, [v1] => cmpl_bool c v1 (L n)
  | .Ccompluimm c n, [v1] => cmplu_bool cfg c v1 (L n)
  | .Ccompf c, [v1, v2] => cmpf_bool c v1 v2
  | .Cnotcompf c, [v1, v2] => cnot (cmpf_bool c v1 v2)
  | .Ccompfs c, [v1, v2] => cmpfs_bool c v1 v2
  | .Cnotcompfs c, [v1, v2] => cnot (cmpfs_bool c v1 v2)
  | .Cmaskzero n, [v1] => maskzero v1 n
  | .Cmasknotzero n, [v1] => cnot (maskzero v1 n)
  | _, _ => Bnone

def eval_static_addressing_32 (addr : addressing) (vl : List aval) : aval :=
  match addr, vl with
  | .Aindexed n, [v1] => add v1 (I (CompCert4Lean.Lib.Integers.Int.repr n))
  | .Aindexed2 n, [v1, v2] =>
      add (add v1 v2) (I (CompCert4Lean.Lib.Integers.Int.repr n))
  | .Ascaled sc ofs, [v1] =>
      add (mul v1 (I (CompCert4Lean.Lib.Integers.Int.repr sc)))
        (I (CompCert4Lean.Lib.Integers.Int.repr ofs))
  | .Aindexed2scaled sc ofs, [v1, v2] =>
      add v1 (add (mul v2 (I (CompCert4Lean.Lib.Integers.Int.repr sc)))
        (I (CompCert4Lean.Lib.Integers.Int.repr ofs)))
  | .Aglobal s ofs, [] => Ptr (Gl s ofs)
  | .Abased s ofs, [v1] => add (Ptr (Gl s ofs)) v1
  | .Abasedscaled sc s ofs, [v1] =>
      add (Ptr (Gl s ofs))
        (mul v1 (I (CompCert4Lean.Lib.Integers.Int.repr sc)))
  | .Ainstack ofs, [] => Ptr (Stk ofs)
  | _, _ => Vbot

def eval_static_addressing_64 (addr : addressing) (vl : List aval) : aval :=
  match addr, vl with
  | .Aindexed n, [v1] =>
      addl v1 (L (CompCert4Lean.Lib.Integers.Int64.repr n))
  | .Aindexed2 n, [v1, v2] =>
      addl (addl v1 v2) (L (CompCert4Lean.Lib.Integers.Int64.repr n))
  | .Ascaled sc ofs, [v1] =>
      addl (mull v1 (L (CompCert4Lean.Lib.Integers.Int64.repr sc)))
        (L (CompCert4Lean.Lib.Integers.Int64.repr ofs))
  | .Aindexed2scaled sc ofs, [v1, v2] =>
      addl v1 (addl
        (mull v2 (L (CompCert4Lean.Lib.Integers.Int64.repr sc)))
        (L (CompCert4Lean.Lib.Integers.Int64.repr ofs)))
  | .Aglobal s ofs, [] => Ptr (Gl s ofs)
  | .Abased s ofs, [v1] => addl (Ptr (Gl s ofs)) v1
  | .Abasedscaled sc s ofs, [v1] =>
      addl (Ptr (Gl s ofs))
        (mull v1 (L (CompCert4Lean.Lib.Integers.Int64.repr sc)))
  | .Ainstack ofs, [] => Ptr (Stk ofs)
  | _, _ => Vbot

def eval_static_addressing (addr : addressing) (vl : List aval) : aval :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    eval_static_addressing_64 addr vl
  else
    eval_static_addressing_32 addr vl

def eval_static_operation
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (cfg : CompilerConfig) (op : operation)
    (vl : List aval) : aval :=
  match op, vl with
  | .Omove, [v1] => v1
  | .Ointconst n, [] => I n
  | .Olongconst n, [] => L n
  | .Ofloatconst n, [] =>
      if CompCert4Lean.Driver.Compopts.propagate_float_constants cfg then F n else ntop
  | .Osingleconst n, [] =>
      if CompCert4Lean.Driver.Compopts.propagate_float_constants cfg then FS n else ntop
  | .Oindirectsymbol id, [] => Ifptr (Gl id Ptrofs.zero)
  | .Ocast8signed, [v1] => sign_ext (zOfNat 8) v1
  | .Ocast8unsigned, [v1] => zero_ext (zOfNat 8) v1
  | .Ocast16signed, [v1] => sign_ext (zOfNat 16) v1
  | .Ocast16unsigned, [v1] => zero_ext (zOfNat 16) v1
  | .Oneg, [v1] => neg v1
  | .Osub, [v1, v2] => sub v1 v2
  | .Omul, [v1, v2] => mul v1 v2
  | .Omulimm n, [v1] => mul v1 (I n)
  | .Omulhs, [v1, v2] => mulhs v1 v2
  | .Omulhu, [v1, v2] => mulhu v1 v2
  | .Odiv, [v1, v2] => divs cfg v1 v2
  | .Odivu, [v1, v2] => divu cfg v1 v2
  | .Omod, [v1, v2] => mods cfg v1 v2
  | .Omodu, [v1, v2] => modu cfg v1 v2
  | .Oand, [v1, v2] => CompCert4Lean.Backend.ValueDomain.«and» v1 v2
  | .Oandimm n, [v1] => CompCert4Lean.Backend.ValueDomain.«and» v1 (I n)
  | .Oor, [v1, v2] => CompCert4Lean.Backend.ValueDomain.«or» v1 v2
  | .Oorimm n, [v1] => CompCert4Lean.Backend.ValueDomain.«or» v1 (I n)
  | .Oxor, [v1, v2] => xor v1 v2
  | .Oxorimm n, [v1] => xor v1 (I n)
  | .Onot, [v1] => notint v1
  | .Oshl, [v1, v2] => shl v1 v2
  | .Oshlimm n, [v1] => shl v1 (I n)
  | .Oshr, [v1, v2] => shr v1 v2
  | .Oshrimm n, [v1] => shr v1 (I n)
  | .Oshrximm n, [v1] => shrx v1 (I n)
  | .Oshru, [v1, v2] => shru v1 v2
  | .Oshruimm n, [v1] => shru v1 (I n)
  | .Ororimm n, [v1] => ror v1 (I n)
  | .Oshldimm n, [v1, v2] =>
      CompCert4Lean.Backend.ValueDomain.«or» (shl v1 (I n))
        (shru v2 (I (CompCert4Lean.Lib.Integers.Int.sub
          CompCert4Lean.Lib.Integers.Int.iwordsize n)))
  | .Olea addr, _ => eval_static_addressing_32 addr vl
  | .Omakelong, [v1, v2] => longofwords v1 v2
  | .Olowlong, [v1] => loword v1
  | .Ohighlong, [v1] => hiword v1
  | .Ocast32signed, [v1] => longofint v1
  | .Ocast32unsigned, [v1] => longofintu v1
  | .Onegl, [v1] => negl v1
  | .Oaddlimm n, [v1] => addl v1 (L n)
  | .Osubl, [v1, v2] => subl v1 v2
  | .Omull, [v1, v2] => mull v1 v2
  | .Omullimm n, [v1] => mull v1 (L n)
  | .Omullhs, [v1, v2] => mullhs v1 v2
  | .Omullhu, [v1, v2] => mullhu v1 v2
  | .Odivl, [v1, v2] => divls cfg v1 v2
  | .Odivlu, [v1, v2] => divlu cfg v1 v2
  | .Omodl, [v1, v2] => modls cfg v1 v2
  | .Omodlu, [v1, v2] => modlu cfg v1 v2
  | .Oandl, [v1, v2] => andl v1 v2
  | .Oandlimm n, [v1] => andl v1 (L n)
  | .Oorl, [v1, v2] => orl v1 v2
  | .Oorlimm n, [v1] => orl v1 (L n)
  | .Oxorl, [v1, v2] => xorl v1 v2
  | .Oxorlimm n, [v1] => xorl v1 (L n)
  | .Onotl, [v1] => notl v1
  | .Oshll, [v1, v2] => shll v1 v2
  | .Oshllimm n, [v1] => shll v1 (I n)
  | .Oshrl, [v1, v2] => shrl v1 v2
  | .Oshrlimm n, [v1] => shrl v1 (I n)
  | .Oshrxlimm n, [v1] => shrxl v1 (I n)
  | .Oshrlu, [v1, v2] => shrlu v1 v2
  | .Oshrluimm n, [v1] => shrlu v1 (I n)
  | .Ororlimm n, [v1] => rorl v1 (I n)
  | .Oleal addr, _ => eval_static_addressing_64 addr vl
  | .Onegf, [v1] => negf v1
  | .Oabsf, [v1] => absf v1
  | .Oaddf, [v1, v2] => addf v1 v2
  | .Osubf, [v1, v2] => subf v1 v2
  | .Omulf, [v1, v2] => mulf v1 v2
  | .Odivf, [v1, v2] => divf v1 v2
  | .Omaxf, [v1, v2] => binop_float float_max v1 v2
  | .Ominf, [v1, v2] => binop_float float_min v1 v2
  | .Onegfs, [v1] => negfs v1
  | .Oabsfs, [v1] => absfs v1
  | .Oaddfs, [v1, v2] => addfs v1 v2
  | .Osubfs, [v1, v2] => subfs v1 v2
  | .Omulfs, [v1, v2] => mulfs v1 v2
  | .Odivfs, [v1, v2] => divfs v1 v2
  | .Osingleoffloat, [v1] => singleoffloat v1
  | .Ofloatofsingle, [v1] => floatofsingle v1
  | .Ointoffloat, [v1] => intoffloat cfg v1
  | .Ofloatofint, [v1] =>
      floatofint (binary64_certificate := binary64_certificate) v1
  | .Ointofsingle, [v1] => intofsingle cfg v1
  | .Osingleofint, [v1] =>
      singleofint (binary32_certificate := binary32_certificate) v1
  | .Olongoffloat, [v1] => longoffloat cfg v1
  | .Ofloatoflong, [v1] =>
      floatoflong (binary64_certificate := binary64_certificate) v1
  | .Olongofsingle, [v1] => longofsingle cfg v1
  | .Osingleoflong, [v1] =>
      singleoflong (binary32_certificate := binary32_certificate) v1
  | .Ocmp c, _ => of_optbool (eval_static_condition cfg c vl)
  | .Osel c ty, v1 :: v2 :: rest =>
      select cfg (eval_static_condition cfg c rest) v1 v2 ty
  | _, _ => Vbot

def eval_static_condition_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification)
    (cond : condition) (vargs : List val) (m : mem) (aargs : List aval),
    list_forall2 (vmatch bc) vargs aargs →
    cmatch (eval_condition cond vargs m)
      (eval_static_condition cfg cond aargs)

def symbol_address_soundStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (id : ident) (ofs : ptrofs),
    vmatch bc (Genv.symbol_address ge id ofs) (Ptr (Gl id ofs))

def symbol_address_sound_2Statement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (id : ident) (ofs : ptrofs),
    vmatch bc (Genv.symbol_address ge id ofs) (Ifptr (Gl id ofs))

def eval_static_addressing_32_soundStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (sp : block), bc sp = BCstack →
    ∀ (addr : addressing) (vargs : List val) (vres : val)
      (aargs : List aval),
      eval_addressing32 ge (Vptr sp Ptrofs.zero) addr vargs = some vres →
      list_forall2 (vmatch bc) vargs aargs →
      vmatch bc vres (eval_static_addressing_32 addr aargs)

def eval_static_addressing_64_soundStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (sp : block), bc sp = BCstack →
    ∀ (addr : addressing) (vargs : List val) (vres : val)
      (aargs : List aval),
      eval_addressing64 ge (Vptr sp Ptrofs.zero) addr vargs = some vres →
      list_forall2 (vmatch bc) vargs aargs →
      vmatch bc vres (eval_static_addressing_64 addr aargs)

def eval_static_addressing_soundStatement : Prop :=
  ∀ (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (sp : block), bc sp = BCstack →
    ∀ (addr : addressing) (vargs : List val) (vres : val)
      (aargs : List aval),
      eval_addressing ge (Vptr sp Ptrofs.zero) addr vargs = some vres →
      list_forall2 (vmatch bc) vargs aargs →
      vmatch bc vres (eval_static_addressing addr aargs)

def eval_static_operation_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (sp : block), bc sp = BCstack →
    ∀ (op : operation) (vargs : List val) (m : mem) (vres : val)
      (aargs : List aval),
      eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (Vptr sp Ptrofs.zero) op vargs m = some vres →
      list_forall2 (vmatch bc) vargs aargs →
      vmatch bc vres
        (eval_static_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg op aargs)

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

theorem symbol_address_sound : symbol_address_soundStatement := by
  intro bc ge hge id ofs
  unfold CompCert4Lean.Common.Globalenvs.Genv.symbol_address
  cases hfind : CompCert4Lean.Common.Globalenvs.Genv.find_symbol ge id with
  | none =>
      exact CompCert4Lean.Backend.ValueDomain.vmatch.ptrUndef
        (CompCert4Lean.Backend.ValueDomain.Gl id ofs)
  | some b =>
      apply CompCert4Lean.Backend.ValueDomain.vmatch.ptr
      exact CompCert4Lean.Backend.ValueDomain.pmatch.gl id
        ((hge.1 id b).mp hfind)

theorem symbol_address_sound_2 : symbol_address_sound_2Statement := by
  intro bc ge hge id ofs
  unfold CompCert4Lean.Common.Globalenvs.Genv.symbol_address
  cases hfind : CompCert4Lean.Common.Globalenvs.Genv.find_symbol ge id with
  | none =>
      exact CompCert4Lean.Backend.ValueDomain.vmatch.ifptrUndef
        (CompCert4Lean.Backend.ValueDomain.Gl id ofs)
  | some b =>
      apply CompCert4Lean.Backend.ValueDomain.vmatch.ifptrPtr
      exact CompCert4Lean.Backend.ValueDomain.pmatch.gl id
        ((hge.1 id b).mp hfind)

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.X86.Op
open Lean Elab Tactic Meta

private theorem addr32_testbit_nat (i : int) (n : Nat) :
    CompCert4Lean.Lib.Integers.Int.testbit i (ZArith.BinInt.Z.of_nat n) = i.val.testBit n := by
  run_tac
    let nm := (← getEnv).constants.toList.find? fun (n, _) =>
      n.toString.endsWith ".CompCert4Lean.Lib.Integers.Int.suffix_testbit_nat"
    let some (nm, _) := nm | throwError "Missing checked bit-index lemma"
    let g ← getMainGoal
    let e ← mkAppM nm #[← pure (mkFVar ((← getLCtx).findFromUserName? `i).get!.fvarId), ← pure (mkFVar ((← getLCtx).findFromUserName? `n).get!.fvarId)]
    g.assign e
    replaceMainGoal []

private theorem addr32_add_val (i j : int) :
    (CompCert4Lean.Lib.Integers.Int.add i j).val = (i.val + j.val) % 2^32 := by
  run_tac
    let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
      n.toString.endsWith ".CompCert4Lean.Lib.Integers.WordCore.add_val")
      | throwError "Missing checked addition lemma"
    let e ← mkAppM nm #[← pure (mkFVar ((← getLCtx).findFromUserName? `i).get!.fvarId), ← pure (mkFVar ((← getLCtx).findFromUserName? `j).get!.fvarId)]
    (← getMainGoal).assign e
    replaceMainGoal []

private theorem addr32_mul_val (i j : int) :
    (CompCert4Lean.Lib.Integers.Int.mul i j).val = (i.val * j.val) % 2^32 := by
  run_tac
    let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
      n.toString.endsWith ".CompCert4Lean.Lib.Integers.Int.suffix_wordcore_mul_val_nat")
      | throwError "Missing checked multiplication lemma"
    let e ← mkAppM nm #[← pure (mkFVar ((← getLCtx).findFromUserName? `i).get!.fvarId), ← pure (mkFVar ((← getLCtx).findFromUserName? `j).get!.fvarId)]
    (← getMainGoal).assign e
    replaceMainGoal []

private abbrev addr32_bv (i : int) : BitVec 32 := BitVec.ofFin i.toFin

private theorem addr32_bv_add (i j : int) :
    addr32_bv (CompCert4Lean.Lib.Integers.Int.add i j) = addr32_bv i + addr32_bv j := by
  apply BitVec.eq_of_toNat_eq
  exact addr32_add_val i j

private theorem addr32_bv_mul (i j : int) :
    addr32_bv (CompCert4Lean.Lib.Integers.Int.mul i j) = addr32_bv i * addr32_bv j := by
  apply BitVec.eq_of_toNat_eq
  exact addr32_mul_val i j

private theorem addr32_uns_bits (i : int) (n : Z) (hn : 0 ≤ intOfZ n)
    (hi : is_uns n i) : i.val < 2 ^ (intOfZ n).toNat := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  by_cases hk32 : k < 32
  · have h := hi (ZArith.BinInt.Z.of_nat k)
    change _ → _ → CompCert4Lean.Lib.Integers.Int.testbit i
      (ZArith.BinInt.Z.of_nat k) = false at h
    rw [addr32_testbit_nat] at h
    apply h
    · change 0 ≤ intOfZ (zOfInt (Int.ofNat k)) ∧
        intOfZ (zOfInt (Int.ofNat k)) < 32
      simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast]
      omega
    · change intOfZ n ≤ intOfZ (zOfInt (Int.ofNat k))
      simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast]
      omega
  · apply Nat.testBit_lt_two_pow
    exact Nat.lt_of_lt_of_le i.toFin.isLt
      (Nat.pow_le_pow_right (by decide) (by change 32 ≤ k; omega))

private theorem addr32_uns_of_bits (i : int) (n : Z) (hn : 0 ≤ intOfZ n)
    (hi : i.val < 2 ^ (intOfZ n).toNat) : is_uns n i := by
  intro k hk hnk
  have hk0 : 0 ≤ intOfZ k := hk.1
  have he : k = ZArith.BinInt.Z.of_nat (intOfZ k).toNat := by
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt, Int.ofNat_eq_natCast, Int.toNat_of_nonneg hk0]
  change CompCert4Lean.Lib.Integers.Int.testbit i k = false
  rw [he, addr32_testbit_nat]
  apply Nat.testBit_lt_two_pow
  apply Nat.lt_of_lt_of_le hi
  apply Nat.pow_le_pow_right (by decide)
  change intOfZ n ≤ intOfZ k at hnk
  omega

private theorem addr32_bv_signed_range (b : BitVec 32) (k : Nat) (hk : k < 32) :
    (∀ j, k ≤ j → j < 32 → b.getLsbD j = b.msb) ↔
      -(2 ^ k : Int) ≤ b.toInt ∧ b.toInt < (2 ^ k : Int) := by
  cases hb : b.msb with
  | false =>
    have hv : b.toInt = (b.toNat : Int) := by
      simp [BitVec.toInt_eq_msb_cond, hb]
    rw [hv]
    constructor
    · intro h
      have hu : b.toNat < 2^k := by
        apply Nat.lt_pow_two_of_testBit
        intro j hj
        by_cases hj32 : j < 32
        · exact h j hj hj32
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le b.isLt
            (Nat.pow_le_pow_right (by decide) (by omega)))
      have hp := Nat.two_pow_pos k
      have hc : (2^k : Int) = (2^k : Nat) := (Int.natCast_pow 2 k).symm
      rw [hc]
      omega
    · intro h j hj hj32
      have hc : (2^k : Int) = (2^k : Nat) := (Int.natCast_pow 2 k).symm
      rw [hc] at h
      have hu : b.toNat < 2^k := by omega
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu
        (Nat.pow_le_pow_right (by decide) hj))
  | true =>
    have hv : b.toInt = (b.toNat : Int) - 2^32 := by
      simp [BitVec.toInt_eq_msb_cond, hb]
    rw [hv]
    have hc : (2^k : Int) = (2^k : Nat) := (Int.natCast_pow 2 k).symm
    rw [hc]
    have hnot : (~~~b).toNat = 2^32 - 1 - b.toNat := BitVec.toNat_not
    have hbnd := b.isLt
    constructor
    · intro h
      have hu : (~~~b).toNat < 2^k := by
        apply Nat.lt_pow_two_of_testBit
        intro j hj
        by_cases hj32 : j < 32
        · have hh := h j hj hj32
          change (~~~b).getLsbD j = false
          simp [BitVec.getLsbD_not, hj32, hh]
        · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (~~~b).isLt
            (Nat.pow_le_pow_right (by decide) (by omega)))
      have hp := Nat.two_pow_pos k
      omega
    · intro h j hj hj32
      have hu : (~~~b).toNat < 2^k := by omega
      have hh : (~~~b).getLsbD j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hu
          (Nat.pow_le_pow_right (by decide) hj))
      simpa [BitVec.getLsbD_not, hj32] using hh

private theorem addr32_sgn_bits (i : int) (n : Z)
    (hn : 0 < intOfZ n) (hn32 : intOfZ n ≤ 32) :
    is_sgn n i ↔
      -(2 ^ ((intOfZ n).toNat - 1) : Int) ≤ (addr32_bv i).toInt ∧
      (addr32_bv i).toInt < (2 ^ ((intOfZ n).toNat - 1) : Int) := by
  rw [← addr32_bv_signed_range (addr32_bv i) _ (by omega)]
  constructor
  · intro h j hj hj32
    have hh := h (ZArith.BinInt.Z.of_nat j)
    change _ → _ → CompCert4Lean.Lib.Integers.Int.testbit i
        (ZArith.BinInt.Z.of_nat j) =
      CompCert4Lean.Lib.Integers.Int.testbit i (ZArith.BinInt.Z.of_nat 31) at hh
    rw [addr32_testbit_nat, addr32_testbit_nat] at hh
    apply hh
    · change 0 ≤ intOfZ (zOfInt (Int.ofNat j)) ∧
        intOfZ (zOfInt (Int.ofNat j)) < 32
      simp only [intOfZ_zOfInt, Int.ofNat_eq_natCast]
      omega
    · change intOfZ (ZArith.BinInt.Z.sub n (.Zpos .xH)) ≤
        intOfZ (zOfInt (Int.ofNat j))
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, Int.ofNat_eq_natCast]
      change intOfZ n - 1 ≤ (j : Int)
      omega
  · intro h k hk hnk
    have hk0 : 0 ≤ intOfZ k := hk.1
    have hk32 : intOfZ k < 32 := hk.2
    have he : k = ZArith.BinInt.Z.of_nat (intOfZ k).toNat := by
      apply intOfZ_injective
      simp only [ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
        Int.ofNat_eq_natCast, Int.toNat_of_nonneg hk0]
    change CompCert4Lean.Lib.Integers.Int.testbit i k =
      CompCert4Lean.Lib.Integers.Int.testbit i (ZArith.BinInt.Z.of_nat 31)
    rw [he, addr32_testbit_nat, addr32_testbit_nat]
    apply h
    · change intOfZ (ZArith.BinInt.Z.sub n (.Zpos .xH)) ≤ intOfZ k at hnk
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hnk
      change intOfZ n - 1 ≤ intOfZ k at hnk
      omega
    · omega

private theorem addr32_sgn_large (i : int) (n : Z) (hn : 32 < intOfZ n) :
    is_sgn n i := by
  intro k hk hnk
  have hk32 : intOfZ k < 32 := hk.2
  change intOfZ (ZArith.BinInt.Z.sub n (.Zpos .xH)) ≤ intOfZ k at hnk
  simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at hnk
  change intOfZ n - 1 ≤ intOfZ k at hnk
  omega

private theorem addr32_pow_mono (n m : Nat) (h : n ≤ m) :
    (2^n : Int) ≤ 2^m := by
  have hn : (2^n : Int) = (2^n : Nat) := (Int.natCast_pow 2 n).symm
  have hm : (2^m : Int) = (2^m : Nat) := (Int.natCast_pow 2 m).symm
  rw [hn, hm]
  exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) h)

private theorem addr32_bmod_range (x : Int) (k : Nat) (hk : k ≤ 31)
    (hx : -(2^k : Int) ≤ x ∧ x < 2^k) :
    -(2^k : Int) ≤ x.bmod (2^32) ∧ x.bmod (2^32) < 2^k := by
  have hp := addr32_pow_mono k 31 hk
  change (2^k : Int) ≤ 2147483648 at hp
  have he : x.bmod (2^32) = x := by
    apply Int.bmod_eq_of_le
    · change -(2147483648 : Int) ≤ x; omega
    · change x < (2147483648 : Int); omega
  rw [he]
  exact hx

private theorem addr32_uns_add (i j : int) (n m : Z)
    (hn : 0 ≤ intOfZ n) (hm : 0 ≤ intOfZ m)
    (hi : is_uns n i) (hj : is_uns m j) :
    is_uns (ZArith.BinInt.Z.add (ZArith.BinInt.Z.max n m) (.Zpos .xH))
      (CompCert4Lean.Lib.Integers.Int.add i j) := by
  have hi' := addr32_uns_bits i n hn hi
  have hj' := addr32_uns_bits j m hm hj
  have hmax : intOfZ (ZArith.BinInt.Z.max n m) = max (intOfZ n) (intOfZ m) := by
    unfold ZArith.BinInt.Z.max
    split <;> omega
  have hsize : intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.max n m) (.Zpos .xH)) = max (intOfZ n) (intOfZ m) + 1 := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt, hmax]
    rfl
  apply addr32_uns_of_bits _ _ (by rw [hsize]; omega)
  rw [addr32_add_val, hsize]
  have hni : (intOfZ n).toNat ≤ (max (intOfZ n) (intOfZ m)).toNat := by omega
  have hmj : (intOfZ m).toNat ≤ (max (intOfZ n) (intOfZ m)).toNat := by omega
  have pi := Nat.pow_le_pow_right (n := 2) (by decide) hni
  have pj := Nat.pow_le_pow_right (n := 2) (by decide) hmj
  have he : (max (intOfZ n) (intOfZ m) + 1).toNat =
      (max (intOfZ n) (intOfZ m)).toNat + 1 := by omega
  rw [he, Nat.pow_succ]
  have hmod := Nat.mod_le (i.val + j.val) (2^32)
  omega

private theorem addr32_sgn_add (i j : int) (n m : Z)
    (hn : 0 < intOfZ n) (hm : 0 < intOfZ m)
    (hi : is_sgn n i) (hj : is_sgn m j) :
    is_sgn (ZArith.BinInt.Z.add (ZArith.BinInt.Z.max n m) (.Zpos .xH))
      (CompCert4Lean.Lib.Integers.Int.add i j) := by
  have hmax : intOfZ (ZArith.BinInt.Z.max n m) = max (intOfZ n) (intOfZ m) := by
    unfold ZArith.BinInt.Z.max
    split <;> omega
  have hsize : intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.max n m) (.Zpos .xH)) = max (intOfZ n) (intOfZ m) + 1 := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt, hmax]
    rfl
  by_cases h32 : max (intOfZ n) (intOfZ m) + 1 ≤ 32
  · apply (addr32_sgn_bits _ _ (by rw [hsize]; omega) (by rw [hsize]; omega)).mpr
    rw [hsize, addr32_bv_add, BitVec.toInt_add]
    have hi' := (addr32_sgn_bits i n hn (by omega)).mp hi
    have hj' := (addr32_sgn_bits j m hm (by omega)).mp hj
    let k := (max (intOfZ n) (intOfZ m)).toNat - 1
    have pi := addr32_pow_mono ((intOfZ n).toNat - 1) k (by dsimp [k]; omega)
    have pj := addr32_pow_mono ((intOfZ m).toNat - 1) k (by dsimp [k]; omega)
    have he : (max (intOfZ n) (intOfZ m) + 1).toNat - 1 = k + 1 := by dsimp [k]; omega
    rw [he]
    apply addr32_bmod_range _ _ (by dsimp [k]; omega)
    rw [Int.pow_succ]
    omega
  · apply addr32_sgn_large
    rw [hsize]
    omega

private theorem addr32_uns_mul (i j : int) (n m : Z)
    (hn : 0 ≤ intOfZ n) (hm : 0 ≤ intOfZ m)
    (hi : is_uns n i) (hj : is_uns m j) :
    is_uns (ZArith.BinInt.Z.add n m) (CompCert4Lean.Lib.Integers.Int.mul i j) := by
  have hi' := addr32_uns_bits i n hn hi
  have hj' := addr32_uns_bits j m hm hj
  apply addr32_uns_of_bits _ _
    (by simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]; omega)
  rw [addr32_mul_val]
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  have he : (intOfZ n + intOfZ m).toNat = (intOfZ n).toNat + (intOfZ m).toNat := by omega
  rw [he, Nat.pow_add]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    (Nat.mul_lt_mul_of_lt_of_lt hi' hj')

private theorem addr32_sgn_mul (i j : int) (n m : Z)
    (hn : 0 < intOfZ n) (hm : 0 < intOfZ m)
    (hi : is_sgn n i) (hj : is_sgn m j) :
    is_sgn (ZArith.BinInt.Z.add n m) (CompCert4Lean.Lib.Integers.Int.mul i j) := by
  have hs : intOfZ (ZArith.BinInt.Z.add n m) = intOfZ n + intOfZ m := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  by_cases h32 : intOfZ n + intOfZ m ≤ 32
  · apply (addr32_sgn_bits _ _ (by rw [hs]; omega) (by rw [hs]; omega)).mpr
    rw [hs, addr32_bv_mul, BitVec.toInt_mul]
    have hi' := (addr32_sgn_bits i n hn (by omega)).mp hi
    have hj' := (addr32_sgn_bits j m hm (by omega)).mp hj
    let a := (2 ^ ((intOfZ n).toNat - 1) : Int)
    let b := (2 ^ ((intOfZ m).toNat - 1) : Int)
    have ha : 0 < a := Int.pow_pos (by decide)
    have hb : 0 < b := Int.pow_pos (by decide)
    have hprod : - (a*b) ≤ (addr32_bv i).toInt * (addr32_bv j).toInt ∧
        (addr32_bv i).toInt * (addr32_bv j).toInt ≤ a*b := by
      have hia : -(a : Int) ≤ (addr32_bv i).toInt ∧ (addr32_bv i).toInt ≤ a := by
        dsimp [a]; omega
      have hjb : -(b : Int) ≤ (addr32_bv j).toInt ∧ (addr32_bv j).toInt ≤ b := by
        dsimp [b]; omega
      have habs_i : (addr32_bv i).toInt.natAbs ≤ a.natAbs := by omega
      have habs_j : (addr32_bv j).toInt.natAbs ≤ b.natAbs := by omega
      have hp := Nat.mul_le_mul habs_i habs_j
      rw [← Int.natAbs_mul, ← Int.natAbs_mul] at hp
      have hab : 0 < a*b := Int.mul_pos ha hb
      omega
    have he : (intOfZ n + intOfZ m).toNat - 1 =
        ((intOfZ n).toNat - 1) + ((intOfZ m).toNat - 1) + 1 := by omega
    rw [he]
    apply addr32_bmod_range _ _ (by omega)
    rw [Int.pow_succ, Int.pow_add]
    change -(a*b*2) ≤ _ ∧ _ < a*b*2
    have hab := Int.mul_pos ha hb
    omega
  · apply addr32_sgn_large
    rw [hs]
    omega

private theorem addr32_uns_zero (i : int) (n : Z)
    (hn : intOfZ n ≤ 0) (hi : is_uns n i) :
    i = CompCert4Lean.Lib.Integers.Int.zero := by
  have hi0 : is_uns (.Z0) i := by
    intro k hk hnk
    apply hi k hk
    change intOfZ n ≤ intOfZ k
    have h := hk.1
    change 0 ≤ intOfZ k at h
    omega
  have hv := addr32_uns_bits i (.Z0) (by decide) hi0
  apply WordCore.ext_of_val_eq
  change i.val = 0
  change i.val < 1 at hv
  omega

private theorem addr32_uns_shape (p : aptr) (n : Z) :
    uns p n = if intOfZ n ≤ 0 then IU CompCert4Lean.Lib.Integers.Int.zero else uns1 p n := by
  unfold uns uns1
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.zle",
        ".CompCert4Lean.Backend.ValueDomain.boolOfSumbool"] do
      let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
        n.toString.endsWith suffix) | throwError "Missing comparison definition"
      evalTactic (← `(tactic| unfold $(mkIdent nm)))
  simp only [CompCert4Lean.Lib.Coqlib.zle, ZArith.ZArith_dec.Z_le_gt_dec,
    ZArith.BinInt.Z.le]
  have hz : intOfZ (.Z0 : Z) = 0 := rfl
  run_tac
    let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
      n.toString.endsWith ".CompCert4Lean.Backend.ValueDomain.z0")
      | throwError "Missing zero abbreviation"
    evalTactic (← `(tactic| unfold $(mkIdent nm)))
  by_cases h : intOfZ n ≤ 0 <;> simp only [hz, h, dite_true, dite_false,
    Bool.true_eq, Bool.false_eq_true, if_true, if_false]

private theorem addr32_vmatch_uns (bc : block_classification) (p : aptr)
    (n : Z) (i : int) (hn : 0 ≤ intOfZ n) (hi : is_uns n i) :
    vmatch bc (Vint i) (uns p n) := by
  rw [addr32_uns_shape]
  split
  · rename_i h
    rw [addr32_uns_zero i n h hi]
    exact vmatch.vmatch_iu _
  · exact vmatch_ge bc _ _ _ (vge_uns_i' p n i hn hi) (vmatch.vmatch_i i)

private theorem addr32_vmatch_uns_undef (bc : block_classification) (p : aptr) (n : Z) :
    vmatch bc Vundef (uns p n) := by
  rw [addr32_uns_shape]
  split
  · exact vmatch.iuUndef _
  · exact vmatch_ge bc _ _ _ (vge_uns_uns' p n) (vmatch.vmatch_Uns_undef p n)

private theorem addr32_vmatch_sgn (bc : block_classification) (p : aptr)
    (n : Z) (i : int) (hn : 0 < intOfZ n) (hi : is_sgn n i) :
    vmatch bc (Vint i) (sgn p n) := by
  exact vmatch_ge bc _ _ _ (vge_sgn_i' p n i hn hi) (vmatch.vmatch_i i)

private theorem addr32_vmatch_sgn_undef (bc : block_classification) (p : aptr) (n : Z) :
    vmatch bc Vundef (sgn p n) := by
  exact vmatch_ge bc _ _ _ (vge_sgn_sgn' p n) (vmatch.sgnUndef p n)

private theorem addr32_usize : ∀ (i : int), is_uns (usize i) i := by
  run_tac
    let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
      n.toString.endsWith ".CompCert4Lean.Backend.ValueDomain.is_uns_usize_select_aux")
      | throwError "Missing checked unsigned-size lemma"
    (← getMainGoal).assign (mkConst nm)
    replaceMainGoal []

private theorem addr32_ssize : ∀ (i : int), is_sgn (ssize i) i := by
  run_tac
    let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
      n.toString.endsWith ".CompCert4Lean.Backend.ValueDomain.is_sgn_ssize_select_aux")
      | throwError "Missing checked signed-size lemma"
    (← getMainGoal).assign (mkConst nm)
    replaceMainGoal []

private theorem addr32_uns_sgn (n : Z) (i : int) (hi : is_uns n i) :
    is_sgn (ZArith.BinInt.Z.add n (.Zpos .xH)) i := by
  have hh : ∀ n m i, is_uns n i → ZArith.BinInt.Z.lt n m → is_sgn m i := by
    run_tac
      let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
        n.toString.endsWith ".CompCert4Lean.Backend.ValueDomain.is_uns_sgn_vmatch")
        | throwError "Missing checked unsigned-to-signed lemma"
      (← getMainGoal).assign (mkConst nm)
      replaceMainGoal []
  apply hh n _ i hi
  change intOfZ n < intOfZ (ZArith.BinInt.Z.add n (.Zpos .xH))
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  change intOfZ n < intOfZ n + 1
  omega

private theorem addr32_max_int (n m : Z) :
    intOfZ (ZArith.BinInt.Z.max n m) = max (intOfZ n) (intOfZ m) := by
  unfold ZArith.BinInt.Z.max
  split <;> omega

private theorem addr32_pos_succ (n : Z) (h : 0 ≤ intOfZ n) :
    0 < intOfZ (ZArith.BinInt.Z.add n (.Zpos .xH)) := by
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  change 0 < intOfZ n + 1
  omega

private theorem addr32_nonneg_max_left (n m : Z) (h : 0 ≤ intOfZ n) :
    0 ≤ intOfZ (ZArith.BinInt.Z.max n m) := by
  rw [addr32_max_int]
  omega

private theorem addr32_nonneg_max_right (n m : Z) (h : 0 ≤ intOfZ m) :
    0 ≤ intOfZ (ZArith.BinInt.Z.max n m) := by
  rw [addr32_max_int]
  omega

private theorem addr32_usize_pos (i : int) : 0 ≤ intOfZ (usize i) := usize_pos i

private theorem addr32_ssize_pos (i : int) : 0 < intOfZ (ssize i) := ssize_pos i

private theorem addr32_add_comm (i j : int) :
    CompCert4Lean.Lib.Integers.Int.add i j = CompCert4Lean.Lib.Integers.Int.add j i :=
  CompCert4Lean.Lib.Integers.Int.add_commut_proof i j

private def addr32_unfold_arithmetic : TacticM Unit := do
  let suffixes := [".CompCert4Lean.Backend.ValueDomain.zAdd",
    ".CompCert4Lean.Backend.ValueDomain.zMax",
    ".CompCert4Lean.Backend.ValueDomain.zLe",
    ".CompCert4Lean.Backend.ValueDomain.zLt",
    ".CompCert4Lean.Backend.ValueDomain.z0",
    ".CompCert4Lean.Backend.ValueDomain.z1",
    ".CompCert4Lean.Common.Values.Int.add",
    ".CompCert4Lean.Common.Values.Int.mul"]
  let names := (← getEnv).constants.toList.filterMap fun (n, _) =>
    if suffixes.any (fun suffix => n.toString.endsWith suffix) then some (mkIdent n) else none
  for nm in names do
    evalTactic (← `(tactic| all_goals try unfold $nm:ident at *))

set_option maxHeartbeats 4000000 in
private theorem addr32_add_sound (bc : block_classification) (v w : val) (x y : aval)
    (hv : vmatch bc v x) (hw : vmatch bc w y) :
    vmatch bc (Val.add v w) (add x y) := by
  cases hv <;> cases hw <;>
    simp only [Val.add, add, CompCert4Lean.X86_64.Archi.ptr64, if_true,
      ntop2, ntop1, ntop]
  all_goals first
    | with_reducible exact addr32_vmatch_uns_undef _ _ _
    | with_reducible exact addr32_vmatch_sgn_undef _ _ _
    | with_reducible exact vmatch.vmatch_i _
    | with_reducible exact vmatch.vmatch_iu _
    | with_reducible exact vmatch.iuUndef _
    | with_reducible exact vmatch.ptrUndef _
    | with_reducible exact vmatch.ifptrUndef _
    | with_reducible exact vmatch.ifptrInt _ _
    | with_reducible exact vmatch.numUndef _
    | with_reducible exact vmatch.numInt _ _
    | skip
  all_goals first
    | with_reducible apply addr32_vmatch_uns
    | with_reducible apply addr32_vmatch_sgn
  run_tac addr32_unfold_arithmetic
  all_goals
    try simp only [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
      show intOfZ (.Z0 : Z) = 0 from rfl,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl] at *
  all_goals with_reducible first
    | solve
      | apply addr32_uns_add
        all_goals first
          | assumption
          | with_reducible exact addr32_usize _
          | with_reducible exact addr32_ssize _
          | with_reducible exact addr32_usize_pos _
          | with_reducible exact addr32_ssize_pos _
          | (with_reducible apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | rw [addr32_add_comm]
        apply addr32_uns_add
        all_goals first
          | assumption
          | with_reducible exact addr32_usize _
          | with_reducible exact addr32_ssize _
          | with_reducible exact addr32_usize_pos _
          | with_reducible exact addr32_ssize_pos _
          | (with_reducible apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | apply addr32_sgn_add
        all_goals first
          | assumption
          | with_reducible exact addr32_usize _
          | with_reducible exact addr32_ssize _
          | with_reducible exact addr32_usize_pos _
          | with_reducible exact addr32_ssize_pos _
          | (with_reducible apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | rw [addr32_add_comm]
        apply addr32_sgn_add
        all_goals first
          | assumption
          | with_reducible exact addr32_usize _
          | with_reducible exact addr32_ssize _
          | with_reducible exact addr32_usize_pos _
          | with_reducible exact addr32_ssize_pos _
          | (with_reducible apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | try apply Int.le_of_lt
        apply addr32_pos_succ
        apply addr32_nonneg_max_left
        first
          | assumption
          | (apply Int.le_of_lt; assumption)
          | (apply Int.le_of_lt; apply addr32_pos_succ; assumption)

private theorem addr32_nonneg_add (n m : Z)
    (hn : 0 ≤ intOfZ n) (hm : 0 ≤ intOfZ m) :
    0 ≤ intOfZ (ZArith.BinInt.Z.add n m) := by
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  omega

private theorem addr32_pos_add (n m : Z)
    (hn : 0 < intOfZ n) (hm : 0 < intOfZ m) :
    0 < intOfZ (ZArith.BinInt.Z.add n m) := by
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  omega

private theorem addr32_mul_base_const (bc : block_classification) (v : val)
    (x : aval) (j : int) (hv : vmatch bc v x) :
    vmatch bc (Val.mul v (Vint j)) (mul_base x (I j)) := by
  cases hv <;> simp only [mul_base, Val.mul, ntop2]
  all_goals with_reducible first
    | exact vmatch.numUndef _
    | exact vmatch.numInt _ _
    | exact addr32_vmatch_uns_undef _ _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | apply addr32_vmatch_uns
    | apply addr32_vmatch_sgn
  run_tac addr32_unfold_arithmetic
  all_goals try simp only [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
    show intOfZ (.Z0 : Z) = 0 from rfl] at *
  all_goals with_reducible first
    | solve
      | apply addr32_uns_mul
        all_goals first | assumption | exact addr32_usize_pos _ | exact addr32_usize _
    | solve
      | apply addr32_sgn_mul
        all_goals first | assumption | exact addr32_ssize_pos _ | exact addr32_ssize _
    | solve
      | apply addr32_nonneg_add
        all_goals first | assumption | exact addr32_usize_pos _
    | solve
      | apply addr32_pos_add
        all_goals first | assumption | exact addr32_ssize_pos _

private theorem addr32_vincl_zero (bc : block_classification) (v : val) (x : aval)
    (hv : vmatch bc v x) (h : vincl x (Uns Ptop (.Z0)) = true) :
    v = Vundef ∨ v = Vint CompCert4Lean.Lib.Integers.Int.zero := by
  cases hv <;> try exact Or.inl rfl
  all_goals simp only [vincl] at h
  all_goals try contradiction
  case vmatch_i i =>
    have he : CompCert4Lean.Lib.Integers.Int.zero_ext (.Z0) i = i :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hz : CompCert4Lean.Lib.Integers.Int.zero_ext (.Z0) i =
        CompCert4Lean.Lib.Integers.Int.zero := rfl
    exact Or.inr (congrArg Vint (he.symm.trans hz))
  case vmatch_iu i =>
    have he : CompCert4Lean.Lib.Integers.Int.zero_ext (.Z0) i = i :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    have hz : CompCert4Lean.Lib.Integers.Int.zero_ext (.Z0) i =
        CompCert4Lean.Lib.Integers.Int.zero := rfl
    exact Or.inr (congrArg Vint (he.symm.trans hz))
  case uns p i n hn hi =>
    have he := (Bool.and_eq_true_iff.mp h).1
    have hn0 : intOfZ n ≤ 0 := by
      run_tac withMainContext do
        let some (nm, _) := (← getEnv).constants.toList.find? (fun (n, _) =>
          n.toString.endsWith ".CompCert4Lean.Backend.ValueDomain.zle_true_prop_for_inval")
          | throwError "Missing checked comparison lemma"
        let some he := (← getLCtx).findDecl? (fun d => if d.userName.eraseMacroScopes.toString == "he" then some d else none)
          | throwError "Missing comparison hypothesis"
        let e ← mkAppM nm #[mkFVar he.fvarId]
        (← getMainGoal).assign e
        replaceMainGoal []
    exact Or.inr (congrArg Vint (addr32_uns_zero i n hn0 hi))

private theorem addr32_mul_const (bc : block_classification) (v : val)
    (x : aval) (j : int) (hv : vmatch bc v x) :
    vmatch bc (Val.mul v (Vint j)) (mul x (I j)) := by
  have hz : (vincl x (Uns Ptop (.Z0)) || vincl (I j) (Uns Ptop (.Z0))) = true →
      vmatch bc (Val.mul v (Vint j)) (IU CompCert4Lean.Lib.Integers.Int.zero) := by
    intro h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rcases addr32_vincl_zero bc v x hv h with he | he
      · rw [he]
        exact vmatch.iuUndef _
      · rw [he]
        change vmatch bc (Vint (CompCert4Lean.Lib.Integers.Int.mul
          CompCert4Lean.Lib.Integers.Int.zero j)) _
        rw [CompCert4Lean.Lib.Integers.Int.mul_commut_proof,
          CompCert4Lean.Lib.Integers.Int.mul_zero_proof]
        exact vmatch.vmatch_iu _
    · rcases addr32_vincl_zero bc (Vint j) (I j) (vmatch.vmatch_i j) h with he | he
      · contradiction
      · have hj : j = CompCert4Lean.Lib.Integers.Int.zero := val.Vint.inj he
        subst j
        cases v <;> simp only [Val.mul]
        run_tac addr32_unfold_arithmetic
        all_goals first
          | exact vmatch.iuUndef _
          | (rw [CompCert4Lean.Lib.Integers.Int.mul_zero_proof]; exact vmatch.vmatch_iu _)
  have hbase := addr32_mul_base_const bc v x j hv
  cases hv <;> simp only [mul, Val.mul]
  all_goals with_reducible first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | skip
  all_goals split
  all_goals first | (apply hz; assumption) | exact hbase


theorem eval_static_addressing_32_sound : eval_static_addressing_32_soundStatement := by
  intro bc ge hge sp hsp addr vargs vres aargs he hm
  cases hm with
  | nil =>
      cases addr <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at he
  | cons v a hv ht =>
      cases ht with
      | nil =>
          cases addr <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at he
          all_goals cases he
          all_goals simp only [eval_static_addressing_32]
          all_goals apply addr32_add_sound
          all_goals first
            | exact hv
            | exact vmatch.vmatch_i _
            | exact addr32_mul_const bc _ _ _ hv
      | cons w b hw ht =>
          cases ht with
          | nil =>
              cases addr <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at he
              all_goals cases he
              all_goals simp only [eval_static_addressing_32]
              all_goals apply addr32_add_sound
              all_goals first
                | exact hv
                | exact vmatch.vmatch_i _
                | exact addr32_add_sound bc _ _ _ _ hv hw
                | (apply addr32_add_sound; exact addr32_mul_const bc _ _ _ hw;
                    exact vmatch.vmatch_i _)
          | cons z c hz ht =>
              cases addr <;> simp [eval_addressing32, CompCert4Lean.X86_64.Archi.ptr64] at he

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.X86.Op

private theorem addr64_padd_match (bc : block_classification) (b : block)
    (ofs n : ptrofs) (p : aptr) (h : pmatch bc b ofs p) :
    pmatch bc b (Ptrofs.add ofs n) (padd p n) := by
  cases h <;> simp only [padd]
  all_goals constructor <;> assumption

private theorem addr64_poffset_match (bc : block_classification) (b : block)
    (ofs ofs' : ptrofs) (p : aptr) (h : pmatch bc b ofs p) :
    pmatch bc b ofs' (poffset p) := by
  cases h <;> simp only [poffset]
  all_goals constructor <;> assumption

set_option maxHeartbeats 2000000 in
private theorem addr64_add_match (bc : block_classification)
    (v w : val) (x y : aval) (hv : vmatch bc v x) (hw : vmatch bc w y) :
    vmatch bc (Val.addl v w) (addl x y) := by
  cases hv <;> cases hw <;>
    simp only [Val.addl, addl, CompCert4Lean.X86_64.Archi.ptr64, if_true, ntop2]
  all_goals first
    | exact vmatch.long _
    | exact vmatch.numUndef _
    | exact vmatch.numLong _ _
    | exact vmatch.ptrUndef _
    | exact vmatch.ifptrUndef _
    | exact vmatch.ifptrLong _ _
    | (apply vmatch.ptr; apply addr64_padd_match; assumption)
    | (apply vmatch.ptr; apply addr64_poffset_match; assumption)
    | (apply vmatch.ifptrPtr; apply addr64_padd_match; assumption)
    | (apply vmatch.ifptrPtr; apply addr64_poffset_match; assumption)
    | (apply vmatch.ifptrPtr; apply pmatch_lub_l;
        apply addr64_poffset_match; assumption)
    | (apply vmatch.ifptrPtr; apply pmatch_lub_r;
        apply addr64_poffset_match; assumption)

private theorem addr64_mul_const_match (bc : block_classification)
    (v : val) (x : aval) (j : int64) (hv : vmatch bc v x) :
    vmatch bc (Val.mull v (Vlong j)) (mull x (L j)) := by
  cases hv <;> simp only [Val.mull, mull, binop_long, ntop2]
  all_goals first
    | exact vmatch.long _
    | exact vmatch.numUndef _
    | exact vmatch.numLong _ _

private theorem addr64_add_zero_left (ofs : ptrofs) :
    Ptrofs.add Ptrofs.zero ofs = ofs := by
  apply WordCore.ext_of_val_eq
  have hadd : (Ptrofs.add Ptrofs.zero ofs).val =
      (Ptrofs.zero.val + ofs.val) % (2 ^ Ptrofs.wordsize) := by
    run_tac
      let some (nm, _) := (← Lean.getEnv).constants.toList.find? (fun (n, _) =>
        n.toString.endsWith ".CompCert4Lean.Lib.Integers.WordCore.add_val")
        | throwError "Missing checked word addition lemma"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent nm) _ _))
  rw [hadd]
  change (0 + ofs.val) % (2 ^ Ptrofs.wordsize) = ofs.val
  rw [Nat.zero_add]
  apply Nat.mod_eq_of_lt
  exact ofs.toFin.isLt

theorem eval_static_addressing_64_sound : eval_static_addressing_64_soundStatement := by
  intro bc ge hge sp hsp addr vargs vres aargs he hm
  cases hm with
  | nil =>
      cases addr <;> simp [eval_addressing64, CompCert4Lean.X86_64.Archi.ptr64] at he
      all_goals cases he
      · exact symbol_address_sound bc ge hge _ _
      · simp only [eval_static_addressing_64, Val.offset_ptr, addr64_add_zero_left]
        exact vmatch.ptr _ _ _ (pmatch.stk hsp)
  | cons v a hv ht =>
      cases ht with
      | nil =>
          cases addr <;> simp [eval_addressing64] at he
          all_goals cases he
          all_goals simp only [eval_static_addressing_64]
          all_goals apply addr64_add_match
          all_goals first
            | exact hv
            | exact vmatch.long _
            | exact addr64_mul_const_match bc _ _ _ hv
      | cons w b hw ht =>
          cases ht with
          | nil =>
              cases addr <;> simp [eval_addressing64] at he
              all_goals cases he
              all_goals simp only [eval_static_addressing_64]
              all_goals apply addr64_add_match
              all_goals first
                | exact hv
                | exact vmatch.long _
                | exact addr64_add_match bc _ _ _ _ hv hw
                | (apply addr64_add_match; exact addr64_mul_const_match bc _ _ _ hw;
                    exact vmatch.long _)
          | cons z c hz ht =>
              cases addr <;> simp [eval_addressing64] at he

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

theorem eval_static_addressing_sound : eval_static_addressing_soundStatement := by
  exact eval_static_addressing_64_sound

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private abbrev ConditionComparison := CompCert4Lean.Lib.Integers.comparison

private def condition_compare (comparison : ConditionComparison) (left right : Int) : Bool :=
  match comparison with
  | .Ceq => decide (left = right)
  | .Cne => decide (left ≠ right)
  | .Clt => decide (left < right)
  | .Cle => decide (left ≤ right)
  | .Cgt => decide (right < left)
  | .Cge => decide (right ≤ left)

private def condition_interval (comparison : ConditionComparison) (lower upper value : Int) : abool :=
  match comparison with
  | .Ceq => if value < lower ∨ upper < value then Maybe false else Btop
  | .Cne => if value < lower ∨ upper < value then Maybe true else Btop
  | .Clt => if upper < value then Maybe true else if value ≤ lower then Maybe false else Btop
  | .Cle => if upper ≤ value then Maybe true else if value < lower then Maybe false else Btop
  | .Cgt => if value < lower then Maybe true else if upper ≤ value then Maybe false else Btop
  | .Cge => if value ≤ lower then Maybe true else if upper < value then Maybe false else Btop

private theorem condition_cmp_intv_eq (comparison : ConditionComparison) (lower upper value : Z) :
    cmp_intv comparison (lower, upper) value =
      condition_interval comparison (intOfZ lower) (intOfZ upper) (intOfZ value) := by
  cases comparison <;> simp only [cmp_intv, condition_interval]
  all_goals
    run_tac
      let environment ← Lean.getEnv
      for suffix in [".CompCert4Lean.Backend.ValueDomain.zlt",
          ".CompCert4Lean.Backend.ValueDomain.zle",
          ".CompCert4Lean.Backend.ValueDomain.boolOfSumbool"] do
        let some (declaration, _) := environment.constants.toList.find?
          (fun (declaration, _) => declaration.toString.endsWith suffix)
          | throwError "Missing existing abstract-domain comparison definition"
        Lean.Elab.Tactic.evalTactic (← `(tactic| try unfold $(Lean.mkIdent declaration)))
  all_goals
    cases lowerLt : CompCert4Lean.Lib.Coqlib.zlt value lower <;>
      cases upperLt : CompCert4Lean.Lib.Coqlib.zlt upper value <;>
      cases lowerLe : CompCert4Lean.Lib.Coqlib.zle value lower <;>
      cases upperLe : CompCert4Lean.Lib.Coqlib.zle upper value <;>
      simp only [lowerLt, upperLt, lowerLe, upperLe]
  all_goals clear lowerLt upperLt lowerLe upperLe
  all_goals rename_i lowerOrder upperOrder lowerBound upperBound
  all_goals first
    | have lowerNative : intOfZ value < intOfZ lower := lowerOrder
    | have lowerNative : intOfZ lower ≤ intOfZ value := lowerOrder
  all_goals first
    | have upperNative : intOfZ upper < intOfZ value := upperOrder
    | have upperNative : intOfZ value ≤ intOfZ upper := upperOrder
  all_goals first
    | have lowerBoundNative : intOfZ value ≤ intOfZ lower := lowerBound
    | have lowerBoundNative : intOfZ lower < intOfZ value := lowerBound
  all_goals first
    | have upperBoundNative : intOfZ upper ≤ intOfZ value := upperBound
    | have upperBoundNative : intOfZ value < intOfZ upper := upperBound
  all_goals simp [lowerNative, upperNative, lowerBoundNative, upperBoundNative]
  all_goals repeat first | rfl | (exfalso; omega) | split

private theorem condition_maybe_true (proposition : Prop) [Decidable proposition]
    (holds : proposition) : cmatch (some (decide proposition)) (Maybe true) := by
  simp only [holds, decide_true]
  constructor

private theorem condition_maybe_false (proposition : Prop) [Decidable proposition]
    (fails : ¬proposition) : cmatch (some (decide proposition)) (Maybe false) := by
  simp only [fails, decide_false]
  constructor

private theorem condition_interval_sound (comparison : ConditionComparison) (lower upper left right : Int)
    (bounds : lower ≤ left ∧ left ≤ upper) :
    cmatch (some (condition_compare comparison left right))
      (condition_interval comparison lower upper right) := by
  cases comparison <;> simp only [condition_interval, condition_compare]
  all_goals repeat first
    | exact cmatch.topCase _
    | (apply condition_maybe_true; omega)
    | (apply condition_maybe_false; omega)
    | split

private theorem condition_cmp_intv_none (comparison : ConditionComparison) (interval : Z × Z) (value : Z) :
    cmatch none (cmp_intv comparison interval value) := by
  rcases interval with ⟨lower, upper⟩
  rw [condition_cmp_intv_eq]
  cases comparison <;> simp only [condition_interval]
  all_goals split
  all_goals first | constructor | (split <;> constructor)

private theorem condition_not_sound (concrete : Option Bool) (abstract : abool)
    (matched : cmatch concrete abstract) :
    cmatch (concrete.map (!·)) (cnot abstract) := by
  cases matched <;> constructor

private theorem condition_word_lt (left right : int) :
    WordCore.lt left right = decide (intOfZ (CompCert4Lean.Lib.Integers.Int.signed left) <
      intOfZ (CompCert4Lean.Lib.Integers.Int.signed right)) := by
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".word_lt_eq_decide_aux")
      | throwError "Missing checked signed comparison lemma"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent declaration) _ _))

private theorem condition_word_ltu (left right : int) :
    WordCore.ltu left right = decide (intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned left) <
      intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned right)) := by
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".word_ltu_eq_decide_aux")
      | throwError "Missing checked unsigned comparison lemma"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent declaration) _ _))

private theorem condition_word_eq_signed (left right : int) :
    WordCore.eq left right = decide (intOfZ (CompCert4Lean.Lib.Integers.Int.signed left) =
      intOfZ (CompCert4Lean.Lib.Integers.Int.signed right)) := by
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".word_eq_eq_decide_signed_aux")
      | throwError "Missing checked signed equality lemma"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent declaration) _ _))

private theorem condition_word_eq_unsigned (left right : int) :
    WordCore.eq left right = decide (intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned left) =
      intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned right)) := by
  change decide (left.intval = right.intval) = decide (intOfZ left.intval = intOfZ right.intval)
  have equality : (left.intval = right.intval) ↔
      (intOfZ left.intval = intOfZ right.intval) :=
    ⟨congrArg intOfZ, fun same => intOfZ_injective same⟩
  simp only [equality]

private theorem condition_int_cmp (comparison : ConditionComparison) (left right : int) :
    CompCert4Lean.Lib.Integers.Int.cmp comparison left right =
      condition_compare comparison (intOfZ (CompCert4Lean.Lib.Integers.Int.signed left))
        (intOfZ (CompCert4Lean.Lib.Integers.Int.signed right)) := by
  cases comparison <;>
    simp +instances [CompCert4Lean.Lib.Integers.Int.cmp, WordCore.cmp, condition_compare,
      condition_word_lt, condition_word_eq_signed]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp +instances only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  all_goals try omega

private theorem condition_int_cmpu (comparison : ConditionComparison) (left right : int) :
    CompCert4Lean.Lib.Integers.Int.cmpu comparison left right =
      condition_compare comparison (intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned left))
        (intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned right)) := by
  cases comparison <;>
    simp +instances [CompCert4Lean.Lib.Integers.Int.cmpu, WordCore.cmpu, condition_compare,
      condition_word_ltu, condition_word_eq_unsigned]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp +instances only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  all_goals try omega

private theorem condition_unsigned_val (value : int) :
    intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned value) = (value.val : Int) := by
  have nonnegative : 0 ≤ intOfZ value.intval :=
    (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof value).1
  change intOfZ value.intval = ((intOfZ value.intval).toNat : Int)
  exact (Int.toNat_of_nonneg nonnegative).symm

private theorem condition_signed_val (value : int) :
    intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) =
      if value.val < 2 ^ 31 then (value.val : Int) else (value.val : Int) - 2 ^ 32 := by
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith
        ".CompCert4Lean.Lib.Integers.Int.suffix_signed_int")
      | throwError "Missing checked signed word interpretation"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent declaration) _))

private theorem condition_signed_bv (value : int) :
    intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) = (addr32_bv value).toInt := by
  rw [condition_signed_val, BitVec.toInt_eq_toNat_cond]
  change (if value.val < 2 ^ 31 then (value.val : Int) else (value.val : Int) - 2 ^ 32) =
    if 2 * value.val < 2 ^ 32 then (value.val : Int) else (value.val : Int) - 2 ^ 32
  have sameTest : (2 * value.val < 2 ^ 32) ↔ value.val < 2 ^ 31 := by omega
  simp only [sameTest]

private theorem condition_power (width : Z) (nonnegative : 0 ≤ intOfZ width) :
    intOfZ (two_p width) = (2 : Int) ^ (intOfZ width).toNat := by
  simp only [two_p, ZArith.Zpower.two_p, ZArith.BinInt.Z.pow,
    show ¬intOfZ width < 0 by omega, if_false, intOfZ_zOfInt]
  rfl

private theorem condition_uintv_uns (pointer : aptr) (width : Z) :
    uintv (Uns pointer width) =
      if intOfZ width < 32 then
        (.Z0, ZArith.BinInt.Z.sub (two_p width) (.Zpos .xH))
      else (.Z0, CompCert4Lean.Lib.Integers.Int.max_unsigned) := by
  unfold uintv
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.zlt",
        ".CompCert4Lean.Backend.ValueDomain.boolOfSumbool"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases decision : CompCert4Lean.Lib.Coqlib.zlt width
      CompCert4Lean.Lib.Integers.Int.zwordsize with
  | left smaller =>
      have smallerNative : intOfZ width < 32 := smaller
      simp only [decision, smallerNative, if_true]
  | right larger =>
      have largerNative : 32 ≤ intOfZ width := larger
      simp only [decision, show ¬intOfZ width < 32 by omega, Bool.false_eq_true, if_false]

private theorem condition_unsigned_bounds (classification : block_classification)
    (value : int) (abstract : aval) (matched : vmatch classification (Vint value) abstract) :
    intOfZ (uintv abstract).1 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned value) ∧
      intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned value) ≤ intOfZ (uintv abstract).2 := by
  cases matched
  all_goals first
    | exact ⟨Int.le_refl _, Int.le_refl _⟩
    | exact CompCert4Lean.Lib.Integers.Int.unsigned_range_2_proof _
    | skip
  rename_i pointer width nonnegative bits
  rw [condition_uintv_uns]
  split
  · rename_i smaller
    have nonnegativeNative : 0 ≤ intOfZ width := nonnegative
    have bound := addr32_uns_bits value width nonnegativeNative bits
    simp only [Prod.fst, Prod.snd, ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      condition_power width nonnegativeNative, condition_unsigned_val]
    have powerNat : (2 : Int) ^ (intOfZ width).toNat =
        ((2 ^ (intOfZ width).toNat : Nat) : Int) := (Int.natCast_pow _ _).symm
    rw [powerNat]
    change 0 ≤ (value.val : Int) ∧ (value.val : Int) ≤ _ - 1
    omega
  · exact CompCert4Lean.Lib.Integers.Int.unsigned_range_2_proof _

private theorem condition_sintv_uns (pointer : aptr) (width : Z) :
    sintv (Uns pointer width) =
      if intOfZ width < 32 then
        (.Z0, ZArith.BinInt.Z.sub (two_p width) (.Zpos .xH))
      else (CompCert4Lean.Lib.Integers.Int.min_signed,
        CompCert4Lean.Lib.Integers.Int.max_signed) := by
  unfold sintv
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.zlt",
        ".CompCert4Lean.Backend.ValueDomain.boolOfSumbool"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases decision : CompCert4Lean.Lib.Coqlib.zlt width
      CompCert4Lean.Lib.Integers.Int.zwordsize with
  | left smaller =>
      have smallerNative : intOfZ width < 32 := smaller
      simp only [decision, smallerNative, if_true]
  | right larger =>
      have largerNative : 32 ≤ intOfZ width := larger
      simp only [decision, show ¬intOfZ width < 32 by omega, Bool.false_eq_true, if_false]

private theorem condition_sintv_sgn (pointer : aptr) (width : Z) :
    sintv (Sgn pointer width) =
      if intOfZ width < 32 then
        (ZArith.BinInt.Z.opp (two_p (ZArith.BinInt.Z.sub width (.Zpos .xH))),
          ZArith.BinInt.Z.sub (two_p (ZArith.BinInt.Z.sub width (.Zpos .xH))) (.Zpos .xH))
      else (CompCert4Lean.Lib.Integers.Int.min_signed,
        CompCert4Lean.Lib.Integers.Int.max_signed) := by
  unfold sintv
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.zlt",
        ".CompCert4Lean.Backend.ValueDomain.boolOfSumbool"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases decision : CompCert4Lean.Lib.Coqlib.zlt width
      CompCert4Lean.Lib.Integers.Int.zwordsize with
  | left smaller =>
      have smallerNative : intOfZ width < 32 := smaller
      simp only [decision, smallerNative, if_true]
  | right larger =>
      have largerNative : 32 ≤ intOfZ width := larger
      simp only [decision, show ¬intOfZ width < 32 by omega, Bool.false_eq_true, if_false]

private theorem condition_signed_bounds (classification : block_classification)
    (value : int) (abstract : aval) (matched : vmatch classification (Vint value) abstract) :
    intOfZ (sintv abstract).1 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) ∧
      intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) ≤ intOfZ (sintv abstract).2 := by
  cases matched
  all_goals first
    | exact ⟨Int.le_refl _, Int.le_refl _⟩
    | exact CompCert4Lean.Lib.Integers.Int.signed_range_proof _
    | skip
  · rename_i pointer width nonnegative bits
    rw [condition_sintv_uns]
    split
    · rename_i smaller
      have nonnegativeNative : 0 ≤ intOfZ width := nonnegative
      have bound := addr32_uns_bits value width nonnegativeNative bits
      have powerBound : 2 ^ (intOfZ width).toNat ≤ 2 ^ 31 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have smallValue : value.val < 2 ^ 31 := by omega
      rw [condition_signed_val, if_pos smallValue]
      simp only [Prod.fst, Prod.snd, ZArith.BinInt.Z.sub, intOfZ_zOfInt,
        condition_power width nonnegativeNative]
      have powerNat : (2 : Int) ^ (intOfZ width).toNat =
          ((2 ^ (intOfZ width).toNat : Nat) : Int) := (Int.natCast_pow _ _).symm
      rw [powerNat]
      change 0 ≤ (value.val : Int) ∧ (value.val : Int) ≤ _ - 1
      omega
    · exact CompCert4Lean.Lib.Integers.Int.signed_range_proof _
  · rename_i pointer width positive bits
    rw [condition_sintv_sgn]
    split
    · rename_i smaller
      have positiveNative : 0 < intOfZ width := positive
      have bounds := (addr32_sgn_bits value width positiveNative (by omega)).mp bits
      rw [condition_signed_bv]
      have widthSub : intOfZ (ZArith.BinInt.Z.sub width (.Zpos .xH)) =
          intOfZ width - 1 := by simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]; rfl
      simp only [Prod.fst, Prod.snd, ZArith.BinInt.Z.opp, ZArith.BinInt.Z.sub,
        intOfZ_zOfInt]
      rw [condition_power _ (by rw [intOfZ_zOfInt]; change 0 ≤ intOfZ width - 1; omega)]
      simp only [intOfZ_zOfInt]
      change -(2 ^ (intOfZ width - 1).toNat : Int) ≤ (addr32_bv value).toInt ∧
        (addr32_bv value).toInt ≤ (2 ^ (intOfZ width - 1).toNat : Int) - 1
      have exponentEq : (intOfZ width - 1).toNat = (intOfZ width).toNat - 1 := by omega
      rw [exponentEq]
      omega
    · exact CompCert4Lean.Lib.Integers.Int.signed_range_proof _

private theorem condition_signed_interval (classification : block_classification)
    (comparison : ConditionComparison) (left right : int) (abstract : aval)
    (matched : vmatch classification (Vint left) abstract) :
    cmatch (some (CompCert4Lean.Lib.Integers.Int.cmp comparison left right))
      (cmp_intv comparison (sintv abstract) (CompCert4Lean.Lib.Integers.Int.signed right)) := by
  rw [condition_int_cmp]
  cases intervalEq : sintv abstract with
  | mk lower upper =>
      rw [condition_cmp_intv_eq]
      apply condition_interval_sound
      simpa only [intervalEq] using condition_signed_bounds classification left abstract matched

private theorem condition_unsigned_interval (classification : block_classification)
    (comparison : ConditionComparison) (left right : int) (abstract : aval)
    (matched : vmatch classification (Vint left) abstract) :
    cmatch (some (CompCert4Lean.Lib.Integers.Int.cmpu comparison left right))
      (cmp_intv comparison (uintv abstract) (CompCert4Lean.Lib.Integers.Int.unsigned right)) := by
  rw [condition_int_cmpu]
  cases intervalEq : uintv abstract with
  | mk lower upper =>
      rw [condition_cmp_intv_eq]
      apply condition_interval_sound
      simpa only [intervalEq] using condition_unsigned_bounds classification left abstract matched

private theorem condition_different_none (configuration : CompilerConfig)
    (comparison : ConditionComparison) : cmatch none (cmp_different_blocks configuration comparison) := by
  cases comparison <;> simp only [cmp_different_blocks]
  all_goals first | constructor | (split <;> constructor)

private theorem condition_different_some (configuration : CompilerConfig)
    (comparison : ConditionComparison) :
    cmatch (Val.cmp_different_blocks comparison) (cmp_different_blocks configuration comparison) := by
  cases comparison <;> simp only [cmp_different_blocks, Val.cmp_different_blocks]
  all_goals first | constructor | (split <;> constructor)

private theorem condition_pointer_none (configuration : CompilerConfig)
    (comparison : ConditionComparison) (left right : aptr) :
    cmatch none (pcmp configuration comparison left right) := by
  cases left <;> cases right <;> simp only [pcmp]
  all_goals first
    | constructor
    | exact condition_different_none _ _
    | (split <;> constructor)

private theorem condition_cmp_constant (comparison : ConditionComparison) (left right : int) :
    cmp_bool comparison (I left) (I right) =
      Just (CompCert4Lean.Lib.Integers.Int.cmp comparison left right) := by
  unfold cmp_bool
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.Int.cmp",
        ".CompCert4Lean.Backend.ValueDomain.cmpWord"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases comparison <;> try rfl
  · change Just (CompCert4Lean.Lib.Integers.Int.lt left right ||
        CompCert4Lean.Lib.Integers.Int.eq left right) =
      Just (!CompCert4Lean.Lib.Integers.Int.lt right left)
    rw [CompCert4Lean.Lib.Integers.Int.lt_not_proof left right]
    simp
  · change Just (CompCert4Lean.Lib.Integers.Int.lt right left ||
        CompCert4Lean.Lib.Integers.Int.eq left right) =
      Just (!CompCert4Lean.Lib.Integers.Int.lt left right)
    rw [CompCert4Lean.Lib.Integers.Int.lt_not_proof right left,
      CompCert4Lean.Lib.Integers.Int.eq_sym_proof right left]
    simp

private theorem condition_cmpu_constant (configuration : CompilerConfig)
    (comparison : ConditionComparison) (left right : int) :
    cmpu_bool configuration comparison (I left) (I right) =
      Just (CompCert4Lean.Lib.Integers.Int.cmpu comparison left right) := by
  unfold cmpu_bool
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.Int.cmpu",
        ".CompCert4Lean.Backend.ValueDomain.cmpWord"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases comparison <;> try rfl
  · change Just (CompCert4Lean.Lib.Integers.Int.ltu left right ||
        CompCert4Lean.Lib.Integers.Int.eq left right) =
      Just (!CompCert4Lean.Lib.Integers.Int.ltu right left)
    rw [CompCert4Lean.Lib.Integers.Int.ltu_not_proof left right]
    simp
  · change Just (CompCert4Lean.Lib.Integers.Int.ltu right left ||
        CompCert4Lean.Lib.Integers.Int.eq left right) =
      Just (!CompCert4Lean.Lib.Integers.Int.ltu left right)
    rw [CompCert4Lean.Lib.Integers.Int.ltu_not_proof right left,
      CompCert4Lean.Lib.Integers.Int.eq_sym_proof right left]
    simp

private theorem condition_cmpl_constant (comparison : ConditionComparison) (left right : int64) :
    cmpl_bool comparison (L left) (L right) =
      Just (Int64.cmp comparison left right) := by
  unfold cmpl_bool
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.Int64.cmp",
        ".CompCert4Lean.Backend.ValueDomain.cmpWord"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases comparison <;> try rfl
  · change Just (CompCert4Lean.Lib.Integers.Int64.lt left right || Int64.eq left right) =
      Just (!CompCert4Lean.Lib.Integers.Int64.lt right left)
    rw [CompCert4Lean.Lib.Integers.Int64.lt_not_proof left right]
    simp
  · change Just (CompCert4Lean.Lib.Integers.Int64.lt right left || Int64.eq left right) =
      Just (!CompCert4Lean.Lib.Integers.Int64.lt left right)
    rw [CompCert4Lean.Lib.Integers.Int64.lt_not_proof right left, Int64.eq_sym_proof right left]
    simp

set_option maxHeartbeats 4000000 in
private theorem condition_cmp_sound (classification : block_classification)
    (comparison : ConditionComparison) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    cmatch (Val.cmp_bool comparison left right) (cmp_bool comparison leftAbstract rightAbstract) := by
  have originalLeft := leftMatch
  have originalRight := rightMatch
  cases leftMatch <;> cases rightMatch <;> simp only [Val.cmp_bool, cmp_bool]
  all_goals first
    | exact cmatch.topCase _
    | exact cmatch.justCase _
    | exact cmatch.maybeSome _
    | exact cmatch.maybeNone _
    | exact condition_cmp_intv_none _ _ _
    | (rename_i leftInteger rightInteger;
        have equality := condition_cmp_constant comparison leftInteger rightInteger;
        change Just _ = Just _ at equality;
        have booleanEq := abool.Just.inj equality;
        rw [booleanEq]; first | exact cmatch.justCase _ | exact cmatch.maybeSome _)
    | exact condition_signed_interval classification comparison _ _ _ originalLeft
    | (rw [← CompCert4Lean.Lib.Integers.Int.swap_cmp_proof comparison];
        exact condition_signed_interval classification _ _ _ _ originalRight)

set_option maxHeartbeats 4000000 in
private theorem condition_cmpu_sound (configuration : CompilerConfig)
    (classification : block_classification) (validPointer : block → Z → Bool)
    (comparison : ConditionComparison) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    cmatch (Val.cmpu_bool validPointer comparison left right)
      (cmpu_bool configuration comparison leftAbstract rightAbstract) := by
  have originalLeft := leftMatch
  have originalRight := rightMatch
  cases leftMatch <;> cases rightMatch <;>
    simp only [Val.cmpu_bool, cmpu_bool, CompCert4Lean.X86_64.Archi.ptr64,
      Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]
  all_goals first
    | exact cmatch.topCase _
    | exact cmatch.justCase _
    | exact cmatch.maybeSome _
    | exact cmatch.maybeNone _
    | exact condition_cmp_intv_none _ _ _
    | exact condition_pointer_none _ _ _ _
    | (rename_i leftInteger rightInteger;
        have equality := condition_cmpu_constant configuration comparison leftInteger rightInteger;
        change Just _ = Just _ at equality;
        have booleanEq := abool.Just.inj equality;
        rw [booleanEq]; first | exact cmatch.justCase _ | exact cmatch.maybeSome _)
    | exact condition_unsigned_interval classification comparison _ _ _ originalLeft
    | (rw [← CompCert4Lean.Lib.Integers.Int.swap_cmpu_proof comparison];
        exact condition_unsigned_interval classification _ _ _ _ originalRight)
    | (split <;> first | exact condition_different_none _ _ | exact cmatch.topCase _)

set_option maxHeartbeats 1000000 in
private theorem condition_cmpl_sound (classification : block_classification)
    (comparison : ConditionComparison) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    cmatch (Val.cmpl_bool comparison left right) (cmpl_bool comparison leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.cmpl_bool, cmpl_bool]
  all_goals first
    | exact cmatch.topCase _
    | (rename_i leftInteger rightInteger;
        change cmatch _ (cmpl_bool comparison (L leftInteger) (L rightInteger));
        rw [condition_cmpl_constant]; exact cmatch.justCase _)

set_option maxHeartbeats 1000000 in
private theorem condition_cmpf_sound (classification : block_classification)
    (comparison : ConditionComparison) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    cmatch (Val.cmpf_bool comparison left right) (cmpf_bool comparison leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.cmpf_bool, cmpf_bool]
  all_goals first | exact cmatch.topCase _ | exact cmatch.justCase _

set_option maxHeartbeats 1000000 in
private theorem condition_cmpfs_sound (classification : block_classification)
    (comparison : ConditionComparison) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    cmatch (Val.cmpfs_bool comparison left right) (cmpfs_bool comparison leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.cmpfs_bool, cmpfs_bool]
  all_goals first | exact cmatch.topCase _ | exact cmatch.justCase _

private theorem condition_cmplu_constant (configuration : CompilerConfig)
    (comparison : ConditionComparison) (left right : int64) :
    cmplu_bool configuration comparison (L left) (L right) =
      Just (Int64.cmpu comparison left right) := by
  unfold cmplu_bool
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.Int64.cmpu",
        ".CompCert4Lean.Backend.ValueDomain.cmpWord"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases comparison <;> try rfl
  · change Just (Int64.ltu left right || Int64.eq left right) = Just (!Int64.ltu right left)
    rw [Int64.ltu_not_proof left right]
    simp
  · change Just (Int64.ltu right left || Int64.eq left right) = Just (!Int64.ltu left right)
    rw [Int64.ltu_not_proof right left, Int64.eq_sym_proof right left]
    simp

private theorem condition_pcmp_stack (configuration : CompilerConfig)
    (comparison : ConditionComparison) (left right : ptrofs) :
    pcmp configuration comparison (Stk left) (Stk right) =
      Maybe (Ptrofs.cmpu comparison left right) := by
  unfold pcmp
  run_tac
    for suffix in [".CompCert4Lean.Backend.ValueDomain.Ptrofs.cmpu",
        ".CompCert4Lean.Backend.ValueDomain.cmpWord"] do
      let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (declaration, _) => declaration.toString.endsWith suffix)
        | throwError "Missing abstract-domain comparison definition"
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases comparison <;> try rfl
  · change Maybe (Ptrofs.ltu left right || Ptrofs.eq left right) =
      Maybe (!Ptrofs.ltu right left)
    rw [Ptrofs.ltu_not_proof left right]
    simp
  · change Maybe (Ptrofs.ltu right left || Ptrofs.eq left right) =
      Maybe (!Ptrofs.ltu left right)
    rw [Ptrofs.ltu_not_proof right left]
    have symmetric : Ptrofs.eq right left = Ptrofs.eq left right := by
      change decide (right.intval = left.intval) = decide (left.intval = right.intval)
      simp [eq_comm]
    rw [symmetric]
    simp

private theorem condition_pointers_same (validPointer : block → Z → Bool)
    (comparison : ConditionComparison) (base : block) (left right : ptrofs) :
    cmatch (Val.cmplu_bool validPointer comparison (Vptr base left) (Vptr base right))
      (Maybe (Ptrofs.cmpu comparison left right)) := by
  unfold Val.cmplu_bool
  simp only [CompCert4Lean.X86_64.Archi.ptr64, if_true]
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".CompCert4Lean.Common.Values.boolOfSumbool")
      | throwError "Missing concrete decision projection"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases equality : eq_block base base with
  | left same =>
      simp only [equality, if_true]
      split <;> constructor
  | right different => exact (different rfl).elim

private theorem condition_pointers_different (configuration : CompilerConfig)
    (validPointer : block → Z → Bool) (comparison : ConditionComparison)
    (leftBase rightBase : block) (left right : ptrofs) (different : leftBase ≠ rightBase) :
    cmatch (Val.cmplu_bool validPointer comparison (Vptr leftBase left) (Vptr rightBase right))
      (cmp_different_blocks configuration comparison) := by
  unfold Val.cmplu_bool
  simp only [CompCert4Lean.X86_64.Archi.ptr64, if_true]
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".CompCert4Lean.Common.Values.boolOfSumbool")
      | throwError "Missing concrete decision projection"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  cases equality : eq_block leftBase rightBase with
  | left same => exact (different same).elim
  | right differentProof =>
      simp only [equality, Bool.false_eq_true, if_false]
      split
      · exact condition_different_some _ _
      · exact condition_different_none _ _

set_option maxHeartbeats 1000000 in
private theorem condition_pointers_sound (configuration : CompilerConfig)
    (classification : block_classification) (validPointer : block → Z → Bool)
    (comparison : ConditionComparison) (leftBase rightBase : block) (left right : ptrofs)
    (leftAbstract rightAbstract : aptr)
    (leftMatch : pmatch classification leftBase left leftAbstract)
    (rightMatch : pmatch classification rightBase right rightAbstract) :
    cmatch (Val.cmplu_bool validPointer comparison (Vptr leftBase left) (Vptr rightBase right))
      (pcmp configuration comparison leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [pcmp]
  all_goals first
    | exact cmatch.topCase _
    | (apply condition_pointers_different; intro same; subst rightBase; simp_all)
    | skip
  · split
    · rename_i leftIdentifier leftGlobal rightIdentifier rightGlobal sameIdentifier
      subst rightIdentifier
      have sameBase := classification.bc_glob leftBase rightBase leftIdentifier leftGlobal rightGlobal
      subst rightBase
      have comparisonEq := condition_pcmp_stack configuration comparison left right
      change Maybe _ = Maybe _ at comparisonEq
      rw [abool.Maybe.inj comparisonEq]
      exact condition_pointers_same _ _ _ _ _
    · exact cmatch.topCase _
  · rename_i leftStack rightStack
    have sameBase := classification.bc_stack leftBase rightBase leftStack rightStack
    subst rightBase
    have comparisonEq := condition_pcmp_stack configuration comparison left right
    change Maybe _ = Maybe _ at comparisonEq
    rw [abool.Maybe.inj comparisonEq]
    exact condition_pointers_same _ _ _ _ _

set_option maxHeartbeats 4000000 in
private theorem condition_cmplu_sound (configuration : CompilerConfig)
    (classification : block_classification) (validPointer : block → Z → Bool)
    (comparison : ConditionComparison) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    cmatch (Val.cmplu_bool validPointer comparison left right)
      (cmplu_bool configuration comparison leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [cmplu_bool]
  all_goals first
    | exact cmatch.topCase _
    | (rename_i leftInteger rightInteger;
        change cmatch _ (cmplu_bool configuration comparison (L leftInteger) (L rightInteger));
        rw [condition_cmplu_constant]; exact cmatch.justCase _)
    | (apply condition_pointers_sound; assumption; assumption)
    | (change cmatch none _; exact condition_pointer_none _ _ _ _)
    | (simp only [Val.cmplu_bool]; split <;>
        first | exact cmatch.topCase _ | exact condition_different_none _ _)
    | (split
       · simp only [Val.cmplu_bool, CompCert4Lean.X86_64.Archi.ptr64, Bool.true_and]
         split
         · exact condition_different_some _ _
         · exact condition_different_none _ _
       · exact cmatch.topCase _)

private theorem condition_mask_uns_zero (width : Z) (value mask : int)
    (nonnegative : ZArith.BinInt.Z.le .Z0 width) (bits : is_uns width value)
    (masked : CompCert4Lean.Lib.Integers.Int.zero_ext width mask =
      CompCert4Lean.Lib.Integers.Int.zero) :
    CompCert4Lean.Lib.Integers.Int.and value mask = CompCert4Lean.Lib.Integers.Int.zero := by
  have fixed := (is_uns_zero_ext width value).mp bits
  change CompCert4Lean.Lib.Integers.Int.zero_ext width value = value at fixed
  rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof width value nonnegative] at fixed
  rw [CompCert4Lean.Lib.Integers.Int.zero_ext_and_proof width mask nonnegative] at masked
  calc
    CompCert4Lean.Lib.Integers.Int.and value mask =
        CompCert4Lean.Lib.Integers.Int.and
          (CompCert4Lean.Lib.Integers.Int.and value
            (CompCert4Lean.Lib.Integers.Int.repr (ZArith.BinInt.Z.sub (two_p width) (.Zpos .xH))))
          mask := congrArg (fun input => CompCert4Lean.Lib.Integers.Int.and input mask) fixed.symm
    _ = CompCert4Lean.Lib.Integers.Int.zero := by
      rw [CompCert4Lean.Lib.Integers.Int.and_assoc_proof,
        CompCert4Lean.Lib.Integers.Int.and_commut_proof _ mask, masked,
        CompCert4Lean.Lib.Integers.Int.and_zero_proof]

private theorem condition_mask_sound (classification : block_classification)
    (value : val) (abstract : aval) (mask : int) (matched : vmatch classification value abstract) :
    cmatch (Val.maskzero_bool value mask) (maskzero abstract mask) := by
  cases matched <;> simp only [Val.maskzero_bool, maskzero]
  all_goals first
    | exact cmatch.topCase _
    | exact cmatch.justCase _
    | exact cmatch.maybeSome _
    | exact cmatch.maybeNone _
    | skip
  · rename_i pointer integerValue width nonnegative bits
    split
    · rename_i masked
      change CompCert4Lean.Lib.Integers.Int.eq
        (CompCert4Lean.Lib.Integers.Int.zero_ext width mask) CompCert4Lean.Lib.Integers.Int.zero =
        true at masked
      have maskEq := CompCert4Lean.Lib.Integers.Int.eq_spec_proof
        (CompCert4Lean.Lib.Integers.Int.zero_ext width mask) CompCert4Lean.Lib.Integers.Int.zero
      rw [masked] at maskEq
      have zero := condition_mask_uns_zero width integerValue mask nonnegative bits maskEq
      change cmatch (some (CompCert4Lean.Lib.Integers.Int.eq
        (CompCert4Lean.Lib.Integers.Int.and integerValue mask) CompCert4Lean.Lib.Integers.Int.zero))
        (Maybe true)
      rw [zero, CompCert4Lean.Lib.Integers.Int.eq_true_proof]
      constructor
    · exact cmatch.topCase _
  · split <;> constructor

set_option maxHeartbeats 4000000 in
theorem eval_static_condition_sound : eval_static_condition_soundStatement := by
  intro configuration classification condition values memory abstracts matched
  cases matched with
  | nil => cases condition <;> exact cmatch.noneCase
  | cons firstValue firstAbstract firstMatch restMatch =>
      cases restMatch with
      | nil =>
          cases condition <;> simp only [CompCert4Lean.X86.Op.eval_condition, eval_static_condition]
          all_goals first
            | exact cmatch.noneCase
            | exact condition_cmp_sound classification _ _ _ _ _ firstMatch (vmatch.vmatch_i _)
            | exact condition_cmpu_sound configuration classification _ _ _ _ _ _ firstMatch
                (vmatch.vmatch_i _)
            | exact condition_cmpl_sound classification _ _ _ _ _ firstMatch (vmatch.long _)
            | exact condition_cmplu_sound configuration classification _ _ _ _ _ _ firstMatch
                (vmatch.long _)
            | exact condition_mask_sound classification _ _ _ firstMatch
            | exact condition_not_sound _ _ (condition_mask_sound classification _ _ _ firstMatch)
      | cons secondValue secondAbstract secondMatch tailMatch =>
          cases tailMatch with
          | nil =>
              cases condition <;> simp only [CompCert4Lean.X86.Op.eval_condition, eval_static_condition]
              all_goals first
                | exact cmatch.noneCase
                | exact condition_cmp_sound classification _ _ _ _ _ firstMatch secondMatch
                | exact condition_cmpu_sound configuration classification _ _ _ _ _ _
                    firstMatch secondMatch
                | exact condition_cmpl_sound classification _ _ _ _ _ firstMatch secondMatch
                | exact condition_cmplu_sound configuration classification _ _ _ _ _ _
                    firstMatch secondMatch
                | exact condition_cmpf_sound classification _ _ _ _ _ firstMatch secondMatch
                | exact condition_cmpfs_sound classification _ _ _ _ _ firstMatch secondMatch
                | exact condition_not_sound _ _
                    (condition_cmpf_sound classification _ _ _ _ _ firstMatch secondMatch)
                | exact condition_not_sound _ _
                    (condition_cmpfs_sound classification _ _ _ _ _ firstMatch secondMatch)
          | cons thirdValue thirdAbstract thirdMatch tailMatch =>
              cases condition <;> exact cmatch.noneCase

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.X86.Op

private theorem operation_unary_long (classification : block_classification)
    (semantic : int64 → int64) (value : val) (abstract : aval)
    (matched : vmatch classification value abstract) :
    vmatch classification ((fun operand : val => match operand with
      | Vlong input => Vlong (semantic input) | _ => Vundef) value)
      (unop_long semantic abstract) := by
  cases matched <;> simp only [unop_long, ntop1] <;> constructor

set_option maxHeartbeats 2000000 in
private theorem operation_binary_long (classification : block_classification)
    (semantic : int64 → int64 → int64)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification
      ((fun firstValue secondValue : val => match firstValue, secondValue with
        | Vlong first, Vlong second => Vlong (semantic first second) | _, _ => Vundef) left right)
      (binop_long semantic leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [binop_long, ntop2] <;> constructor

private theorem operation_unary_float (classification : block_classification)
    (semantic : CompCert4Lean.Lib.Floats.float → CompCert4Lean.Lib.Floats.float) (value : val) (abstract : aval)
    (matched : vmatch classification value abstract) :
    vmatch classification ((fun operand : val => match operand with
      | Vfloat input => Vfloat (semantic input) | _ => Vundef) value)
      (unop_float semantic abstract) := by
  cases matched <;> simp only [unop_float, ntop1] <;> constructor

private theorem operation_unary_single (classification : block_classification)
    (semantic : CompCert4Lean.Lib.Floats.float32 → CompCert4Lean.Lib.Floats.float32) (value : val) (abstract : aval)
    (matched : vmatch classification value abstract) :
    vmatch classification ((fun operand : val => match operand with
      | Vsingle input => Vsingle (semantic input) | _ => Vundef) value)
      (unop_single semantic abstract) := by
  cases matched <;> simp only [unop_single, ntop1] <;> constructor

set_option maxHeartbeats 2000000 in
private theorem operation_binary_single (classification : block_classification)
    (semantic : CompCert4Lean.Lib.Floats.float32 → CompCert4Lean.Lib.Floats.float32 → CompCert4Lean.Lib.Floats.float32)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification
      ((fun firstValue secondValue : val => match firstValue, secondValue with
        | Vsingle first, Vsingle second => Vsingle (semantic first second) | _, _ => Vundef) left right)
      (binop_single semantic leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [binop_single, ntop2] <;> constructor

private theorem operation_longofint (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.longofint value) (longofint abstract) := by
  cases matched <;> simp only [Val.longofint, longofint, ntop1] <;> constructor

private theorem operation_longofintu (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.longofintu value) (longofintu abstract) := by
  cases matched <;> simp only [Val.longofintu, longofintu, ntop1] <;> constructor

private theorem operation_loword (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.loword value) (loword abstract) := by
  cases matched <;> simp only [Val.loword, loword, ntop1] <;> constructor

private theorem operation_hiword (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.hiword value) (hiword abstract) := by
  cases matched <;> simp only [Val.hiword, hiword, ntop1] <;> constructor

private theorem operation_singleoffloat (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.singleoffloat value) (singleoffloat abstract) := by
  cases matched <;> simp only [Val.singleoffloat, singleoffloat, ntop1] <;> constructor

private theorem operation_floatofsingle (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.floatofsingle value) (floatofsingle abstract) := by
  cases matched <;> simp only [Val.floatofsingle, floatofsingle, ntop1] <;> constructor

set_option maxHeartbeats 2000000 in
private theorem operation_longofwords (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.longofwords left right) (longofwords leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.longofwords, longofwords, ntop2] <;> constructor

private theorem operation_floatofint
    [certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.floatofint value = some result) :
    vmatch classification result (floatofint abstract) := by
  cases matched <;> simp only [Val.floatofint, Option.some.injEq, reduceCtorEq] at evaluated
  all_goals subst result; simp only [floatofint, ntop1]; constructor

private theorem operation_floatoflong
    [certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.floatoflong value = some result) :
    vmatch classification result (floatoflong abstract) := by
  cases matched <;> simp only [Val.floatoflong, Option.some.injEq, reduceCtorEq] at evaluated
  all_goals subst result; simp only [floatoflong, ntop1]; constructor

private theorem operation_singleofint
    [certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.singleofint value = some result) :
    vmatch classification result (singleofint abstract) := by
  cases matched <;> simp only [Val.singleofint, Option.some.injEq, reduceCtorEq] at evaluated
  all_goals subst result; simp only [singleofint, ntop1]; constructor

private theorem operation_singleoflong
    [certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.singleoflong value = some result) :
    vmatch classification result (singleoflong abstract) := by
  cases matched <;> simp only [Val.singleoflong, Option.some.injEq, reduceCtorEq] at evaluated
  all_goals subst result; simp only [singleoflong, ntop1]; constructor

private theorem operation_intoffloat (configuration : CompilerConfig)
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.intoffloat value = some result) :
    vmatch classification result (intoffloat configuration abstract) := by
  cases matched <;> simp only [Val.intoffloat, reduceCtorEq] at evaluated
  all_goals
    obtain ⟨converted, conversion, resultEq⟩ := Option.map_eq_some_iff.mp evaluated
    subst result
    simp only [intoffloat, conversion, ntop1]
    constructor

private theorem operation_intofsingle (configuration : CompilerConfig)
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.intofsingle value = some result) :
    vmatch classification result (intofsingle configuration abstract) := by
  cases matched <;> simp only [Val.intofsingle, reduceCtorEq] at evaluated
  all_goals
    obtain ⟨converted, conversion, resultEq⟩ := Option.map_eq_some_iff.mp evaluated
    subst result
    simp only [intofsingle, conversion, ntop1]
    constructor

private theorem operation_longoffloat (configuration : CompilerConfig)
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.longoffloat value = some result) :
    vmatch classification result (longoffloat configuration abstract) := by
  cases matched <;> simp only [Val.longoffloat, reduceCtorEq] at evaluated
  all_goals
    obtain ⟨converted, conversion, resultEq⟩ := Option.map_eq_some_iff.mp evaluated
    subst result
    simp only [longoffloat, conversion, ntop1]
    constructor

private theorem operation_longofsingle (configuration : CompilerConfig)
    (classification : block_classification) (value result : val) (abstract : aval)
    (matched : vmatch classification value abstract) (evaluated : Val.longofsingle value = some result) :
    vmatch classification result (longofsingle configuration abstract) := by
  cases matched <;> simp only [Val.longofsingle, reduceCtorEq] at evaluated
  all_goals
    obtain ⟨converted, conversion, resultEq⟩ := Option.map_eq_some_iff.mp evaluated
    subst result
    simp only [longofsingle, conversion, ntop1]
    constructor

set_option maxHeartbeats 2000000 in
private theorem operation_shift_long (classification : block_classification)
    (semantic : int64 → int → int64) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification
      ((fun firstValue secondValue : val => match firstValue, secondValue with
       | Vlong value, Vint amount =>
           if CompCert4Lean.Lib.Integers.Int.ltu amount Int64.iwordsize' then
             Vlong (semantic value amount) else Vundef
       | _, _ => Vundef) left right)
      (shift_long semantic leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [shift_long, ntop1]
  all_goals first | constructor | (split <;> constructor)

set_option maxHeartbeats 2000000 in
private theorem operation_rotate_long (classification : block_classification)
    (semantic : int64 → int64 → int64) (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification
      ((fun firstValue secondValue : val => match firstValue, secondValue with
       | Vlong value, Vint amount =>
           Vlong (semantic value (Int64.repr (CompCert4Lean.Lib.Integers.Int.unsigned amount)))
       | _, _ => Vundef) left right)
      (rotate_long semantic leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [rotate_long, ntop1] <;> constructor

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open Lean Elab Tactic Meta

private def operation_unfold_domain (suffixes : List String) : TacticM Unit := do
  for suffix in suffixes do
    let some (declaration, _) := (← getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith
        (".CompCert4Lean.Backend.ValueDomain." ++ suffix))
      | throwError "Missing abstract-domain definition {suffix}"
    evalTactic (← `(tactic| all_goals try unfold $(mkIdent declaration) at *))

private theorem operation_uns_mono (value : int) (width larger : Z)
    (bits : is_uns width value) (bound : intOfZ width ≤ intOfZ larger) :
    is_uns larger value := by
  intro index inWord above
  exact bits index inWord (Int.le_trans bound above)

private theorem operation_sgn_mono (value : int) (width larger : Z)
    (bits : is_sgn width value) (bound : intOfZ width ≤ intOfZ larger) :
    is_sgn larger value := by
  intro index inWord above
  apply bits index inWord
  change intOfZ (ZArith.BinInt.Z.sub width (.Zpos .xH)) ≤ intOfZ index
  change intOfZ (ZArith.BinInt.Z.sub larger (.Zpos .xH)) ≤ intOfZ index at above
  simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at *
  omega

private theorem operation_match_uns (classification : block_classification) (pointer : aptr)
    (width : Z) (value : int) (bits : is_uns width value) :
    vmatch classification (Vint value) (uns pointer width) := by
  by_cases nonpositive : intOfZ width ≤ 0
  · rw [addr32_uns_shape, if_pos nonpositive, addr32_uns_zero value width nonpositive bits]
    constructor
  · exact addr32_vmatch_uns _ _ _ _ (by omega) bits

private theorem operation_sgn_shape (pointer : aptr) (width : Z) :
    sgn pointer width =
      if intOfZ width ≤ 8 then Sgn pointer (zOfNat 8)
      else if intOfZ width ≤ 16 then Sgn pointer (zOfNat 16) else Num pointer := by
  unfold sgn
  run_tac operation_unfold_domain ["zle", "boolOfSumbool", "zOfNat"]
  simp only [CompCert4Lean.Lib.Coqlib.zle, ZArith.ZArith_dec.Z_le_gt_dec,
    ZArith.BinInt.Z.le,
    show intOfZ (ZArith.BinInt.Z.of_nat 8) = 8 from rfl,
    show intOfZ (ZArith.BinInt.Z.of_nat 16) = 16 from rfl]
  by_cases first : intOfZ width ≤ 8 <;> by_cases second : intOfZ width ≤ 16 <;>
    simp only [first, second, dite_true, dite_false, Bool.true_eq, Bool.false_eq_true,
      if_true, if_false]

private theorem operation_match_sgn (classification : block_classification) (pointer : aptr)
    (width : Z) (value : int) (bits : is_sgn width value) :
    vmatch classification (Vint value) (sgn pointer width) := by
  rw [operation_sgn_shape]
  split
  · exact vmatch.sgn _ _ _ (by change (0 : Int) < 8; decide)
      (operation_sgn_mono _ _ _ bits (by assumption))
  · split
    · exact vmatch.sgn _ _ _ (by change (0 : Int) < 16; decide)
        (operation_sgn_mono _ _ _ bits (by assumption))
    · constructor

private theorem operation_uns_word (value : int) : is_uns (zOfNat 32) value := by
  intro index bounds lower
  have upper : intOfZ index < 32 := bounds.2
  change 32 ≤ intOfZ index at lower
  omega

private theorem operation_sgn_word (value : int) : is_sgn (zOfNat 32) value := by
  intro index bounds lower
  have upper : intOfZ index < 32 := bounds.2
  change 31 ≤ intOfZ index at lower
  have same : index = zOfNat 31 := by
    apply intOfZ_injective
    change intOfZ index = 31
    omega
  subst index
  rfl

private theorem operation_uns_and_left (left right : int) (width : Z)
    (bits : is_uns width left) :
    is_uns width (CompCert4Lean.Lib.Integers.Int.and left right) := by
  intro index bounds lower
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.and left right) index = false
  rw [CompCert4Lean.Lib.Integers.Int.bits_and_proof left right index bounds]
  have highBit := bits index bounds lower
  change CompCert4Lean.Lib.Integers.Int.testbit left index = false at highBit
  simp only [highBit, Bool.false_and]

private theorem operation_uns_and_right (left right : int) (width : Z)
    (bits : is_uns width right) :
    is_uns width (CompCert4Lean.Lib.Integers.Int.and left right) := by
  rw [CompCert4Lean.Lib.Integers.Int.and_commut_proof]
  exact operation_uns_and_left _ _ _ bits

private theorem operation_uns_and (left right : int) (leftWidth rightWidth : Z)
    (leftBits : is_uns leftWidth left) (rightBits : is_uns rightWidth right) :
    is_uns (ZArith.BinInt.Z.min leftWidth rightWidth)
      (CompCert4Lean.Lib.Integers.Int.and left right) := by
  by_cases order : intOfZ leftWidth ≤ intOfZ rightWidth
  · have minimum : ZArith.BinInt.Z.min leftWidth rightWidth = leftWidth := by
      simp only [ZArith.BinInt.Z.min, order, if_true]
    rw [minimum]
    exact operation_uns_and_left _ _ _ leftBits
  · have minimum : ZArith.BinInt.Z.min leftWidth rightWidth = rightWidth := by
      simp only [ZArith.BinInt.Z.min, order, if_false]
    rw [minimum]
    exact operation_uns_and_right _ _ _ rightBits

private theorem operation_uns_or (left right : int) (leftWidth rightWidth : Z)
    (leftBits : is_uns leftWidth left) (rightBits : is_uns rightWidth right) :
    is_uns (ZArith.BinInt.Z.max leftWidth rightWidth)
      (CompCert4Lean.Lib.Integers.Int.or left right) := by
  intro index bounds lower
  have lower' : max (intOfZ leftWidth) (intOfZ rightWidth) ≤ intOfZ index := by
    change intOfZ (ZArith.BinInt.Z.max leftWidth rightWidth) ≤ intOfZ index at lower
    simpa only [addr32_max_int] using lower
  have leftBit := leftBits index bounds (by change intOfZ leftWidth ≤ intOfZ index; omega)
  have rightBit := rightBits index bounds (by change intOfZ rightWidth ≤ intOfZ index; omega)
  change CompCert4Lean.Lib.Integers.Int.testbit left index = false at leftBit
  change CompCert4Lean.Lib.Integers.Int.testbit right index = false at rightBit
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.or left right) index = false
  rw [CompCert4Lean.Lib.Integers.Int.bits_or_proof left right index bounds, leftBit, rightBit]
  rfl

private theorem operation_uns_xor (left right : int) (leftWidth rightWidth : Z)
    (leftBits : is_uns leftWidth left) (rightBits : is_uns rightWidth right) :
    is_uns (ZArith.BinInt.Z.max leftWidth rightWidth)
      (CompCert4Lean.Lib.Integers.Int.xor left right) := by
  intro index bounds lower
  have lower' : max (intOfZ leftWidth) (intOfZ rightWidth) ≤ intOfZ index := by
    change intOfZ (ZArith.BinInt.Z.max leftWidth rightWidth) ≤ intOfZ index at lower
    simpa only [addr32_max_int] using lower
  have leftBit := leftBits index bounds (by change intOfZ leftWidth ≤ intOfZ index; omega)
  have rightBit := rightBits index bounds (by change intOfZ rightWidth ≤ intOfZ index; omega)
  change CompCert4Lean.Lib.Integers.Int.testbit left index = false at leftBit
  change CompCert4Lean.Lib.Integers.Int.testbit right index = false at rightBit
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.xor left right) index = false
  rw [CompCert4Lean.Lib.Integers.Int.bits_xor_proof left right index bounds, leftBit, rightBit]
  rfl

private theorem operation_sgn_and (left right : int) (leftWidth rightWidth : Z)
    (leftBits : is_sgn leftWidth left) (rightBits : is_sgn rightWidth right) :
    is_sgn (ZArith.BinInt.Z.max leftWidth rightWidth)
      (CompCert4Lean.Lib.Integers.Int.and left right) := by
  intro index bounds lower
  have lower' : max (intOfZ leftWidth) (intOfZ rightWidth) - 1 ≤ intOfZ index := by
    change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.max leftWidth rightWidth)
      (.Zpos .xH)) ≤ intOfZ index at lower
    simpa only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, addr32_max_int,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl] using lower
  have leftBit := leftBits index bounds (by
    change intOfZ (ZArith.BinInt.Z.sub leftWidth (.Zpos .xH)) ≤ intOfZ index
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega)
  have rightBit := rightBits index bounds (by
    change intOfZ (ZArith.BinInt.Z.sub rightWidth (.Zpos .xH)) ≤ intOfZ index
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega)
  change CompCert4Lean.Lib.Integers.Int.testbit left index =
    CompCert4Lean.Lib.Integers.Int.testbit left (zOfNat 31) at leftBit
  change CompCert4Lean.Lib.Integers.Int.testbit right index =
    CompCert4Lean.Lib.Integers.Int.testbit right (zOfNat 31) at rightBit
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.and left right) index =
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.and left right) (zOfNat 31)
  rw [CompCert4Lean.Lib.Integers.Int.bits_and_proof left right index bounds,
    CompCert4Lean.Lib.Integers.Int.bits_and_proof left right (zOfNat 31)
      (by change 0 ≤ (31 : Int) ∧ (31 : Int) < 32; decide),
    leftBit, rightBit]

private theorem operation_sgn_or (left right : int) (leftWidth rightWidth : Z)
    (leftBits : is_sgn leftWidth left) (rightBits : is_sgn rightWidth right) :
    is_sgn (ZArith.BinInt.Z.max leftWidth rightWidth)
      (CompCert4Lean.Lib.Integers.Int.or left right) := by
  intro index bounds lower
  have lower' : max (intOfZ leftWidth) (intOfZ rightWidth) - 1 ≤ intOfZ index := by
    change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.max leftWidth rightWidth)
      (.Zpos .xH)) ≤ intOfZ index at lower
    simpa only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, addr32_max_int,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl] using lower
  have leftBit := leftBits index bounds (by
    change intOfZ (ZArith.BinInt.Z.sub leftWidth (.Zpos .xH)) ≤ intOfZ index
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega)
  have rightBit := rightBits index bounds (by
    change intOfZ (ZArith.BinInt.Z.sub rightWidth (.Zpos .xH)) ≤ intOfZ index
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega)
  change CompCert4Lean.Lib.Integers.Int.testbit left index =
    CompCert4Lean.Lib.Integers.Int.testbit left (zOfNat 31) at leftBit
  change CompCert4Lean.Lib.Integers.Int.testbit right index =
    CompCert4Lean.Lib.Integers.Int.testbit right (zOfNat 31) at rightBit
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.or left right) index =
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.or left right) (zOfNat 31)
  rw [CompCert4Lean.Lib.Integers.Int.bits_or_proof left right index bounds,
    CompCert4Lean.Lib.Integers.Int.bits_or_proof left right (zOfNat 31)
      (by change 0 ≤ (31 : Int) ∧ (31 : Int) < 32; decide),
    leftBit, rightBit]

private theorem operation_sgn_xor (left right : int) (leftWidth rightWidth : Z)
    (leftBits : is_sgn leftWidth left) (rightBits : is_sgn rightWidth right) :
    is_sgn (ZArith.BinInt.Z.max leftWidth rightWidth)
      (CompCert4Lean.Lib.Integers.Int.xor left right) := by
  intro index bounds lower
  have lower' : max (intOfZ leftWidth) (intOfZ rightWidth) - 1 ≤ intOfZ index := by
    change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.max leftWidth rightWidth)
      (.Zpos .xH)) ≤ intOfZ index at lower
    simpa only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, addr32_max_int,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl] using lower
  have leftBit := leftBits index bounds (by
    change intOfZ (ZArith.BinInt.Z.sub leftWidth (.Zpos .xH)) ≤ intOfZ index
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega)
  have rightBit := rightBits index bounds (by
    change intOfZ (ZArith.BinInt.Z.sub rightWidth (.Zpos .xH)) ≤ intOfZ index
    simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
      show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega)
  change CompCert4Lean.Lib.Integers.Int.testbit left index =
    CompCert4Lean.Lib.Integers.Int.testbit left (zOfNat 31) at leftBit
  change CompCert4Lean.Lib.Integers.Int.testbit right index =
    CompCert4Lean.Lib.Integers.Int.testbit right (zOfNat 31) at rightBit
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.xor left right) index =
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.xor left right) (zOfNat 31)
  rw [CompCert4Lean.Lib.Integers.Int.bits_xor_proof left right index bounds,
    CompCert4Lean.Lib.Integers.Int.bits_xor_proof left right (zOfNat 31)
      (by change 0 ≤ (31 : Int) ∧ (31 : Int) < 32; decide),
    leftBit, rightBit]

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

set_option maxHeartbeats 4000000 in
private theorem operation_and (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.and left right) (CompCert4Lean.Backend.ValueDomain.«and» leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.and, CompCert4Lean.Backend.ValueDomain.«and», ntop2]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact addr32_vmatch_uns_undef _ _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | skip
  all_goals first | apply operation_match_uns | apply operation_match_sgn
  run_tac operation_unfold_domain ["zMin", "zMax", "Int.and"]
  all_goals first
    | solve
      | apply operation_uns_and _ _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | apply operation_uns_and_left _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | apply operation_uns_and_right _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | apply operation_sgn_and _ _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | change is_uns _ (CompCert4Lean.Lib.Integers.Int.and _ _)
        rw [CompCert4Lean.Lib.Integers.Int.and_commut_proof]
        apply operation_uns_and
        all_goals first | assumption | exact addr32_usize _

set_option maxHeartbeats 4000000 in
private theorem operation_or (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.or left right) (CompCert4Lean.Backend.ValueDomain.«or» leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.or, CompCert4Lean.Backend.ValueDomain.«or», ntop2]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact addr32_vmatch_uns_undef _ _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | skip
  all_goals first | apply operation_match_uns | apply operation_match_sgn
  run_tac operation_unfold_domain ["zMin", "zMax", "Int.or"]
  all_goals first
    | solve
      | apply operation_uns_or _ _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | apply operation_sgn_or _ _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | change is_uns _ (CompCert4Lean.Lib.Integers.Int.or _ _)
        rw [CompCert4Lean.Lib.Integers.Int.or_commut_proof]
        apply operation_uns_or
        all_goals first | assumption | exact addr32_usize _

set_option maxHeartbeats 4000000 in
private theorem operation_xor (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.xor left right) (CompCert4Lean.Backend.ValueDomain.xor leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;>
    simp only [Val.xor, CompCert4Lean.Backend.ValueDomain.xor, ntop2]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact addr32_vmatch_uns_undef _ _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | skip
  all_goals first | apply operation_match_uns | apply operation_match_sgn
  run_tac operation_unfold_domain ["zMin", "zMax", "Int.xor"]
  all_goals first
    | solve
      | apply operation_uns_xor _ _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | apply operation_sgn_xor _ _ _ _
        all_goals first | assumption | exact addr32_usize _
    | solve
      | change is_uns _ (CompCert4Lean.Lib.Integers.Int.xor _ _)
        rw [CompCert4Lean.Lib.Integers.Int.xor_commut_proof]
        apply operation_uns_xor
        all_goals first | assumption | exact addr32_usize _

private theorem operation_zero_ext_bits (value : int) (width known : Z)
    (bits : is_uns known value) :
    is_uns (ZArith.BinInt.Z.min known width)
      (CompCert4Lean.Lib.Integers.Int.zero_ext width value) := by
  unfold ZArith.BinInt.Z.min
  split
  · exact is_zero_ext_uns value width known (.inl bits)
  · exact is_zero_ext_uns value width width (.inr (Int.le_refl _))

private theorem operation_zero_ext (classification : block_classification)
    (width : Z) (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.zero_ext width value) (zero_ext width abstract) := by
  cases matched <;> simp only [Val.zero_ext, zero_ext]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact addr32_vmatch_uns_undef _ _ _
    | (apply operation_match_uns; exact operation_zero_ext_bits _ _ _ (by assumption))
    | (apply operation_match_uns; exact is_zero_ext_uns _ _ _ (.inr (Int.le_refl _)))

private theorem operation_sign_ext_bits (value : int) (width known : Z)
    (positive : 0 < intOfZ width) (knownPositive : 0 < intOfZ known)
    (bits : is_sgn known value) :
    is_sgn (ZArith.BinInt.Z.min known width)
      (CompCert4Lean.Lib.Integers.Int.sign_ext width value) := by
  unfold ZArith.BinInt.Z.min
  split
  · exact is_sign_ext_sgn value width known positive knownPositive (.inl bits)
  · exact is_sign_ext_sgn value width width positive positive (.inr (Int.le_refl _))

set_option maxHeartbeats 1000000 in
private theorem operation_sign_ext (classification : block_classification)
    (width : Z) (positive : 0 < intOfZ width) (value : val) (abstract : aval)
    (matched : vmatch classification value abstract) :
    vmatch classification (Val.sign_ext width value) (sign_ext width abstract) := by
  cases matched <;> simp only [Val.sign_ext, sign_ext]
  run_tac operation_unfold_domain ["zle", "zlt", "boolOfSumbool", "z0", "zMin"]
  all_goals simp only [CompCert4Lean.Lib.Coqlib.zle, CompCert4Lean.Lib.Coqlib.zlt,
    ZArith.ZArith_dec.Z_le_gt_dec, ZArith.ZArith_dec.Z_lt_dec,
    ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt, show intOfZ (.Z0 : Z) = 0 from rfl,
    show ¬ intOfZ width ≤ 0 from by omega, dite_false, Bool.false_eq_true, if_false]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact addr32_vmatch_sgn_undef _ _ _
    | (apply operation_match_sgn; exact operation_sign_ext_bits _ _ _ positive (by assumption) (by assumption))
    | (apply operation_match_sgn; exact is_sign_ext_sgn _ width width positive positive (.inr (Int.le_refl _)))
    | skip
  all_goals split <;> simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false]
  all_goals first
    | exact vmatch.vmatch_Uns_undef _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | (apply vmatch.uns; assumption; apply is_sign_ext_uns; constructor <;> assumption; assumption)
    | (apply operation_match_sgn; exact is_sign_ext_sgn _ width width positive positive (.inr (Int.le_refl _)))

set_option maxHeartbeats 2000000 in
private theorem operation_divls (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.divls left right = some result) :
    vmatch classification result (divls configuration leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.divls, reduceCtorEq] at evaluated
  all_goals split at evaluated <;> simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals subst result; simp_all only [divls, ntop2]; constructor

set_option maxHeartbeats 2000000 in
private theorem operation_divlu (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.divlu left right = some result) :
    vmatch classification result (divlu configuration leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.divlu, reduceCtorEq] at evaluated
  all_goals split at evaluated <;> simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals subst result; simp_all only [divlu, ntop2]; constructor

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_bv_sub (left right : int) :
    addr32_bv (CompCert4Lean.Lib.Integers.Int.sub left right) =
      addr32_bv left - addr32_bv right := by
  apply BitVec.eq_of_toNat_eq
  change (CompCert4Lean.Lib.Integers.Int.sub left right).val =
    (2 ^ 32 - right.val + left.val) % 2 ^ 32
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith
        ".CompCert4Lean.Lib.Integers.WordCore.sub_val")
      | throwError "Missing checked subtraction representation"
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent declaration) _ _))

private theorem operation_sgn_sub (left right : int) (leftWidth rightWidth : Z)
    (leftPositive : 0 < intOfZ leftWidth) (rightPositive : 0 < intOfZ rightWidth)
    (leftBits : is_sgn leftWidth left) (rightBits : is_sgn rightWidth right) :
    is_sgn (ZArith.BinInt.Z.add (ZArith.BinInt.Z.max leftWidth rightWidth) (.Zpos .xH))
      (CompCert4Lean.Lib.Integers.Int.sub left right) := by
  have widthValue : intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.max leftWidth rightWidth) (.Zpos .xH)) =
      max (intOfZ leftWidth) (intOfZ rightWidth) + 1 := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt, addr32_max_int]
    rfl
  by_cases small : max (intOfZ leftWidth) (intOfZ rightWidth) + 1 ≤ 32
  · apply (addr32_sgn_bits _ _ (by rw [widthValue]; omega) (by rw [widthValue]; omega)).mpr
    rw [widthValue, operation_bv_sub, BitVec.toInt_sub]
    have leftBound := (addr32_sgn_bits left leftWidth leftPositive (by omega)).mp leftBits
    have rightBound := (addr32_sgn_bits right rightWidth rightPositive (by omega)).mp rightBits
    let exponent := (max (intOfZ leftWidth) (intOfZ rightWidth)).toNat - 1
    have leftPower := addr32_pow_mono ((intOfZ leftWidth).toNat - 1) exponent (by dsimp [exponent]; omega)
    have rightPower := addr32_pow_mono ((intOfZ rightWidth).toNat - 1) exponent (by dsimp [exponent]; omega)
    have exponentEq : (max (intOfZ leftWidth) (intOfZ rightWidth) + 1).toNat - 1 = exponent + 1 := by
      dsimp [exponent]; omega
    rw [exponentEq]
    apply addr32_bmod_range _ _ (by dsimp [exponent]; omega)
    rw [Int.pow_succ]
    omega
  · apply addr32_sgn_large
    rw [widthValue]
    omega

private theorem operation_uns_sub (left right : int) (leftWidth rightWidth : Z)
    (leftPositive : 0 ≤ intOfZ leftWidth) (rightPositive : 0 ≤ intOfZ rightWidth)
    (leftBits : is_uns leftWidth left) (rightBits : is_uns rightWidth right) :
    is_sgn (ZArith.BinInt.Z.add (ZArith.BinInt.Z.max leftWidth rightWidth) (.Zpos .xH))
      (CompCert4Lean.Lib.Integers.Int.sub left right) := by
  have widthValue : intOfZ (ZArith.BinInt.Z.add
      (ZArith.BinInt.Z.max leftWidth rightWidth) (.Zpos .xH)) =
      max (intOfZ leftWidth) (intOfZ rightWidth) + 1 := by
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt, addr32_max_int]
    rfl
  by_cases small : max (intOfZ leftWidth) (intOfZ rightWidth) + 1 ≤ 32
  · apply (addr32_sgn_bits _ _ (by rw [widthValue]; omega) (by rw [widthValue]; omega)).mpr
    rw [widthValue, operation_bv_sub, BitVec.toInt_sub]
    have leftBound := addr32_uns_bits left leftWidth leftPositive leftBits
    have rightBound := addr32_uns_bits right rightWidth rightPositive rightBits
    let exponent := (max (intOfZ leftWidth) (intOfZ rightWidth)).toNat
    have leftPower := Nat.pow_le_pow_right (n := 2) (by decide)
      (show (intOfZ leftWidth).toNat ≤ exponent by dsimp [exponent]; omega)
    have rightPower := Nat.pow_le_pow_right (n := 2) (by decide)
      (show (intOfZ rightWidth).toNat ≤ exponent by dsimp [exponent]; omega)
    have halfPower := Nat.pow_le_pow_right (n := 2) (by decide)
      (show exponent ≤ 31 by dsimp [exponent]; omega)
    have leftSigned : (addr32_bv left).toInt = (left.val : Int) := by
      rw [BitVec.toInt_eq_toNat_bmod]
      change (left.val : Int).bmod 4294967296 = left.val
      apply Int.bmod_eq_of_le <;> omega
    have rightSigned : (addr32_bv right).toInt = (right.val : Int) := by
      rw [BitVec.toInt_eq_toNat_bmod]
      change (right.val : Int).bmod 4294967296 = right.val
      apply Int.bmod_eq_of_le <;> omega
    rw [leftSigned, rightSigned]
    have exponentEq : (max (intOfZ leftWidth) (intOfZ rightWidth) + 1).toNat - 1 = exponent := by
      dsimp [exponent]; omega
    rw [exponentEq]
    apply addr32_bmod_range _ _ (by dsimp [exponent]; omega)
    rw [show (2 ^ exponent : Int) = (2 ^ exponent : Nat) from (Int.natCast_pow 2 exponent).symm]
    omega
  · apply addr32_sgn_large
    rw [widthValue]
    omega

private theorem operation_sgn_neg (value : int) (width : Z)
    (positive : 0 < intOfZ width) (bits : is_sgn width value) :
    is_sgn (ZArith.BinInt.Z.add width (.Zpos .xH))
      (CompCert4Lean.Lib.Integers.Int.neg value) := by
  have zeroBits : is_sgn width CompCert4Lean.Lib.Integers.Int.zero := by
    intro index bounds lower
    change CompCert4Lean.Lib.Integers.Int.testbit CompCert4Lean.Lib.Integers.Int.zero index =
      CompCert4Lean.Lib.Integers.Int.testbit CompCert4Lean.Lib.Integers.Int.zero (zOfNat 31)
    exact (CompCert4Lean.Lib.Integers.Int.bits_zero_proof index).trans
      (CompCert4Lean.Lib.Integers.Int.bits_zero_proof (zOfNat 31)).symm
  have difference := operation_sgn_sub CompCert4Lean.Lib.Integers.Int.zero value width width
    positive positive zeroBits bits
  have equalWidth : ZArith.BinInt.Z.max width width = width := by
    unfold ZArith.BinInt.Z.max
    split <;> rfl
  rw [equalWidth, CompCert4Lean.Lib.Integers.Int.sub_add_opp_proof,
    CompCert4Lean.Lib.Integers.Int.add_zero_l_proof] at difference
  exact difference

private theorem operation_neg (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.neg value) (neg abstract) := by
  cases matched <;> simp only [Val.neg, neg, ntop1]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact addr32_vmatch_sgn_undef _ _ _
    | (apply operation_match_sgn; exact operation_sgn_neg _ _ (by assumption) (by assumption))

private theorem operation_sgn_not (value : int) (width : Z) (bits : is_sgn width value) :
    is_sgn width (CompCert4Lean.Lib.Integers.Int.not value) := by
  intro index bounds lower
  have bit := bits index bounds lower
  change CompCert4Lean.Lib.Integers.Int.testbit value index =
    CompCert4Lean.Lib.Integers.Int.testbit value (zOfNat 31) at bit
  change CompCert4Lean.Lib.Integers.Int.testbit
    (CompCert4Lean.Lib.Integers.Int.not value) index =
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.not value) (zOfNat 31)
  rw [CompCert4Lean.Lib.Integers.Int.bits_not_proof value index bounds,
    CompCert4Lean.Lib.Integers.Int.bits_not_proof value (zOfNat 31)
      (by change 0 ≤ (31 : Int) ∧ (31 : Int) < 32; decide), bit]

private theorem operation_not (classification : block_classification)
    (value : val) (abstract : aval) (matched : vmatch classification value abstract) :
    vmatch classification (Val.notint value) (notint abstract) := by
  cases matched <;> simp only [Val.notint, notint, ntop1]
  all_goals first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact vmatch.sgnUndef _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | (apply vmatch.sgn; assumption; apply operation_sgn_not; assumption)
    | (apply operation_match_sgn; apply operation_sgn_not; apply addr32_uns_sgn; assumption)

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_max_comm (left right : Z) :
    ZArith.BinInt.Z.max left right = ZArith.BinInt.Z.max right left := by
  apply intOfZ_injective
  rw [addr32_max_int, addr32_max_int]
  exact Int.max_comm _ _

private theorem operation_add_comm (left right : Z) :
    ZArith.BinInt.Z.add left right = ZArith.BinInt.Z.add right left := by
  apply intOfZ_injective
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
  omega

set_option maxHeartbeats 1000000 in
private theorem operation_sub_undefined (classification : block_classification) (left right : aval)
    (incompatible : ∀ first second, left = I first → right = I second → False) :
    vmatch classification Vundef (sub left right) := by
  cases left <;> cases right <;>
    simp only [sub, CompCert4Lean.X86_64.Archi.ptr64, if_true, ntop2]
  all_goals first
    | exact vmatch.iuUndef _
    | exact vmatch.numUndef _
    | exact vmatch.ifptrUndef _
    | exact addr32_vmatch_sgn_undef _ _ _
    | exact (incompatible _ _ rfl rfl).elim

set_option maxHeartbeats 1000000 in
private theorem operation_sub (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.sub left right) (sub leftAbstract rightAbstract) := by
  cases left <;> cases right <;>
    simp only [Val.sub, CompCert4Lean.X86_64.Archi.ptr64, if_true]
  all_goals try
    solve
    | apply operation_sub_undefined
      intro first second leftEquality rightEquality
      subst leftAbstract
      subst rightAbstract
      cases leftMatch <;> cases rightMatch
  cases leftMatch <;> cases rightMatch <;>
    simp only [sub, ntop2, CompCert4Lean.X86_64.Archi.ptr64, if_true]
  all_goals with_reducible first
    | exact vmatch.vmatch_i _
    | exact vmatch.vmatch_iu _
    | exact vmatch.iuUndef _
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact vmatch.ifptrInt _ _
    | exact vmatch.ifptrUndef _
    | exact addr32_vmatch_sgn_undef _ _ _
    | skip
  all_goals with_reducible apply operation_match_sgn
  run_tac operation_unfold_domain ["zAdd", "zMax", "Int.sub", "zLe", "zLt", "z0"]
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".CompCert4Lean.Common.Values.Int.sub")
      | throwError "Missing concrete subtraction definition"
    Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals unfold $(Lean.mkIdent declaration)))
  all_goals simp only [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
    show intOfZ (.Z0 : Z) = 0 from rfl] at *
  all_goals with_reducible first
    | solve
      | apply operation_uns_sub
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | apply operation_sgn_sub
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | rw [operation_max_comm]
        apply operation_sgn_sub
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)

set_option maxHeartbeats 1000000 in
private theorem operation_mul_base_undefined (classification : block_classification) (left right : aval) :
    vmatch classification Vundef (mul_base left right) := by
  cases left <;> cases right <;> simp only [mul_base, ntop2]
  all_goals first
    | exact vmatch.numUndef _
    | exact addr32_vmatch_uns_undef _ _ _
    | exact addr32_vmatch_sgn_undef _ _ _

set_option maxHeartbeats 1000000 in
private theorem operation_mul_base (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mul left right) (mul_base leftAbstract rightAbstract) := by
  cases left <;> cases right <;> simp only [Val.mul]
  all_goals try exact operation_mul_base_undefined _ _ _
  cases leftMatch <;> cases rightMatch <;> simp only [mul_base, ntop2]
  all_goals with_reducible first
    | exact vmatch.numInt _ _
    | exact vmatch.numUndef _
    | exact addr32_vmatch_uns_undef _ _ _
    | exact addr32_vmatch_sgn_undef _ _ _
    | skip
  all_goals with_reducible first | apply operation_match_uns | apply operation_match_sgn
  run_tac operation_unfold_domain ["zAdd", "Int.mul", "zLe", "zLt", "z0"]
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".CompCert4Lean.Common.Values.Int.mul")
      | throwError "Missing concrete multiplication definition"
    Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals unfold $(Lean.mkIdent declaration)))
  all_goals simp only [ZArith.BinInt.Z.le, ZArith.BinInt.Z.lt,
    show intOfZ (.Z0 : Z) = 0 from rfl] at *
  all_goals with_reducible first
    | solve
      | apply addr32_uns_mul
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | apply addr32_sgn_mul
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | rw [operation_add_comm]
        apply addr32_uns_mul
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)
    | solve
      | rw [operation_add_comm]
        apply addr32_sgn_mul
        all_goals first
          | assumption
          | exact addr32_usize _
          | exact addr32_ssize _
          | exact addr32_usize_pos _
          | exact addr32_ssize_pos _
          | (apply addr32_uns_sgn; assumption)
          | (apply addr32_pos_succ; assumption)

private theorem operation_mul_zero_left (classification : block_classification) (right : val) :
    vmatch classification (Val.mul (Vint CompCert4Lean.Lib.Integers.Int.zero) right)
      (IU CompCert4Lean.Lib.Integers.Int.zero) := by
  cases right <;> simp only [Val.mul] <;> try exact vmatch.iuUndef _
  change vmatch _ (Vint (CompCert4Lean.Lib.Integers.Int.mul CompCert4Lean.Lib.Integers.Int.zero _)) _
  rw [CompCert4Lean.Lib.Integers.Int.mul_commut_proof, CompCert4Lean.Lib.Integers.Int.mul_zero_proof]
  constructor

private theorem operation_mul_zero_right (classification : block_classification) (left : val) :
    vmatch classification (Val.mul left (Vint CompCert4Lean.Lib.Integers.Int.zero))
      (IU CompCert4Lean.Lib.Integers.Int.zero) := by
  cases left <;> simp only [Val.mul] <;> try exact vmatch.iuUndef _
  change vmatch _ (Vint (CompCert4Lean.Lib.Integers.Int.mul _ CompCert4Lean.Lib.Integers.Int.zero)) _
  rw [CompCert4Lean.Lib.Integers.Int.mul_zero_proof]
  constructor

set_option maxHeartbeats 300000 in
private theorem operation_mul (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mul left right) (mul leftAbstract rightAbstract) := by
  have zeroCase : (vincl leftAbstract (Uns Ptop .Z0) || vincl rightAbstract (Uns Ptop .Z0)) = true →
      vmatch classification (Val.mul left right) (IU CompCert4Lean.Lib.Integers.Int.zero) := by
    intro condition
    rcases Bool.or_eq_true_iff.mp condition with leftZero | rightZero
    · rcases addr32_vincl_zero classification left leftAbstract leftMatch leftZero with equality | equality
      · subst left; cases right <;> exact vmatch.iuUndef _
      · subst left; exact operation_mul_zero_left _ _
    · rcases addr32_vincl_zero classification right rightAbstract rightMatch rightZero with equality | equality
      · subst right; cases left <;> exact vmatch.iuUndef _
      · subst right; exact operation_mul_zero_right _ _
  have base := operation_mul_base classification left right leftAbstract rightAbstract leftMatch rightMatch
  cases leftAbstract <;> cases rightAbstract <;> simp only [mul]
  all_goals first
    | (split; apply zeroCase; assumption; exact base)
    | (cases leftMatch <;> cases rightMatch <;> constructor)

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private def operation_unfold_bit_selector : Lean.Elab.Tactic.TacticM Unit := do
  for suffix in [".CompCert4Lean.Lib.Integers.zltSelect", ".CompCert4Lean.Lib.Integers.sumboolSelect"] do
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
        (fun (name, _) => name.toString.endsWith suffix)
      | throwError "Integer bit selector definition unavailable"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))

private theorem operation_bits_shl (value amount : int) (index : Z)
    (bounds : 0 ≤ intOfZ index ∧ intOfZ index < 32) :
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shl value amount) index =
      if intOfZ index < intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) then false
      else CompCert4Lean.Lib.Integers.Int.testbit value
        (ZArith.BinInt.Z.sub index (CompCert4Lean.Lib.Integers.Int.unsigned amount)) := by
  rw [CompCert4Lean.Lib.Integers.Int.bits_shl_proof value amount index bounds]
  run_tac operation_unfold_bit_selector
  cases decision : CompCert4Lean.Lib.Coqlib.zlt index (CompCert4Lean.Lib.Integers.Int.unsigned amount) with
  | left below =>
      have native : intOfZ index < intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) := below
      simp only [if_pos native]
  | right above =>
      have not_below : ¬intOfZ index < intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) := by
        change intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) ≤ intOfZ index at above
        omega
      simp only [if_neg not_below]

private theorem operation_bits_shru (value amount : int) (index : Z)
    (bounds : 0 ≤ intOfZ index ∧ intOfZ index < 32) :
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shru value amount) index =
      if intOfZ index + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32
      then CompCert4Lean.Lib.Integers.Int.testbit value
        (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount)) else false := by
  rw [CompCert4Lean.Lib.Integers.Int.bits_shru_proof value amount index bounds]
  run_tac operation_unfold_bit_selector
  cases decision : CompCert4Lean.Lib.Coqlib.zlt
      (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      CompCert4Lean.Lib.Integers.Int.zwordsize with
  | left below =>
      have native : intOfZ index + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32 := by
        change intOfZ (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount)) < 32 at below
        simpa only [ZArith.BinInt.Z.add, intOfZ_zOfInt] using below
      simp only [if_pos native]
  | right above =>
      have native : ¬intOfZ index + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32 := by
        change 32 ≤ intOfZ (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount)) at above
        simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at above
        omega
      simp only [if_neg native]

private theorem operation_bits_shr (value amount : int) (index : Z)
    (bounds : 0 ≤ intOfZ index ∧ intOfZ index < 32) :
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shr value amount) index =
      if intOfZ index + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32
      then CompCert4Lean.Lib.Integers.Int.testbit value
        (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      else CompCert4Lean.Lib.Integers.Int.testbit value (ZArith.BinInt.Z.of_nat 31) := by
  rw [CompCert4Lean.Lib.Integers.Int.bits_shr_proof value amount index bounds]
  run_tac operation_unfold_bit_selector
  cases decision : CompCert4Lean.Lib.Coqlib.zlt
      (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      CompCert4Lean.Lib.Integers.Int.zwordsize with
  | left below =>
      have native : intOfZ index + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32 := by
        change intOfZ (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount)) < 32 at below
        simpa only [ZArith.BinInt.Z.add, intOfZ_zOfInt] using below
      simp only [if_pos native]
  | right above =>
      have native : ¬intOfZ index + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32 := by
        change 32 ≤ intOfZ (ZArith.BinInt.Z.add index (CompCert4Lean.Lib.Integers.Int.unsigned amount)) at above
        simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at above
        omega
      simp only [if_neg native]
      rfl

private theorem operation_uns_shl (value amount : int) (width : Z) (bits : is_uns width value) :
    is_uns (ZArith.BinInt.Z.add width (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      (CompCert4Lean.Lib.Integers.Int.shl value amount) := by
  have amountNonnegative := (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof amount).1
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) at amountNonnegative
  intro index bounds lower
  have inWord : 0 ≤ intOfZ index ∧ intOfZ index < 32 := bounds
  change intOfZ (ZArith.BinInt.Z.add width _) ≤ intOfZ index at lower
  simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt] at lower
  change CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shl value amount) index = false
  rw [operation_bits_shl value amount index inWord]
  split
  · rfl
  · apply bits
    · change 0 ≤ intOfZ (ZArith.BinInt.Z.sub index _) ∧ intOfZ (ZArith.BinInt.Z.sub index _) < 32
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega
    · change intOfZ width ≤ intOfZ (ZArith.BinInt.Z.sub index _)
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]
      omega

private theorem operation_uns_shru (value amount : int) (width : Z) (bits : is_uns width value) :
    is_uns (ZArith.BinInt.Z.sub width (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      (CompCert4Lean.Lib.Integers.Int.shru value amount) := by
  have amountNonnegative := (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof amount).1
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) at amountNonnegative
  intro index bounds lower
  have inWord : 0 ≤ intOfZ index ∧ intOfZ index < 32 := bounds
  change intOfZ (ZArith.BinInt.Z.sub width _) ≤ intOfZ index at lower
  simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt] at lower
  change CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shru value amount) index = false
  rw [operation_bits_shru value amount index inWord]
  split
  · apply bits
    · change 0 ≤ intOfZ (ZArith.BinInt.Z.add index _) ∧ intOfZ (ZArith.BinInt.Z.add index _) < 32
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
      omega
    · change intOfZ width ≤ intOfZ (ZArith.BinInt.Z.add index _)
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
      omega
  · rfl

private theorem operation_shr_sign (value amount : int) :
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shr value amount) (zOfNat 31) =
      CompCert4Lean.Lib.Integers.Int.testbit value (zOfNat 31) := by
  have amountNonnegative := (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof amount).1
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) at amountNonnegative
  rw [operation_bits_shr value amount (zOfNat 31) (by change 0 ≤ (31 : Int) ∧ (31 : Int) < 32; decide)]
  simp only [show intOfZ (zOfNat 31) = 31 from rfl]
  split
  · congr 1
    apply intOfZ_injective
    simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
    change 31 + intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) = 31
    omega
  · rfl

private theorem operation_sgn_shr (value amount : int) (width : Z) (bits : is_sgn width value) :
    is_sgn (ZArith.BinInt.Z.sub width (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      (CompCert4Lean.Lib.Integers.Int.shr value amount) := by
  have amountNonnegative := (CompCert4Lean.Lib.Integers.Int.unsigned_range_proof amount).1
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) at amountNonnegative
  intro index bounds lower
  have inWord : 0 ≤ intOfZ index ∧ intOfZ index < 32 := bounds
  change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.sub width _) (.Zpos .xH)) ≤ intOfZ index at lower
  simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, show intOfZ (.Zpos .xH : Z) = 1 from rfl] at lower
  change CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shr value amount) index =
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shr value amount) (zOfNat 31)
  rw [operation_shr_sign, operation_bits_shr value amount index inWord]
  split
  · apply bits
    · change 0 ≤ intOfZ (ZArith.BinInt.Z.add index _) ∧ intOfZ (ZArith.BinInt.Z.add index _) < 32
      simp only [ZArith.BinInt.Z.add, intOfZ_zOfInt]
      omega
    · change intOfZ (ZArith.BinInt.Z.sub width (.Zpos .xH)) ≤ intOfZ (ZArith.BinInt.Z.add index _)
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt,
        show intOfZ (.Zpos .xH : Z) = 1 from rfl]
      omega
  · rfl

private theorem operation_sgn_shl (value amount : int) (width : Z)
    (positive : 0 < intOfZ width) (bits : is_sgn width value)
    (amountSmall : CompCert4Lean.Lib.Integers.Int.ltu amount CompCert4Lean.Lib.Integers.Int.iwordsize = true) :
    is_sgn (ZArith.BinInt.Z.add width (CompCert4Lean.Lib.Integers.Int.unsigned amount))
      (CompCert4Lean.Lib.Integers.Int.shl value amount) := by
  have amountBounds := CompCert4Lean.Lib.Integers.Int.ltu_inv_proof amount
    CompCert4Lean.Lib.Integers.Int.iwordsize amountSmall
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) ∧
    intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) < 32 at amountBounds
  intro index bounds lower
  have inWord : 0 ≤ intOfZ index ∧ intOfZ index < 32 := bounds
  change intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add width _) (.Zpos .xH)) ≤ intOfZ index at lower
  simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt,
    show intOfZ (.Zpos .xH : Z) = 1 from rfl] at lower
  change CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shl value amount) index =
    CompCert4Lean.Lib.Integers.Int.testbit (CompCert4Lean.Lib.Integers.Int.shl value amount) (zOfNat 31)
  rw [operation_bits_shl value amount index inWord,
    operation_bits_shl value amount (zOfNat 31) (by change 0 ≤ (31 : Int) ∧ (31 : Int) < 32; decide)]
  rw [if_neg (show ¬ intOfZ index < intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) by omega),
    if_neg (show ¬ intOfZ (zOfNat 31) < intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned amount) by
      change ¬ (31 : Int) < _; omega)]
  apply Eq.trans (b := CompCert4Lean.Lib.Integers.Int.testbit value (zOfNat 31))
  · apply bits
    · change 0 ≤ intOfZ (ZArith.BinInt.Z.sub index _) ∧ intOfZ (ZArith.BinInt.Z.sub index _) < 32
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt]; omega
    · change intOfZ (ZArith.BinInt.Z.sub width (.Zpos .xH)) ≤ intOfZ (ZArith.BinInt.Z.sub index _)
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
        show intOfZ (.Zpos .xH : Z) = 1 from rfl]; omega
  · symm
    apply bits
    · change 0 ≤ intOfZ (ZArith.BinInt.Z.sub (zOfNat 31) _) ∧
        intOfZ (ZArith.BinInt.Z.sub (zOfNat 31) _) < 32
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt, show intOfZ (zOfNat 31) = 31 from rfl]; omega
    · change intOfZ (ZArith.BinInt.Z.sub width (.Zpos .xH)) ≤
        intOfZ (ZArith.BinInt.Z.sub (zOfNat 31) _)
      simp only [ZArith.BinInt.Z.sub, intOfZ_zOfInt,
        show intOfZ (.Zpos .xH : Z) = 1 from rfl, show intOfZ (zOfNat 31) = 31 from rfl]; omega

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_nat_div_power (quantity divisor exponent : Nat)
    (divisorPositive : 0 < divisor) (bounded : quantity < 2 ^ exponent) :
    quantity / divisor < 2 ^ (exponent - divisor.log2) := by
  apply (Nat.div_lt_iff_lt_mul divisorPositive).mpr
  have divisorBound := Nat.log2_self_le (show divisor ≠ 0 by omega)
  have powerBound : 2 ^ exponent ≤ 2 ^ (exponent - divisor.log2) * divisor := by
    calc
      2 ^ exponent ≤ 2 ^ ((exponent - divisor.log2) + divisor.log2) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ = 2 ^ (exponent - divisor.log2) * 2 ^ divisor.log2 := Nat.pow_add _ _ _
      _ ≤ 2 ^ (exponent - divisor.log2) * divisor := Nat.mul_le_mul_left _ divisorBound
  exact Nat.lt_of_lt_of_le bounded powerBound

private theorem operation_signed_ediv_power (quantity : Int) (exponent shift : Nat)
    (bounded : -(2 ^ exponent : Int) ≤ quantity ∧ quantity < 2 ^ exponent) :
    -(2 ^ (exponent - shift) : Int) ≤ quantity / 2 ^ shift ∧
      quantity / 2 ^ shift < 2 ^ (exponent - shift) := by
  have divisorPositive : (0 : Int) < 2 ^ shift := Int.pow_pos (by decide)
  have powerBound : (2 ^ exponent : Int) ≤ 2 ^ (exponent - shift) * 2 ^ shift := by
    rw [← Int.pow_add]
    exact addr32_pow_mono _ _ (by omega)
  constructor
  · apply (Int.le_ediv_iff_mul_le divisorPositive).mpr
    rw [Int.neg_mul]
    omega
  · apply (Int.ediv_lt_iff_lt_mul divisorPositive).mpr
    omega

private theorem operation_urange (classification : block_classification) (value : int) (abstract : aval)
    (matched : vmatch classification (Vint value) abstract) :
    0 ≤ intOfZ (urange abstract) ∧ is_uns (urange abstract) value := by
  cases matched <;> simp only [urange]
  all_goals first
    | exact ⟨addr32_usize_pos _, addr32_usize _⟩
    | exact ⟨by assumption, by assumption⟩
    | exact ⟨by change (0 : Int) ≤ 32; decide, operation_uns_word _⟩

private theorem operation_srange (classification : block_classification) (value : int) (abstract : aval)
    (matched : vmatch classification (Vint value) abstract) :
    0 < intOfZ (srange abstract) ∧ is_sgn (srange abstract) value := by
  cases matched <;> simp only [srange]
  all_goals first
    | exact ⟨addr32_ssize_pos _, addr32_ssize _⟩
    | exact ⟨by assumption, by assumption⟩
    | exact ⟨by apply addr32_pos_succ; assumption, by apply addr32_uns_sgn; assumption⟩
    | exact ⟨by change (0 : Int) < 32; decide, operation_sgn_word _⟩

private theorem operation_signed_range (value : int) (width : Z)
    (positive : 0 < intOfZ width) (bits : is_sgn width value) :
    -(2 ^ ((intOfZ width).toNat - 1) : Int) ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) ∧
      intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) < 2 ^ ((intOfZ width).toNat - 1) := by
  rw [condition_signed_bv]
  by_cases small : intOfZ width ≤ 32
  · exact (addr32_sgn_bits _ _ positive small).mp bits
  · have standard := (addr32_sgn_bits value (zOfNat 32)
        (by change (0 : Int) < 32; decide) (by change (32 : Int) ≤ 32; decide)).mp
        (operation_sgn_word value)
    have grown := addr32_pow_mono 31 ((intOfZ width).toNat - 1) (by omega)
    change -(2 ^ 31 : Int) ≤ (addr32_bv value).toInt ∧ (addr32_bv value).toInt < 2 ^ 31 at standard
    omega

private theorem operation_repr_uns (quantity : Int) (width : Z)
    (nonnegative : 0 ≤ quantity) (bounded : quantity < (2 ^ (intOfZ width).toNat : Int)) :
    is_uns width (CompCert4Lean.Lib.Integers.Int.repr (zOfInt quantity)) := by
  by_cases nonpositive : intOfZ width ≤ 0
  · have widthZero : (intOfZ width).toNat = 0 := by omega
    rw [widthZero] at bounded
    have quantityZero : quantity = 0 := by omega
    subst quantity
    intro index bounds lower
    exact CompCert4Lean.Lib.Integers.Int.bits_zero_proof index
  · by_cases large : 32 ≤ intOfZ width
    · exact operation_uns_mono _ (zOfNat 32) width (operation_uns_word _) large
    · have powerBound := addr32_pow_mono (intOfZ width).toNat 32 (by omega)
      have representation : CompCert4Lean.Lib.Integers.Int.unsigned
          (CompCert4Lean.Lib.Integers.Int.repr (zOfInt quantity)) = zOfInt quantity :=
        CompCert4Lean.Lib.Integers.Int.unsigned_repr_proof_api _ (by
          change 0 ≤ intOfZ (zOfInt quantity) ∧ intOfZ (zOfInt quantity) ≤ 4294967295
          rw [intOfZ_zOfInt]
          omega)
      have valueEq : ((CompCert4Lean.Lib.Integers.Int.repr (zOfInt quantity)).val : Int) = quantity := by
        rw [← condition_unsigned_val, representation, intOfZ_zOfInt]
      apply addr32_uns_of_bits _ _ (by omega)
      rw [show (2 ^ (intOfZ width).toNat : Int) = (2 ^ (intOfZ width).toNat : Nat) from
        (Int.natCast_pow 2 (intOfZ width).toNat).symm] at bounded
      omega

private theorem operation_repr_sgn_positive (quantity : Int) (width : Z)
    (positive : 0 < intOfZ width)
    (bounded : -(2 ^ (intOfZ width - 1).toNat : Int) ≤ quantity ∧
      quantity < 2 ^ (intOfZ width - 1).toNat) :
    is_sgn width (CompCert4Lean.Lib.Integers.Int.repr (zOfInt quantity)) := by
  by_cases large : 32 ≤ intOfZ width
  · exact operation_sgn_mono _ (zOfNat 32) width (operation_sgn_word _) large
  · have powerBound := addr32_pow_mono (intOfZ width - 1).toNat 31 (by omega)
    have representation : CompCert4Lean.Lib.Integers.Int.signed
        (CompCert4Lean.Lib.Integers.Int.repr (zOfInt quantity)) = zOfInt quantity :=
      CompCert4Lean.Lib.Integers.Int.signed_repr_proof _ (by
        change -2147483648 ≤ intOfZ (zOfInt quantity) ∧ intOfZ (zOfInt quantity) ≤ 2147483647
        rw [intOfZ_zOfInt]
        omega)
    apply (addr32_sgn_bits _ _ positive (by omega)).mpr
    rw [← condition_signed_bv, representation, intOfZ_zOfInt]
    have exponentEq : (intOfZ width).toNat - 1 = (intOfZ width - 1).toNat := by omega
    rw [exponentEq]
    exact bounded

private theorem operation_repr_sgn (quantity : Int) (width : Z)
    (bounded : -(2 ^ (intOfZ width - 1).toNat : Int) ≤ quantity ∧
      quantity < 2 ^ (intOfZ width - 1).toNat) :
    is_sgn width (CompCert4Lean.Lib.Integers.Int.repr (zOfInt quantity)) := by
  by_cases positive : 0 < intOfZ width
  · exact operation_repr_sgn_positive _ _ positive bounded
  · have exponentZero : (intOfZ width - 1).toNat = 0 := by omega
    rw [exponentZero] at bounded
    have oneBit := operation_repr_sgn_positive quantity (zOfNat 1)
      (by change (0 : Int) < 1; decide) bounded
    intro index inWord lower
    exact oneBit index inWord (by change (0 : Int) ≤ intOfZ index; exact inWord.1)

private theorem operation_positive_div (left right : Z) (positive : 0 < intOfZ right) :
    ZArith.BinInt.Z.div left right = zOfInt (intOfZ left / intOfZ right) := by
  unfold ZArith.BinInt.Z.div
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".ZArith.BinInt.Z.zDivEucl")
      | throwError "Missing integer Euclidean division definition"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  simp only [show intOfZ right ≠ 0 by omega, positive, if_false, if_true]
  rfl

private theorem operation_positive_mod (left right : Z) (positive : 0 < intOfZ right) :
    ZArith.BinInt.Z.modulo left right = zOfInt (intOfZ left % intOfZ right) := by
  unfold ZArith.BinInt.Z.modulo
  run_tac
    let some (declaration, _) := (← Lean.getEnv).constants.toList.find?
      (fun (declaration, _) => declaration.toString.endsWith ".ZArith.BinInt.Z.zModEucl")
      | throwError "Missing integer Euclidean remainder definition"
    Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent declaration)))
  simp only [show intOfZ right ≠ 0 by omega, positive, if_false, if_true]
  rfl

private theorem operation_unsigned_positive (value : int)
    (nonzero : value ≠ CompCert4Lean.Lib.Integers.Int.zero) : 0 < value.val := by
  by_cases positive : 0 < value.val
  · exact positive
  · apply False.elim
    apply nonzero
    apply WordCore.ext_of_val_eq
    change value.val = 0
    omega

private theorem operation_signed_nonzero (value : int)
    (nonzero : value ≠ CompCert4Lean.Lib.Integers.Int.zero) :
    intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) ≠ 0 := by
  intro zero
  apply nonzero
  rw [← CompCert4Lean.Lib.Integers.Int.repr_signed_proof value]
  change CompCert4Lean.Lib.Integers.Int.repr (CompCert4Lean.Lib.Integers.Int.signed value) =
    CompCert4Lean.Lib.Integers.Int.repr .Z0
  apply congrArg CompCert4Lean.Lib.Integers.Int.repr
  exact intOfZ_injective zero

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_psub (classification : block_classification) (base : block)
    (offset delta : ptrofs) (pointer : aptr) (matched : pmatch classification base offset pointer) :
    pmatch classification base (Ptrofs.sub offset delta) (psub pointer delta) := by
  cases matched <;> simp only [psub] <;> constructor <;> assumption

set_option maxHeartbeats 2000000 in
private theorem operation_subl (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.subl left right) (subl leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;>
    simp only [Val.subl, subl, CompCert4Lean.X86_64.Archi.ptr64, if_true,
      Bool.not_true, Bool.false_eq_true, if_false, ntop2]
  all_goals first
    | exact vmatch.long _
    | exact vmatch.numUndef _
    | exact vmatch.numLong _ _
    | exact vmatch.ptrUndef _
    | exact vmatch.ifptrUndef _
    | exact vmatch.ifptrLong _ _
    | (apply vmatch.ptr; apply operation_psub; assumption)
    | (apply vmatch.ifptrPtr; apply operation_psub; assumption)
    | (apply vmatch.ifptrPtr; apply addr64_poffset_match; assumption)
    | (apply vmatch.ifptrPtr; apply pmatch_lub_l; apply addr64_poffset_match; assumption)
    | (split <;> first | exact vmatch.ifptrLong _ _ | exact vmatch.ifptrUndef _)

set_option maxHeartbeats 2000000 in
private theorem operation_ror (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.ror left right) (ror leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.ror, ror, ntop1] <;> constructor

set_option maxHeartbeats 2000000 in
private theorem operation_shrx (classification : block_classification)
    (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.shrx left right = some result) :
    vmatch classification result (shrx leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.shrx, reduceCtorEq] at evaluated
  all_goals split at evaluated <;> simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals subst result; simp_all only [shrx, ntop1, ntop]; constructor

set_option maxHeartbeats 2000000 in
private theorem operation_shrxl (classification : block_classification)
    (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.shrxl left right = some result) :
    vmatch classification result (shrxl leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.shrxl, reduceCtorEq] at evaluated
  all_goals split at evaluated <;> simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals subst result; simp_all only [shrxl, ntop1, ntop]; constructor

private theorem operation_shift_product64 (quantity : Z) :
    ZArith.BinInt.Z.shiftr quantity (zOfNat 64) =
      ZArith.BinInt.Z.div quantity Int64.modulus := by
  exact CompCert4Lean.Lib.Zbits.Zshiftr_div_two_p quantity (zOfNat 64)
    (by change (0 : Int) ≤ 64; decide)

private theorem operation_mullhs (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mullhs left right) (mullhs leftAbstract rightAbstract) := by
  have abstractEq : mullhs leftAbstract rightAbstract = binop_long Int64.mulhs leftAbstract rightAbstract := by
    unfold mullhs
    congr 1
  rw [abstractEq]
  have matched := operation_binary_long _ Int64.mulhs _ _ _ _ leftMatch rightMatch
  cases left <;> cases right <;> exact matched

private theorem operation_mullhu (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mullhu left right) (mullhu leftAbstract rightAbstract) := by
  have abstractEq : mullhu leftAbstract rightAbstract = binop_long Int64.mulhu leftAbstract rightAbstract := by
    unfold mullhu
    congr 1
  rw [abstractEq]
  have matched := operation_binary_long _ Int64.mulhu _ _ _ _ leftMatch rightMatch
  cases left <;> cases right <;> exact matched

set_option maxHeartbeats 2000000 in
private theorem operation_modls (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.modls left right = some result) :
    vmatch classification result (modls configuration leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.modls, reduceCtorEq] at evaluated
  all_goals split at evaluated <;> simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals subst result; simp_all only [modls, ntop2]
  all_goals first
    | exact vmatch.numLong _ _
    | (change vmatch _ (Vlong (Int64.mods _ _)) (L _)
       rw [Int64.mods_divs_proof]
       constructor)

set_option maxHeartbeats 2000000 in
private theorem operation_modlu (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.modlu left right = some result) :
    vmatch classification result (modlu configuration leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.modlu, reduceCtorEq] at evaluated
  all_goals split at evaluated <;> simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals subst result; simp_all only [modlu, ntop2]
  all_goals first
    | exact vmatch.numLong _ _
    | (change vmatch _ (Vlong (Int64.modu _ _)) (L _)
       rw [Int64.modu_divu_proof _ _ (by
         intro same
         subst_vars
         have reflexive := Int64.eq_true_proof Int64.zero
         contradiction)]
       constructor)

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_native_signed_quotient_bound (quantity divisor : Int) (exponent : Nat)
    (nonzero : divisor ≠ 0)
    (bounded : -(2 ^ exponent : Int) ≤ quantity ∧ quantity < 2 ^ exponent) :
    -(2 ^ (exponent + 1 - divisor.natAbs.log2) : Int) ≤ quantity.tdiv divisor ∧
      quantity.tdiv divisor < 2 ^ (exponent + 1 - divisor.natAbs.log2) := by
  have divisor_positive : 0 < divisor.natAbs := Int.natAbs_pos.mpr nonzero
  have power_cast : (2 : Int) ^ exponent = ((2 ^ exponent : Nat) : Int) :=
    (Int.natCast_pow _ _).symm
  have quantity_abs_bound : quantity.natAbs ≤ 2 ^ exponent := by
    rw [power_cast] at bounded
    by_cases nonnegative : 0 ≤ quantity
    · have magnitude := Int.natAbs_of_nonneg nonnegative
      omega
    · have magnitude := Int.ofNat_natAbs_of_nonpos (show quantity ≤ 0 by omega)
      omega
  have quantity_abs_strict : quantity.natAbs < 2 ^ (exponent + 1) := by
    rw [Nat.pow_succ]
    have positive_power := Nat.two_pow_pos exponent
    omega
  have quotient_abs_bound : (quantity.tdiv divisor).natAbs <
      2 ^ (exponent + 1 - divisor.natAbs.log2) := by
    rw [Int.natAbs_tdiv]
    exact operation_nat_div_power quantity.natAbs divisor.natAbs (exponent + 1)
      divisor_positive quantity_abs_strict
  have quotient_upper : quantity.tdiv divisor ≤ ((quantity.tdiv divisor).natAbs : Int) := Int.le_natAbs
  have quotient_lower : -((quantity.tdiv divisor).natAbs : Int) ≤ quantity.tdiv divisor := by
    have opposite : -(quantity.tdiv divisor) ≤ ((-(quantity.tdiv divisor)).natAbs : Int) := Int.le_natAbs
    simp only [Int.natAbs_neg] at opposite
    omega
  rw [show (2 : Int) ^ (exponent + 1 - divisor.natAbs.log2) =
      ((2 ^ (exponent + 1 - divisor.natAbs.log2) : Nat) : Int) from (Int.natCast_pow _ _).symm]
  omega

private theorem operation_native_signed_remainder_bound (quantity divisor : Int) (exponent : Nat)
    (nonzero : divisor ≠ 0)
    (bounded : -(2 ^ exponent : Int) ≤ divisor ∧ divisor < 2 ^ exponent) :
    -(2 ^ exponent : Int) ≤ quantity.tmod divisor ∧ quantity.tmod divisor < 2 ^ exponent := by
  have divisor_positive : 0 < divisor.natAbs := Int.natAbs_pos.mpr nonzero
  have power_cast : (2 : Int) ^ exponent = ((2 ^ exponent : Nat) : Int) :=
    (Int.natCast_pow _ _).symm
  have divisor_abs_bound : divisor.natAbs ≤ 2 ^ exponent := by
    rw [power_cast] at bounded
    by_cases nonnegative : 0 ≤ divisor
    · have magnitude := Int.natAbs_of_nonneg nonnegative
      omega
    · have magnitude := Int.ofNat_natAbs_of_nonpos (show divisor ≤ 0 by omega)
      omega
  have remainder_abs_bound : (quantity.tmod divisor).natAbs < 2 ^ exponent := by
    rw [Int.natAbs_tmod]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ divisor_positive) divisor_abs_bound
  have remainder_upper : quantity.tmod divisor ≤ ((quantity.tmod divisor).natAbs : Int) := Int.le_natAbs
  have remainder_lower : -((quantity.tmod divisor).natAbs : Int) ≤ quantity.tmod divisor := by
    have opposite : -(quantity.tmod divisor) ≤ ((-(quantity.tmod divisor)).natAbs : Int) := Int.le_natAbs
    simp only [Int.natAbs_neg] at opposite
    omega
  rw [power_cast]
  omega

private theorem operation_support_remainder_unsigned (value : int) :
    intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned value) = (value.val : Int) := by
  change intOfZ value.intval = ((intOfZ value.intval).toNat : Int)
  have nonnegative : 0 ≤ intOfZ value.intval := by
    have invariant := value.intrange.1
    change -1 < intOfZ value.intval at invariant
    omega
  exact (Int.toNat_of_nonneg nonnegative).symm

private theorem operation_support_modu_bounds (value divisor : int) (nonzero : divisor ≠ CompCert4Lean.Lib.Integers.Int.zero) :
    is_uns (usize divisor) (CompCert4Lean.Lib.Integers.Int.modu value divisor) := by
  have positive : 0 < divisor.val := by
    by_cases present : 0 < divisor.val
    · exact present
    · exact False.elim (nonzero (WordCore.ext_of_val_eq (by change divisor.val = 0; omega)))
  have represented : CompCert4Lean.Lib.Integers.Int.unsigned
      (CompCert4Lean.Lib.Integers.Int.modu value divisor) =
      ZArith.BinInt.Z.of_nat (value.val % divisor.val) := by
    run_tac
      let some (proofName, _) := (← Lean.getEnv).constants.toList.find?
          (fun (name, _) => name.toString.endsWith ".CompCert4Lean.Common.Values.modu_pow2_unsigned_modu")
        | throwError "Checked unsigned remainder representation unavailable"
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent proofName) <;> assumption))
  have native : (CompCert4Lean.Lib.Integers.Int.modu value divisor).val = value.val % divisor.val := by
    have represented_native := congrArg intOfZ represented
    simp only [operation_support_remainder_unsigned, ZArith.BinInt.Z.of_nat, intOfZ_zOfInt,
      Int.ofNat_eq_natCast, Int.natCast_emod] at represented_native
    omega
  have size_nonnegative : 0 ≤ intOfZ (usize divisor) := usize_pos divisor
  have size_bits := is_uns_usize divisor
  have limit : divisor.val < 2 ^ (intOfZ (usize divisor)).toNat := by
    run_tac
      let some (proofName, _) := (← Lean.getEnv).constants.toList.find?
          (fun (name, _) => name.toString.endsWith ".CompCert4Lean.X86.ValueAOp.addr32_uns_bits")
        | throwError "Checked unsigned bit bound unavailable"
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent proofName) <;> assumption))
  have result_limit : (CompCert4Lean.Lib.Integers.Int.modu value divisor).val <
      2 ^ (intOfZ (usize divisor)).toNat := by
    rw [native]
    exact Nat.lt_trans (Nat.mod_lt _ positive) limit
  run_tac
    let some (proofName, _) := (← Lean.getEnv).constants.toList.find?
        (fun (name, _) => name.toString.endsWith ".CompCert4Lean.X86.ValueAOp.addr32_uns_of_bits")
      | throwError "Checked unsigned bit-bound converse unavailable"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent proofName) <;> assumption))

private theorem operation_support_modu_match (classification : block_classification) (pointer : aptr)
    (value divisor : int) (nonzero : divisor ≠ CompCert4Lean.Lib.Integers.Int.zero) :
    vmatch classification (Vint (CompCert4Lean.Lib.Integers.Int.modu value divisor))
      (uns pointer (usize divisor)) := by
  have nonnegative : 0 ≤ intOfZ (usize divisor) := usize_pos divisor
  have bits := operation_support_modu_bounds value divisor nonzero
  run_tac
    let some (proofName, _) := (← Lean.getEnv).constants.toList.find?
        (fun (name, _) => name.toString.endsWith ".CompCert4Lean.X86.ValueAOp.addr32_vmatch_uns")
      | throwError "Checked unsigned-value matching unavailable"
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent proofName) <;> assumption))

set_option maxHeartbeats 2000000 in
private theorem operation_modu (configuration : CompCert4Lean.Config.CompilerConfig)
    (classification : block_classification) (left right result : val) (left_abstract right_abstract : aval)
    (left_match : vmatch classification left left_abstract)
    (right_match : vmatch classification right right_abstract)
    (evaluated : Val.modu left right = some result) :
    vmatch classification result (modu configuration left_abstract right_abstract) := by
  cases left <;> cases right <;> simp only [Val.modu, reduceCtorEq] at evaluated
  rename_i numerator denominator
  split at evaluated
  · contradiction
  · rename_i nonzero_test
    simp only [Option.some.injEq] at evaluated
    subst result
    have nonzero : denominator ≠ CompCert4Lean.Lib.Integers.Int.zero := by
      have equality_test := CompCert4Lean.Lib.Integers.Int.eq_spec_proof denominator CompCert4Lean.Lib.Integers.Int.zero
      simpa only [nonzero_test, Bool.false_eq_true, if_false] using equality_test
    have remainder_eq := CompCert4Lean.Lib.Integers.Int.modu_divu_proof numerator denominator nonzero
    cases left_match <;> cases right_match <;> simp only [modu]
    all_goals first
      | (change vmatch classification (Vint (CompCert4Lean.Lib.Integers.Int.modu numerator denominator))
          (if CompCert4Lean.Lib.Integers.Int.eq denominator CompCert4Lean.Lib.Integers.Int.zero = true
           then _ else I (CompCert4Lean.Lib.Integers.Int.sub numerator
             (CompCert4Lean.Lib.Integers.Int.mul (CompCert4Lean.Lib.Integers.Int.divu numerator denominator) denominator)));
         simp only [nonzero_test, Bool.false_eq_true, if_false];
         rw [remainder_eq]; constructor)
      | exact operation_support_modu_match classification _ numerator denominator nonzero
      | exact vmatch.numInt _ _


set_option maxHeartbeats 2000000 in
private theorem operation_shl (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.shl left right) (shl leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.shl, shl, ntop1]
  all_goals try split
  all_goals try simp_all only [if_true, if_false]
  all_goals first
    | with_reducible exact vmatch.vmatch_i _
    | with_reducible exact vmatch.vmatch_iu _
    | with_reducible exact vmatch.iuUndef _
    | with_reducible exact vmatch.numInt _ _
    | with_reducible exact vmatch.numUndef _
    | with_reducible exact addr32_vmatch_uns_undef _ _ _
    | with_reducible exact addr32_vmatch_sgn_undef _ _ _
    | (apply operation_match_uns; apply operation_uns_shl; assumption)
    | (apply operation_match_sgn; apply operation_sgn_shl <;> assumption)

set_option maxHeartbeats 2000000 in
private theorem operation_shru (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.shru left right) (shru leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.shru, shru, ntop1]
  all_goals try split
  all_goals try simp_all only [if_true, if_false]
  all_goals first
    | with_reducible exact vmatch.vmatch_i _
    | with_reducible exact vmatch.vmatch_iu _
    | with_reducible exact vmatch.iuUndef _
    | with_reducible exact vmatch.numInt _ _
    | with_reducible exact vmatch.numUndef _
    | with_reducible exact addr32_vmatch_uns_undef _ _ _
    | skip
  all_goals apply operation_match_uns
  all_goals apply operation_uns_shru
  all_goals first | assumption | exact operation_uns_word _

set_option maxHeartbeats 2000000 in
private theorem operation_shr (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.shr left right) (shr leftAbstract rightAbstract) := by
  cases leftMatch <;> cases rightMatch <;> simp only [Val.shr, shr, ntop1]
  all_goals try split
  all_goals try simp_all only [if_true, if_false]
  all_goals first
    | with_reducible exact vmatch.vmatch_i _
    | with_reducible exact vmatch.vmatch_iu _
    | with_reducible exact vmatch.iuUndef _
    | with_reducible exact vmatch.numInt _ _
    | with_reducible exact vmatch.numUndef _
    | with_reducible exact addr32_vmatch_sgn_undef _ _ _
    | skip
  all_goals apply operation_match_sgn
  all_goals apply operation_sgn_shr
  all_goals first
    | assumption
    | (apply addr32_uns_sgn; assumption)
    | exact operation_sgn_word _

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_divu_bits (classification : block_classification)
    (value divisor : int) (abstract : aval)
    (matched : vmatch classification (Vint value) abstract)
    (nonzero : divisor ≠ CompCert4Lean.Lib.Integers.Int.zero) :
    is_uns (ZArith.BinInt.Z.sub (urange abstract)
      (ZArith.BinInt.Z.log2 (CompCert4Lean.Lib.Integers.Int.unsigned divisor)))
      (CompCert4Lean.Lib.Integers.Int.divu value divisor) := by
  obtain ⟨widthNonnegative, bits⟩ := operation_urange classification value abstract matched
  have inputBound := addr32_uns_bits value (urange abstract) widthNonnegative bits
  have positive := operation_unsigned_positive divisor nonzero
  have quotientBound := operation_nat_div_power value.val divisor.val
    (intOfZ (urange abstract)).toNat positive inputBound
  change is_uns _ (CompCert4Lean.Lib.Integers.Int.repr
    (ZArith.BinInt.Z.div (CompCert4Lean.Lib.Integers.Int.unsigned value)
      (CompCert4Lean.Lib.Integers.Int.unsigned divisor)))
  rw [operation_positive_div _ _ (by rw [condition_unsigned_val]; omega)]
  simp only [condition_unsigned_val]
  apply operation_repr_uns
  · rw [← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  · have exponentEq :
        (intOfZ (ZArith.BinInt.Z.sub (urange abstract)
          (ZArith.BinInt.Z.log2 (CompCert4Lean.Lib.Integers.Int.unsigned divisor)))).toNat =
        (intOfZ (urange abstract)).toNat - divisor.val.log2 := by
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.log2, intOfZ_zOfInt,
        condition_unsigned_val, Int.toNat_natCast, Int.ofNat_eq_natCast]
      omega
    rw [exponentEq, ← Int.natCast_ediv,
      show (2 ^ ((intOfZ (urange abstract)).toNat - divisor.val.log2) : Int) =
        (2 ^ ((intOfZ (urange abstract)).toNat - divisor.val.log2) : Nat) from
          (Int.natCast_pow _ _).symm]
    omega

private theorem operation_divs_bits (classification : block_classification)
    (value divisor : int) (abstract : aval)
    (matched : vmatch classification (Vint value) abstract)
    (nonzero : divisor ≠ CompCert4Lean.Lib.Integers.Int.zero) :
    is_sgn (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add (srange abstract) (.Zpos .xH))
      (ZArith.BinInt.Z.log2 (ZArith.BinInt.Z.abs (CompCert4Lean.Lib.Integers.Int.signed divisor))))
      (CompCert4Lean.Lib.Integers.Int.divs value divisor) := by
  obtain ⟨widthPositive, bits⟩ := operation_srange classification value abstract matched
  have inputBound := operation_signed_range value (srange abstract) widthPositive bits
  have quotientBound := operation_native_signed_quotient_bound
    (intOfZ (CompCert4Lean.Lib.Integers.Int.signed value))
    (intOfZ (CompCert4Lean.Lib.Integers.Int.signed divisor))
    ((intOfZ (srange abstract)).toNat - 1) (operation_signed_nonzero divisor nonzero) inputBound
  change is_sgn _ (CompCert4Lean.Lib.Integers.Int.repr (zOfInt
    ((intOfZ (CompCert4Lean.Lib.Integers.Int.signed value)).tdiv
      (intOfZ (CompCert4Lean.Lib.Integers.Int.signed divisor)))))
  apply operation_repr_sgn
  have exponentEq :
      (intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add (srange abstract) (.Zpos .xH))
        (ZArith.BinInt.Z.log2 (ZArith.BinInt.Z.abs (CompCert4Lean.Lib.Integers.Int.signed divisor)))) - 1).toNat =
      ((intOfZ (srange abstract)).toNat - 1 + 1 -
        (intOfZ (CompCert4Lean.Lib.Integers.Int.signed divisor)).natAbs.log2) := by
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, ZArith.BinInt.Z.log2,
      ZArith.BinInt.Z.abs, intOfZ_zOfInt, Int.toNat_natCast,
      Int.ofNat_eq_natCast, show intOfZ (.Zpos .xH : Z) = 1 from rfl]
    omega
  rw [exponentEq]
  exact quotientBound

private theorem operation_mods_bits (value divisor : int)
    (nonzero : divisor ≠ CompCert4Lean.Lib.Integers.Int.zero) :
    is_sgn (ssize divisor) (CompCert4Lean.Lib.Integers.Int.mods value divisor) := by
  have divisorBound := operation_signed_range divisor (ssize divisor)
    (addr32_ssize_pos divisor) (addr32_ssize divisor)
  have remainderBound := operation_native_signed_remainder_bound
    (intOfZ (CompCert4Lean.Lib.Integers.Int.signed value))
    (intOfZ (CompCert4Lean.Lib.Integers.Int.signed divisor))
    ((intOfZ (ssize divisor)).toNat - 1) (operation_signed_nonzero divisor nonzero) divisorBound
  change is_sgn _ (CompCert4Lean.Lib.Integers.Int.repr
    (ZArith.BinInt.Z.sub (CompCert4Lean.Lib.Integers.Int.signed value)
      (ZArith.BinInt.Z.mul
        (ZArith.BinInt.Z.quot (CompCert4Lean.Lib.Integers.Int.signed value)
          (CompCert4Lean.Lib.Integers.Int.signed divisor))
        (CompCert4Lean.Lib.Integers.Int.signed divisor))))
  simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.mul, ZArith.BinInt.Z.quot, intOfZ_zOfInt]
  rw [Int.mul_comm, ← Int.tmod_def]
  apply operation_repr_sgn
  have exponentEq : (intOfZ (ssize divisor) - 1).toNat = (intOfZ (ssize divisor)).toNat - 1 := by omega
  rw [exponentEq]
  exact remainderBound

set_option maxHeartbeats 1000000 in
private theorem operation_divu (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.divu left right = some result) :
    vmatch classification result (divu configuration leftAbstract rightAbstract) := by
  cases left <;> cases right <;> simp only [Val.divu, reduceCtorEq] at evaluated
  rename_i numerator denominator
  split at evaluated
  · contradiction
  · rename_i nonzeroTest
    simp only [Option.some.injEq] at evaluated
    subst result
    have nonzero : denominator ≠ CompCert4Lean.Lib.Integers.Int.zero := by
      have equalityTest := CompCert4Lean.Lib.Integers.Int.eq_spec_proof denominator CompCert4Lean.Lib.Integers.Int.zero
      simpa only [nonzeroTest, Bool.false_eq_true, if_false] using equalityTest
    have bits := operation_divu_bits classification numerator denominator leftAbstract leftMatch nonzero
    cases leftMatch <;> cases rightMatch <;> simp only [divu, ntop2]
    all_goals first
      | (split; contradiction; constructor)
      | (split; contradiction; exact operation_match_uns _ _ _ _ bits)
      | exact vmatch.numInt _ _

set_option maxHeartbeats 1000000 in
private theorem operation_divs (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.divs left right = some result) :
    vmatch classification result (divs configuration leftAbstract rightAbstract) := by
  cases left <;> cases right <;> simp only [Val.divs, reduceCtorEq] at evaluated
  rename_i numerator denominator
  split at evaluated
  · contradiction
  · rename_i validTest
    simp only [Option.some.injEq] at evaluated
    subst result
    have nonzeroTest : CompCert4Lean.Lib.Integers.Int.eq denominator CompCert4Lean.Lib.Integers.Int.zero = false := by
      have condition := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr validTest)
      exact condition.1
    have nonzero : denominator ≠ CompCert4Lean.Lib.Integers.Int.zero := by
      have equalityTest := CompCert4Lean.Lib.Integers.Int.eq_spec_proof denominator CompCert4Lean.Lib.Integers.Int.zero
      simpa only [nonzeroTest, Bool.false_eq_true, if_false] using equalityTest
    have bits := operation_divs_bits classification numerator denominator leftAbstract leftMatch nonzero
    have noOverflow :
        (CompCert4Lean.Lib.Integers.Int.eq numerator
          (CompCert4Lean.Lib.Integers.Int.repr CompCert4Lean.Lib.Integers.Int.min_signed) &&
          CompCert4Lean.Lib.Integers.Int.eq denominator CompCert4Lean.Lib.Integers.Int.mone) = false :=
      (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr validTest)).2
    cases leftMatch <;> cases rightMatch <;>
      simp only [divs, ntop2, nonzeroTest, noOverflow, Bool.false_or, Bool.false_eq_true, if_false]
    all_goals first
      | exact vmatch.vmatch_i _
      | exact operation_match_sgn _ _ _ _ bits
      | exact vmatch.numInt _ _

set_option maxHeartbeats 2000000
private theorem operation_mods (configuration : CompilerConfig)
    (classification : block_classification) (left right result : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract)
    (evaluated : Val.mods left right = some result) :
    vmatch classification result (mods configuration leftAbstract rightAbstract) := by
  cases left <;> cases right <;> simp only [Val.mods, reduceCtorEq] at evaluated
  rename_i numerator denominator
  split at evaluated
  · contradiction
  · rename_i validTest
    simp only [Option.some.injEq] at evaluated
    subst result
    have nonzeroTest : CompCert4Lean.Lib.Integers.Int.eq denominator CompCert4Lean.Lib.Integers.Int.zero = false := by
      have condition := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr validTest)
      exact condition.1
    have nonzero : denominator ≠ CompCert4Lean.Lib.Integers.Int.zero := by
      have equalityTest := CompCert4Lean.Lib.Integers.Int.eq_spec_proof denominator CompCert4Lean.Lib.Integers.Int.zero
      simpa only [nonzeroTest, Bool.false_eq_true, if_false] using equalityTest
    have noOverflow :
        (CompCert4Lean.Lib.Integers.Int.eq numerator
          (CompCert4Lean.Lib.Integers.Int.repr CompCert4Lean.Lib.Integers.Int.min_signed) &&
          CompCert4Lean.Lib.Integers.Int.eq denominator CompCert4Lean.Lib.Integers.Int.mone) = false :=
      (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr validTest)).2
    cases leftMatch <;> cases rightMatch
    all_goals delta CompCert4Lean.Backend.ValueDomain.mods
    all_goals dsimp only
    all_goals try simp only [ntop2, nonzeroTest, noOverflow, Bool.false_or, Bool.false_eq_true, if_false]
    all_goals first
      | with_reducible exact vmatch.numInt _ _
      | with_reducible exact operation_match_sgn _ _ _ _ (operation_mods_bits numerator denominator nonzero)
      | skip
    all_goals
      change vmatch _ (Vint (CompCert4Lean.Lib.Integers.Int.mods numerator denominator))
           (I (CompCert4Lean.Lib.Integers.Int.sub numerator
             (CompCert4Lean.Lib.Integers.Int.mul (CompCert4Lean.Lib.Integers.Int.divs numerator denominator) denominator)))
      rw [CompCert4Lean.Lib.Integers.Int.mods_divs_proof numerator denominator]
      constructor

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_native_unsigned_high_product_bound (left right left_exponent right_exponent shift : Nat)
    (left_bound : left < 2 ^ left_exponent) (right_bound : right < 2 ^ right_exponent) :
    left * right / 2 ^ shift < 2 ^ (left_exponent + right_exponent - shift) := by
  have product_bound : left * right < 2 ^ (left_exponent + right_exponent) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt left_bound right_bound
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).mpr
  have exponent_bound : left_exponent + right_exponent ≤
      (left_exponent + right_exponent - shift) + shift := by omega
  have bound := Nat.pow_le_pow_right (show 0 < 2 by decide) exponent_bound
  rw [Nat.pow_add 2 (left_exponent + right_exponent - shift) shift] at bound
  exact Nat.lt_of_lt_of_le product_bound bound

private theorem operation_native_signed_high_product_bound (left right : Int) (left_exponent right_exponent shift : Nat)
    (left_bound : -(2 ^ left_exponent : Int) ≤ left ∧ left < 2 ^ left_exponent)
    (right_bound : -(2 ^ right_exponent : Int) ≤ right ∧ right < 2 ^ right_exponent) :
    -(2 ^ (left_exponent + right_exponent + 1 - shift) : Int) ≤ left * right / 2 ^ shift ∧
      left * right / 2 ^ shift < 2 ^ (left_exponent + right_exponent + 1 - shift) := by
  have magnitude_bound : ∀ (value : Int) (exponent : Nat),
      -(2 ^ exponent : Int) ≤ value ∧ value < 2 ^ exponent → value.natAbs ≤ 2 ^ exponent := by
    intro value exponent bounded
    rw [show (2 : Int) ^ exponent = ((2 ^ exponent : Nat) : Int) from (Int.natCast_pow _ _).symm] at bounded
    by_cases nonnegative : 0 ≤ value
    · have magnitude := Int.natAbs_of_nonneg nonnegative
      omega
    · have magnitude := Int.ofNat_natAbs_of_nonpos (show value ≤ 0 by omega)
      omega
  have product_magnitude : (left * right).natAbs ≤ 2 ^ (left_exponent + right_exponent) := by
    rw [Int.natAbs_mul, Nat.pow_add]
    exact Nat.mul_le_mul (magnitude_bound left left_exponent left_bound)
      (magnitude_bound right right_exponent right_bound)
  have product_strict : (left * right).natAbs < 2 ^ (left_exponent + right_exponent + 1) := by
    rw [Nat.pow_succ]
    have positive := Nat.two_pow_pos (left_exponent + right_exponent)
    omega
  apply operation_signed_ediv_power (left * right) (left_exponent + right_exponent + 1) shift
  rw [show (2 : Int) ^ (left_exponent + right_exponent + 1) =
      ((2 ^ (left_exponent + right_exponent + 1) : Nat) : Int) from (Int.natCast_pow _ _).symm]
  have upper : left * right ≤ ((left * right).natAbs : Int) := Int.le_natAbs
  have lower : -(left * right) ≤ ((-(left * right)).natAbs : Int) := Int.le_natAbs
  simp only [Int.natAbs_neg] at lower
  omega


private theorem operation_mulhs_repr (left right : int) :
    CompCert4Lean.Lib.Integers.Int.mulhs left right =
      CompCert4Lean.Lib.Integers.Int.repr (zOfInt
        (intOfZ (CompCert4Lean.Lib.Integers.Int.signed left) *
          intOfZ (CompCert4Lean.Lib.Integers.Int.signed right) / 2 ^ 32)) := by
  change CompCert4Lean.Lib.Integers.Int.repr
    (ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.mul (CompCert4Lean.Lib.Integers.Int.signed left)
        (CompCert4Lean.Lib.Integers.Int.signed right)) CompCert4Lean.Lib.Integers.Int.modulus) = _
  rw [operation_positive_div _ _ (by change (0 : Int) < 4294967296; decide)]
  simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt]
  rfl

private theorem operation_mulhu_repr (left right : int) :
    CompCert4Lean.Lib.Integers.Int.mulhu left right =
      CompCert4Lean.Lib.Integers.Int.repr (zOfInt ((left.val * right.val / 2 ^ 32 : Nat) : Int)) := by
  change CompCert4Lean.Lib.Integers.Int.repr
    (ZArith.BinInt.Z.div
      (ZArith.BinInt.Z.mul (CompCert4Lean.Lib.Integers.Int.unsigned left)
        (CompCert4Lean.Lib.Integers.Int.unsigned right)) CompCert4Lean.Lib.Integers.Int.modulus) = _
  rw [operation_positive_div _ _ (by change (0 : Int) < 4294967296; decide)]
  simp only [ZArith.BinInt.Z.mul, intOfZ_zOfInt, condition_unsigned_val]
  rfl

private theorem operation_mulhs_bits (left right : int) (leftWidth rightWidth : Z)
    (leftPositive : 0 < intOfZ leftWidth) (rightPositive : 0 < intOfZ rightWidth)
    (leftBits : is_sgn leftWidth left) (rightBits : is_sgn rightWidth right) :
    is_sgn (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add leftWidth rightWidth) (zOfNat 32))
      (CompCert4Lean.Lib.Integers.Int.mulhs left right) := by
  have leftBound := operation_signed_range left leftWidth leftPositive leftBits
  have rightBound := operation_signed_range right rightWidth rightPositive rightBits
  have productBound := operation_native_signed_high_product_bound
    (intOfZ (CompCert4Lean.Lib.Integers.Int.signed left))
    (intOfZ (CompCert4Lean.Lib.Integers.Int.signed right))
    ((intOfZ leftWidth).toNat - 1) ((intOfZ rightWidth).toNat - 1) 32 leftBound rightBound
  rw [operation_mulhs_repr]
  apply operation_repr_sgn
  have exponentEq :
      (intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add leftWidth rightWidth) (zOfNat 32)) - 1).toNat =
      (intOfZ leftWidth).toNat - 1 + ((intOfZ rightWidth).toNat - 1) + 1 - 32 := by
    simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt,
      show intOfZ (zOfNat 32) = 32 from rfl]
    omega
  rw [exponentEq]
  exact productBound

private theorem operation_mulhu_bits (left right : int) (leftWidth rightWidth : Z)
    (leftNonnegative : 0 ≤ intOfZ leftWidth) (rightNonnegative : 0 ≤ intOfZ rightWidth)
    (leftBits : is_uns leftWidth left) (rightBits : is_uns rightWidth right) :
    is_uns (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add leftWidth rightWidth) (zOfNat 32))
      (CompCert4Lean.Lib.Integers.Int.mulhu left right) := by
  have leftBound := addr32_uns_bits left leftWidth leftNonnegative leftBits
  have rightBound := addr32_uns_bits right rightWidth rightNonnegative rightBits
  have productBound := operation_native_unsigned_high_product_bound left.val right.val
    (intOfZ leftWidth).toNat (intOfZ rightWidth).toNat 32 leftBound rightBound
  rw [operation_mulhu_repr]
  apply operation_repr_uns
  · exact Int.natCast_nonneg _
  · have exponentEq :
        (intOfZ (ZArith.BinInt.Z.sub (ZArith.BinInt.Z.add leftWidth rightWidth) (zOfNat 32))).toNat =
        (intOfZ leftWidth).toNat + (intOfZ rightWidth).toNat - 32 := by
      simp only [ZArith.BinInt.Z.sub, ZArith.BinInt.Z.add, intOfZ_zOfInt,
        show intOfZ (zOfNat 32) = 32 from rfl]
      omega
    rw [exponentEq, show (2 ^ ((intOfZ leftWidth).toNat + (intOfZ rightWidth).toNat - 32) : Int) =
      (2 ^ ((intOfZ leftWidth).toNat + (intOfZ rightWidth).toNat - 32) : Nat) from
        (Int.natCast_pow _ _).symm]
    exact Int.ofNat_lt.mpr productBound

private theorem operation_mulhs_base (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mulhs left right) (mulhs_base leftAbstract rightAbstract) := by
  cases left <;> cases right <;> simp only [Val.mulhs, mulhs_base]
  all_goals try exact addr32_vmatch_sgn_undef _ _ _
  rename_i numerator multiplier
  obtain ⟨leftPositive, leftBits⟩ := operation_srange classification numerator leftAbstract leftMatch
  obtain ⟨rightPositive, rightBits⟩ := operation_srange classification multiplier rightAbstract rightMatch
  apply operation_match_sgn
  exact operation_mulhs_bits _ _ _ _ leftPositive rightPositive leftBits rightBits

private theorem operation_mulhu_base (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mulhu left right) (mulhu_base leftAbstract rightAbstract) := by
  cases left <;> cases right <;> simp only [Val.mulhu, mulhu_base]
  all_goals try exact addr32_vmatch_uns_undef _ _ _
  rename_i numerator multiplier
  obtain ⟨leftNonnegative, leftBits⟩ := operation_urange classification numerator leftAbstract leftMatch
  obtain ⟨rightNonnegative, rightBits⟩ := operation_urange classification multiplier rightAbstract rightMatch
  apply operation_match_uns
  exact operation_mulhu_bits _ _ _ _ leftNonnegative rightNonnegative leftBits rightBits

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib

private theorem operation_mulhs_zero (value : int) :
    CompCert4Lean.Lib.Integers.Int.mulhs CompCert4Lean.Lib.Integers.Int.zero value =
      CompCert4Lean.Lib.Integers.Int.zero := by
  rw [operation_mulhs_repr]
  change CompCert4Lean.Lib.Integers.Int.repr
    (zOfInt (0 * intOfZ (CompCert4Lean.Lib.Integers.Int.signed value) / 2 ^ 32)) = _
  simp only [Int.zero_mul, Int.zero_ediv]
  rfl

private theorem operation_mulhu_small (left right : int) (small : left.val ≤ 1) :
    CompCert4Lean.Lib.Integers.Int.mulhu left right = CompCert4Lean.Lib.Integers.Int.zero := by
  have rightBound := CompCert4Lean.Lib.Integers.Int.unsigned_range_proof right
  change 0 ≤ intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned right) ∧
    intOfZ (CompCert4Lean.Lib.Integers.Int.unsigned right) < 4294967296 at rightBound
  rw [condition_unsigned_val] at rightBound
  have productLe := Nat.mul_le_mul_right right.val small
  have productBound : left.val * right.val < 2 ^ 32 := by
    simp only [Nat.one_mul] at productLe
    omega
  rw [operation_mulhu_repr, Nat.div_eq_of_lt productBound]
  rfl

private theorem operation_val_mulhs_comm (left right : val) :
    Val.mulhs left right = Val.mulhs right left := by
  cases left <;> cases right <;> try rfl
  change Vint (CompCert4Lean.Lib.Integers.Int.mulhs _ _) = Vint (CompCert4Lean.Lib.Integers.Int.mulhs _ _)
  simp only [operation_mulhs_repr, Int.mul_comm]

private theorem operation_val_mulhu_comm (left right : val) :
    Val.mulhu left right = Val.mulhu right left := by
  cases left <;> cases right <;> try rfl
  change Vint (CompCert4Lean.Lib.Integers.Int.mulhu _ _) = Vint (CompCert4Lean.Lib.Integers.Int.mulhu _ _)
  simp only [operation_mulhu_repr, Nat.mul_comm]

private theorem operation_mulhs_zero_left (classification : block_classification) (left right : val)
    (zero : left = Vundef ∨ left = Vint CompCert4Lean.Lib.Integers.Int.zero) :
    vmatch classification (Val.mulhs left right) (IU CompCert4Lean.Lib.Integers.Int.zero) := by
  rcases zero with zero | zero
  · subst left
    cases right <;> exact vmatch.iuUndef _
  · subst left
    cases right <;> try exact vmatch.iuUndef _
    change vmatch _ (Vint (CompCert4Lean.Lib.Integers.Int.mulhs CompCert4Lean.Lib.Integers.Int.zero _)) _
    rw [operation_mulhs_zero]
    constructor

private theorem operation_mulhu_zero_left (classification : block_classification) (left right : val)
    (small : left = Vundef ∨ left = Vint CompCert4Lean.Lib.Integers.Int.zero ∨
      left = Vint CompCert4Lean.Lib.Integers.Int.one) :
    vmatch classification (Val.mulhu left right) (IU CompCert4Lean.Lib.Integers.Int.zero) := by
  cases left <;> cases right <;> try exact vmatch.iuUndef _
  rename_i first second
  have smallValue : first.val ≤ 1 := by
    rcases small with impossible | zero | one
    · cases impossible
    · cases zero
      decide
    · cases one
      decide
  change vmatch _ (Vint (CompCert4Lean.Lib.Integers.Int.mulhu first second)) _
  rw [operation_mulhu_small first second smallValue]
  constructor

set_option maxHeartbeats 1000000 in
private theorem operation_mulhs (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mulhs left right) (mulhs leftAbstract rightAbstract) := by
  have zeroCase : (vincl leftAbstract (Uns Ptop .Z0) || vincl rightAbstract (Uns Ptop .Z0)) = true →
      vmatch classification (Val.mulhs left right) (IU CompCert4Lean.Lib.Integers.Int.zero) := by
    intro condition
    rcases Bool.or_eq_true_iff.mp condition with leftZero | rightZero
    · exact operation_mulhs_zero_left _ _ _
        (addr32_vincl_zero classification left leftAbstract leftMatch leftZero)
    · rw [operation_val_mulhs_comm]
      exact operation_mulhs_zero_left _ _ _
        (addr32_vincl_zero classification right rightAbstract rightMatch rightZero)
  have base := operation_mulhs_base classification left right leftAbstract rightAbstract leftMatch rightMatch
  cases leftAbstract <;> cases rightAbstract <;> simp only [mulhs]
  all_goals first
    | (split; apply zeroCase; assumption; exact base)
    | (cases leftMatch <;> cases rightMatch <;> constructor)

set_option maxHeartbeats 1000000 in
private theorem operation_mulhu (classification : block_classification)
    (left right : val) (leftAbstract rightAbstract : aval)
    (leftMatch : vmatch classification left leftAbstract)
    (rightMatch : vmatch classification right rightAbstract) :
    vmatch classification (Val.mulhu left right) (mulhu leftAbstract rightAbstract) := by
  have zeroCase : (vincl leftAbstract (Uns Ptop (.Zpos .xH)) ||
      vincl rightAbstract (Uns Ptop (.Zpos .xH))) = true →
      vmatch classification (Val.mulhu left right) (IU CompCert4Lean.Lib.Integers.Int.zero) := by
    intro condition
    rcases Bool.or_eq_true_iff.mp condition with leftSmall | rightSmall
    · exact operation_mulhu_zero_left _ _ _ (vmatch_Uns_1 classification Ptop left
        (vmatch_ge classification left _ _ (vincl_ge _ _ leftSmall) leftMatch))
    · rw [operation_val_mulhu_comm]
      exact operation_mulhu_zero_left _ _ _ (vmatch_Uns_1 classification Ptop right
        (vmatch_ge classification right _ _ (vincl_ge _ _ rightSmall) rightMatch))
  have base := operation_mulhu_base classification left right leftAbstract rightAbstract leftMatch rightMatch
  cases leftAbstract <;> cases rightAbstract <;> simp only [mulhu]
  all_goals first
    | (split; apply zeroCase; assumption; exact base)
    | (cases leftMatch <;> cases rightMatch <;> constructor)

end CompCert4Lean.X86.ValueAOp

namespace CompCert4Lean.X86.ValueAOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.X86.Op

set_option maxHeartbeats 4000000
theorem eval_static_operation_sound
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)] :
    eval_static_operation_soundStatement := by
  intro configuration classification environment environmentMatch stack stackMatch
    operator values memory result abstracts evaluated matched
  cases operator
  case Olea address =>
    exact eval_static_addressing_32_sound classification environment environmentMatch stack stackMatch
      address values result abstracts evaluated matched
  case Oleal address =>
    exact eval_static_addressing_64_sound classification environment environmentMatch stack stackMatch
      address values result abstracts evaluated matched
  case Ocmp condition =>
    have conditionMatched := eval_static_condition_sound configuration classification condition values memory abstracts matched
    cases matched
    all_goals try cases ‹list_forall2 (vmatch classification) _ _›
    all_goals try cases ‹list_forall2 (vmatch classification) _ _›
    all_goals delta CompCert4Lean.X86.Op.eval_operation at evaluated
    all_goals dsimp only at evaluated
    all_goals simp only [Option.some.injEq] at evaluated
    all_goals subst result
    all_goals delta eval_static_operation
    all_goals dsimp only
    all_goals exact of_optbool_sound classification _ _ conditionMatched
  case Osel condition type =>
    cases matched with
    | nil => cases evaluated
    | cons firstValue firstAbstract firstMatch restMatch =>
        cases restMatch with
        | nil => cases evaluated
        | cons secondValue secondAbstract secondMatch tailMatch =>
            have conditionMatched := eval_static_condition_sound configuration classification condition _ memory _ tailMatch
            cases tailMatch
            all_goals delta CompCert4Lean.X86.Op.eval_operation at evaluated
            all_goals dsimp only at evaluated
            all_goals simp only [Option.some.injEq] at evaluated
            all_goals subst result
            all_goals delta eval_static_operation
            all_goals dsimp only
            all_goals
              exact select_sound configuration classification _ _ _ _ _ _ type
                conditionMatched firstMatch secondMatch
  all_goals cases matched
  all_goals try cases ‹list_forall2 (vmatch classification) _ _›
  all_goals try cases ‹list_forall2 (vmatch classification) _ _›
  all_goals delta CompCert4Lean.X86.Op.eval_operation at evaluated
  all_goals dsimp only at evaluated
  all_goals try simp only [reduceCtorEq, Option.some.injEq] at evaluated
  all_goals try subst result
  all_goals delta eval_static_operation
  all_goals dsimp only
  all_goals first
    | assumption
    | with_reducible exact vmatch.vmatch_i _
    | with_reducible exact vmatch.long _
    | (with_reducible apply operation_zero_ext
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_sign_ext
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_neg
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_sub
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_mul
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_mulhs
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_mulhu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_divs
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_divu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_mods
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_modu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_and
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_or
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_xor
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_not
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_shl
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_shr
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_shru
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_shrx
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_ror
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_longofwords
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_loword
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_hiword
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_longofint
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_longofintu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply addr64_add_match
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_subl
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_mullhs
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_mullhu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_divls
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_divlu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_modls
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_modlu
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_shrxl
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_singleoffloat
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_floatofsingle
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_intoffloat
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_floatofint
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_intofsingle
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_singleofint
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_longoffloat
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_floatoflong
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_longofsingle
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_singleoflong
       all_goals first | assumption | with_reducible exact vmatch.vmatch_i _ | with_reducible exact vmatch.long _ | decide)
    | (with_reducible apply operation_or
       · apply operation_shl <;> first | assumption | constructor
       · apply operation_shru <;> first | assumption | constructor)
    | skip
  case Ofloatconst.nil =>
    split <;> constructor
  case Osingleconst.nil =>
    split <;> constructor
  case Oindirectsymbol.nil =>
    exact symbol_address_sound_2 classification environment environmentMatch _ _
  all_goals try simp only [negl, Val.negl, notl, Val.notl, mull, Val.mull,
    andl, Val.andl, orl, Val.orl, xorl, Val.xorl,
    shll, Val.shll, shrl, Val.shrl, shrlu, Val.shrlu, rorl, Val.rorl,
    negf, Val.negf, absf, Val.absf, negfs, Val.negfs, absfs, Val.absfs,
    addf, Val.addf, subf, Val.subf, mulf, Val.mulf, divf, Val.divf,
    addfs, Val.addfs, subfs, Val.subfs, mulfs, Val.mulfs, divfs, Val.divfs,
    maxf, minf]
  all_goals first
    | (apply operation_unary_long; assumption)
    | (apply operation_binary_long <;> first | assumption | constructor)
    | (apply operation_unary_float; assumption)
    | (apply operation_unary_single; assumption)
    | (apply operation_binary_single <;> assumption)
    | (apply binop_float_sound <;> assumption)
    | (apply operation_shift_long <;> first | assumption | constructor)
    | (apply operation_rotate_long <;> first | assumption | constructor)

end CompCert4Lean.X86.ValueAOp
