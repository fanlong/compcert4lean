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
