import CompCert4Lean.Backend.NeedDomain
import CompCert4Lean.X86.Op

/-!
# x86 neededness analysis

Definition-bearing translation of CompCert's `x86/NeedOp.v`.  The five
soundness declarations are retained as exact proposition descriptors for a
later proof-migration phase.
-/

namespace CompCert4Lean.X86.NeedOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.NeedDomain
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op

private abbrev int := CompCert4Lean.Lib.Integers.int
private abbrev int64 := CompCert4Lean.Lib.Integers.int64
private abbrev ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev block := CompCert4Lean.Common.Values.block
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev nval := CompCert4Lean.Backend.NeedDomain.nval
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate

def op1 (nv : nval) : List nval := [nv]

def op2 (nv : nval) : List nval := [nv, nv]

def needs_of_condition (cond : condition) : List nval :=
  match cond with
  | .Cmaskzero n | .Cmasknotzero n => op1 (maskzero n)
  | _ => []

def needs_of_addressing (addr : addressing) (nv : nval) : List nval :=
  match addr with
  | .Aindexed _ => op1 (modarith nv)
  | .Aindexed2 _ => op2 (modarith nv)
  | .Ascaled _ _ => op1 (modarith (modarith nv))
  | .Aindexed2scaled _ _ => op2 (modarith nv)
  | .Aglobal _ _ => []
  | .Abased _ _ => op1 (modarith nv)
  | .Abasedscaled _ _ _ => op1 (modarith (modarith nv))
  | .Ainstack _ => []

def needs_of_operation (op : operation) (nv : nval) : List nval :=
  match op with
  | .Omove => op1 nv
  | .Ointconst _ | .Olongconst _ | .Ofloatconst _ | .Osingleconst _
  | .Oindirectsymbol _ => []
  | .Ocast8signed => op1 (sign_ext (ZArith.BinInt.Z.of_nat 8) nv)
  | .Ocast8unsigned => op1 (zero_ext (ZArith.BinInt.Z.of_nat 8) nv)
  | .Ocast16signed => op1 (sign_ext (ZArith.BinInt.Z.of_nat 16) nv)
  | .Ocast16unsigned => op1 (zero_ext (ZArith.BinInt.Z.of_nat 16) nv)
  | .Oneg => op1 (modarith nv)
  | .Osub => op2 (default nv)
  | .Omul => op2 (modarith nv)
  | .Omulimm _ => op1 (modarith nv)
  | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu => op2 (default nv)
  | .Oand => op2 (bitwise nv)
  | .Oandimm n => op1 (andimm nv n)
  | .Oor => op2 (bitwise nv)
  | .Oorimm n => op1 (orimm nv n)
  | .Oxor => op2 (bitwise nv)
  | .Oxorimm _ => op1 (bitwise nv)
  | .Onot => op1 (bitwise nv)
  | .Oshl => op2 (default nv)
  | .Oshlimm n => op1 (shlimm nv n)
  | .Oshr => op2 (default nv)
  | .Oshrimm n => op1 (shrimm nv n)
  | .Oshrximm _ => op1 (default nv)
  | .Oshru => op2 (default nv)
  | .Oshruimm n => op1 (shruimm nv n)
  | .Ororimm n => op1 (ror nv n)
  | .Oshldimm _ => op1 (default nv)
  | .Olea addr => needs_of_addressing addr nv
  | .Omakelong => [makelong_hi nv, makelong_lo nv]
  | .Olowlong => op1 (loword nv)
  | .Ohighlong => op1 (hiword nv)
  | .Ocast32signed => op1 (longofint nv)
  | .Ocast32unsigned => op1 (longofintu nv)
  | .Onegl => op1 (modarith nv)
  | .Oaddlimm _ => op1 (modarith nv)
  | .Osubl => op2 (default nv)
  | .Omull => op2 (modarith nv)
  | .Omullimm _ => op1 (modarith nv)
  | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl | .Omodlu =>
      op2 (default nv)
  | .Oandl => op2 (bitwise nv)
  | .Oandlimm n => op1 (andlimm nv n)
  | .Oorl => op2 (bitwise nv)
  | .Oorlimm n => op1 (orlimm nv n)
  | .Oxorl => op2 (bitwise nv)
  | .Oxorlimm _ => op1 (bitwise nv)
  | .Onotl => op1 (bitwise nv)
  | .Oshll => op2 (default nv)
  | .Oshllimm n => op1 (shllimm nv n)
  | .Oshrl => op2 (default nv)
  | .Oshrlimm n => op1 (shrlimm nv n)
  | .Oshrxlimm _ => op1 (default nv)
  | .Oshrlu => op2 (default nv)
  | .Oshrluimm n => op1 (shrluimm nv n)
  | .Ororlimm n => op1 (rorl nv n)
  | .Oleal addr => needs_of_addressing addr nv
  | .Onegf | .Oabsf => op1 (default nv)
  | .Oaddf | .Osubf | .Omulf | .Odivf | .Omaxf | .Ominf => op2 (default nv)
  | .Onegfs | .Oabsfs => op1 (default nv)
  | .Oaddfs | .Osubfs | .Omulfs | .Odivfs => op2 (default nv)
  | .Osingleoffloat | .Ofloatofsingle => op1 (default nv)
  | .Ointoffloat | .Ofloatofint | .Ointofsingle | .Osingleofint =>
      op1 (default nv)
  | .Olongoffloat | .Ofloatoflong | .Olongofsingle | .Osingleoflong =>
      op1 (default nv)
  | .Ocmp c => needs_of_condition c
  | .Osel c _ => nv :: nv :: needs_of_condition c

def operation_is_redundant (op : operation) (nv : nval) : Bool :=
  match op with
  | .Ocast8signed => sign_ext_redundant (ZArith.BinInt.Z.of_nat 8) nv
  | .Ocast8unsigned => zero_ext_redundant (ZArith.BinInt.Z.of_nat 8) nv
  | .Ocast16signed => sign_ext_redundant (ZArith.BinInt.Z.of_nat 16) nv
  | .Ocast16unsigned => zero_ext_redundant (ZArith.BinInt.Z.of_nat 16) nv
  | .Oandimm n => andimm_redundant nv n
  | .Oorimm n => orimm_redundant nv n
  | .Oandlimm n => andlimm_redundant nv n
  | .Oorlimm n => orlimm_redundant nv n
  | _ => false

def needs_of_condition_soundStatement : Prop :=
  ∀ (m m' : mem),
    (∀ b ofs k p, Mem.perm m b ofs k p → Mem.perm m' b ofs k p) →
    ∀ (cond : condition) (args : List val) (b : Bool) (args' : List val),
      eval_condition cond args m = some b →
      vagree_list args args' (needs_of_condition cond) →
      eval_condition cond args' m' = some b

def needs_of_addressing_32_soundStatement : Prop :=
  ∀ (ge : genv) (sp : block) (addr : addressing) (args : List val)
      (v : val) (nv : nval) (args' : List val),
    eval_addressing32 ge (Vptr sp Ptrofs.zero) addr args = some v →
    vagree_list args args' (needs_of_addressing addr nv) →
    ∃ v',
      eval_addressing32 ge (Vptr sp Ptrofs.zero) addr args' = some v' ∧
        vagree v v' nv

def needs_of_addressing_64_soundStatement : Prop :=
  ∀ (ge : genv) (sp : block) (addr : addressing) (args : List val)
      (v : val) (nv : nval) (args' : List val),
    eval_addressing64 ge (Vptr sp Ptrofs.zero) addr args = some v →
    vagree_list args args' (needs_of_addressing addr nv) →
    ∃ v',
      eval_addressing64 ge (Vptr sp Ptrofs.zero) addr args' = some v' ∧
        vagree v v' nv

def needs_of_operation_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (m m' : mem),
    (∀ b ofs k p, Mem.perm m b ofs k p → Mem.perm m' b ofs k p) →
    ∀ (op : operation) (args : List val) (v : val) (nv : nval)
      (args' : List val),
      eval_operation
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          ge (Vptr sp Ptrofs.zero) op args m = some v →
      vagree_list args args' (needs_of_operation op nv) →
      nv ≠ Nothing →
      ∃ v',
        eval_operation
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            ge (Vptr sp Ptrofs.zero) op args' m' = some v' ∧
        vagree v v' nv

def operation_is_redundant_soundStatement
    [binary64_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 53) (ZArith.BinInt.Z.of_nat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate
      (ZArith.BinInt.Z.of_nat 24) (ZArith.BinInt.Z.of_nat 128)] : Prop :=
  ∀ (ge : genv) (sp : block) (m : mem) (op : operation) (nv : nval)
      (arg1 : val) (args : List val) (v : val) (arg1' : val)
      (args' : List val),
    operation_is_redundant op nv = true →
    eval_operation
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        ge (Vptr sp Ptrofs.zero) op (arg1 :: args) m = some v →
    vagree_list (arg1 :: args) (arg1' :: args') (needs_of_operation op nv) →
    vagree v arg1' nv

end CompCert4Lean.X86.NeedOp
