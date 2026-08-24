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

def eval_static_operation (cfg : CompilerConfig) (op : operation)
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
  | .Ofloatofint, [v1] => floatofint v1
  | .Ointofsingle, [v1] => intofsingle cfg v1
  | .Osingleofint, [v1] => singleofint v1
  | .Olongoffloat, [v1] => longoffloat cfg v1
  | .Ofloatoflong, [v1] => floatoflong v1
  | .Olongofsingle, [v1] => longofsingle cfg v1
  | .Osingleoflong, [v1] => singleoflong v1
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

def eval_static_operation_soundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (bc : block_classification) (ge : genv),
    genv_match bc ge → ∀ (sp : block), bc sp = BCstack →
    ∀ (op : operation) (vargs : List val) (m : mem) (vres : val)
      (aargs : List aval),
      eval_operation ge (Vptr sp Ptrofs.zero) op vargs m = some vres →
      list_forall2 (vmatch bc) vargs aargs →
      vmatch bc vres (eval_static_operation cfg op aargs)

end CompCert4Lean.X86.ValueAOp
