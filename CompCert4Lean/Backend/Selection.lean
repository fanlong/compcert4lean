import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Builtins
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Switch
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Backend.Cminor
import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Backend.Cminortyping
import CompCert4Lean.Backend.SplitLong
import CompCert4Lean.Backend.SelectDiv
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.SelectLong
import CompCert4Lean.X86.SelectOp
import CompCert4Lean.X86.Machregs

/-!
# Instruction selection

Definition-bearing translation of CompCert's `backend/Selection.v`.
The source's extracted switch compiler and if-conversion heuristic are kept
as local pure support functions; all mapped public definitions retain their
source-shaped identities.
-/

namespace CompCert4Lean.Backend.Selection

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Errors
open CompCert4Lean.Common.Switch
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Cminor
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Backend.Cminortyping
open CompCert4Lean.Backend.SplitLong
open CompCert4Lean.Backend.SelectDiv
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp
open CompCert4Lean.X86.Machregs

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCFloat := CompCert4Lean.Lib.Floats.float
private abbrev CCFloat32 := CompCert4Lean.Lib.Floats.float32
private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev BexactInverseCertificate :=
  CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev z24 : Z := zOfNat 24
private abbrev z53 : Z := zOfNat 53
private abbrev z128 : Z := zOfNat 128
private abbrev z1024 : Z := zOfNat 1024
private abbrev z0 : Z := .Z0
private abbrev z1 : Z := ZArith.BinInt.Z.of_nat 1
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zLt := ZArith.BinInt.Z.lt
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail => .String b tail) .EmptyString

private def stringEq (s1 s2 : RocqString) : Bool :=
  match string_dec s1 s2 with
  | .left _ => true
  | .right _ => false

private def signatureEq (s1 s2 : signature) : Bool :=
  match signature_eq s1 s2 with
  | .left _ => true
  | .right _ => false

private def bytesToString : List UInt8 -> RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (bytesToString rest)

private def selectionErrorText : RocqString :=
  bytesToString [83, 101, 108, 101, 99, 116, 105, 111, 110, 58, 32]

private def badSwitchIntText : RocqString :=
  bytesToString [83, 101, 108, 101, 99, 116, 105, 111, 110, 58, 32,
    98, 97, 100, 32, 115, 119, 105, 116, 99, 104, 32, 40, 105, 110, 116, 41]

private def badSwitchLongText : RocqString :=
  bytesToString [83, 101, 108, 101, 99, 116, 105, 111, 110, 58, 32,
    98, 97, 100, 32, 115, 119, 105, 116, 99, 104, 32, 40, 108, 111, 110, 103, 41]

/-! Condition conversion support. -/

def condexpr_of_expr : CminorSel.expr → condexpr
  | CminorSel.expr.Eop (X86.Op.operation.Ocmp c) el => .CEcond c el
  | CminorSel.expr.Econdition a b c => .CEcondition a (condexpr_of_expr b) (condexpr_of_expr c)
  | CminorSel.expr.Elet a b => .CElet a (condexpr_of_expr b)
  | e => .CEcond (Ccompuimm .Cne (CompCert4Lean.Lib.Integers.Int.zero))
      (CminorSel.exprlist.Econs e CminorSel.exprlist.Enil)

def condition_of_expr : CminorSel.expr → condition × exprlist
  | CminorSel.expr.Eop (X86.Op.operation.Ocmp c) el => (c, el)
  | e => (Ccompuimm .Cne (CompCert4Lean.Lib.Integers.Int.zero),
      CminorSel.exprlist.Econs e CminorSel.exprlist.Enil)

/-! ## Exact generated functional-induction surfaces

These transparent proposition descriptors preserve the source-generated
branch equalities, recursive hypotheses, and negative match obligations.
Their canonical identities are owned here; proof terms remain assigned to the
later proof-migration phase for the `Selectionproof` consumer.
-/

def condexpr_of_expr_indStatement : Prop :=
  ∀ (P : CminorSel.expr → CminorSel.condexpr → Prop),
    (∀ (e : CminorSel.expr) (c : condition) (el : CminorSel.exprlist),
      e = .Eop (.Ocmp c) el →
        P (.Eop (.Ocmp c) el) (.CEcond c el)) →
    (∀ (e : CminorSel.expr) (a : CminorSel.condexpr) (b c : CminorSel.expr),
      e = .Econdition a b c →
      P b (condexpr_of_expr b) →
      P c (condexpr_of_expr c) →
        P (.Econdition a b c)
          (.CEcondition a (condexpr_of_expr b) (condexpr_of_expr c))) →
    (∀ (e a b : CminorSel.expr),
      e = .Elet a b →
      P b (condexpr_of_expr b) →
        P (.Elet a b) (.CElet a (condexpr_of_expr b))) →
    (∀ (e x : CminorSel.expr),
      e = x →
      (match x with
       | .Eop (.Ocmp _) _ | .Econdition _ _ _ | .Elet _ _ => False
       | _ => True) →
        P x (.CEcond (.Ccompuimm .Cne Int.zero) (.Econs e .Enil))) →
    ∀ e : CminorSel.expr, P e (condexpr_of_expr e)

def condition_of_expr_indStatement : Prop :=
  ∀ (P : CminorSel.expr → condition × CminorSel.exprlist → Prop),
    (∀ (e : CminorSel.expr) (c : condition) (el : CminorSel.exprlist),
      e = .Eop (.Ocmp c) el →
        P (.Eop (.Ocmp c) el) (c, el)) →
    (∀ (e x : CminorSel.expr),
      e = x →
      (match x with
       | .Eop (.Ocmp _) _ => False
       | _ => True) →
        P x (.Ccompuimm .Cne Int.zero, .Econs e .Enil)) →
    ∀ e : CminorSel.expr, P e (condition_of_expr e)

/-! Extracted host callbacks used by instruction selection. -/

abbrev CompileSwitchOracle := Z → Nat → table → comptree
abbrev IfConversionHeuristic :=
  ident → Cminor.expr → Cminor.expr → Cminor.expr → typ → CminorSel.stmt → Bool

structure SelectionOracle where
  compileSwitch : CompileSwitchOracle
  ifConversionHeuristic : IfConversionHeuristic

def compile_switch (oracle : SelectionOracle) : CompileSwitchOracle :=
  oracle.compileSwitch

def if_conversion_heuristic (oracle : SelectionOracle) : IfConversionHeuristic :=
  oracle.ifConversionHeuristic

/-! Conversion of loads and stores. -/

def load (chunk : memory_chunk) (e1 : CminorSel.expr) : CminorSel.expr :=
  let (mode, args) := addressing chunk e1
  .Eload chunk mode args

def store (chunk : memory_chunk) (e1 e2 : CminorSel.expr) : CminorSel.stmt :=
  let (mode, args) := addressing chunk e1
  .Sstore chunk mode args e2

section Selection

def globdef := CompCert4Lean.Common.AST.globdef Cminor.fundef Unit
variable (defmap : PTree.t globdef)
variable [hf : helper_functions]

def sel_constant (cfg : CompilerConfig) (cst : Cminor.constant) : CminorSel.expr :=
  match cst with
  | .Ointconst n => .Eop (.Ointconst n) .Enil
  | .Ofloatconst f => .Eop (.Ofloatconst f) .Enil
  | .Osingleconst f => .Eop (.Osingleconst f) .Enil
  | .Olongconst n => CompCert4Lean.X86.SelectLong.longconst n
  | .Oaddrsymbol id ofs => addrsymbol cfg.relocation id ofs
  | .Oaddrstack ofs => addrstack ofs

def sel_unop
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    (op : Cminor.unary_operation) (arg : CminorSel.expr) : CminorSel.expr :=
  match op with
  | .Ocast8unsigned => cast8unsigned arg
  | .Ocast8signed => cast8signed arg
  | .Ocast16unsigned => cast16unsigned arg
  | .Ocast16signed => cast16signed arg
  | .Onegint => negint arg
  | .Onotint => notint arg
  | .Onegf => negf arg
  | .Oabsf => absf arg
  | .Onegfs => negfs arg
  | .Oabsfs => absfs arg
  | .Osingleoffloat => singleoffloat arg
  | .Ofloatofsingle => floatofsingle arg
  | .Ointoffloat => intoffloat arg
  | .Ointuoffloat => intuoffloat
      (binary64_certificate := binary64_certificate) arg
  | .Ofloatofint => floatofint
      (binary64_certificate := binary64_certificate) arg
  | .Ofloatofintu => floatofintu
      (binary64_certificate := binary64_certificate) arg
  | .Ointofsingle => intofsingle arg
  | .Ointuofsingle => intuofsingle
      (binary64_certificate := binary64_certificate) arg
  | .Osingleofint => singleofint
      (binary32_certificate := binary32_certificate) arg
  | .Osingleofintu => singleofintu
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) arg
  | .Onegl => CompCert4Lean.X86.SelectLong.negl arg
  | .Onotl => CompCert4Lean.X86.SelectLong.notl arg
  | .Ointoflong => CompCert4Lean.X86.SelectLong.intoflong arg
  | .Olongofint => CompCert4Lean.X86.SelectLong.longofint arg
  | .Olongofintu => CompCert4Lean.X86.SelectLong.longofintu arg
  | .Olongoffloat => CompCert4Lean.X86.SelectLong.longoffloat arg
  | .Olonguoffloat => longuoffloat arg
  | .Ofloatoflong => CompCert4Lean.X86.SelectLong.floatoflong arg
  | .Ofloatoflongu => floatoflongu arg
  | .Olongofsingle => CompCert4Lean.X86.SelectLong.longofsingle arg
  | .Olonguofsingle => longuofsingle arg
  | .Osingleoflong => CompCert4Lean.X86.SelectLong.singleoflong arg
  | .Osingleoflongu => singleoflongu arg

def sel_binop
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    (op : Cminor.binary_operation)
    (arg1 arg2 : CminorSel.expr) : CminorSel.expr :=
  match op with
  | .Oadd => add arg1 arg2
  | .Osub => sub arg1 arg2
  | .Omul => mul arg1 arg2
  | .Odiv => divs cfg arg1 arg2
  | .Odivu => divu cfg arg1 arg2
  | .Omod => mods cfg arg1 arg2
  | .Omodu => modu cfg arg1 arg2
  | .Oand => and arg1 arg2
  | .Oor => or arg1 arg2
  | .Oxor => xor arg1 arg2
  | .Oshl => shl arg1 arg2
  | .Oshr => shr arg1 arg2
  | .Oshru => shru arg1 arg2
  | .Oaddf => addf arg1 arg2
  | .Osubf => subf arg1 arg2
  | .Omulf => mulf arg1 arg2
  | .Odivf => CompCert4Lean.Backend.SelectDiv.divf
      (certificate := binary64_inverse_certificate) arg1 arg2
  | .Oaddfs => addfs arg1 arg2
  | .Osubfs => subfs arg1 arg2
  | .Omulfs => mulfs arg1 arg2
  | .Odivfs => CompCert4Lean.Backend.SelectDiv.divfs
      (certificate := binary32_inverse_certificate) arg1 arg2
  | .Oaddl => CompCert4Lean.X86.SelectLong.addl arg1 arg2
  | .Osubl => CompCert4Lean.X86.SelectLong.subl arg1 arg2
  | .Omull => CompCert4Lean.X86.SelectLong.mull arg1 arg2
  | .Odivl => divls cfg arg1 arg2
  | .Odivlu => divlu cfg arg1 arg2
  | .Omodl => modls cfg arg1 arg2
  | .Omodlu => modlu cfg arg1 arg2
  | .Oandl => CompCert4Lean.X86.SelectLong.andl arg1 arg2
  | .Oorl => CompCert4Lean.X86.SelectLong.orl arg1 arg2
  | .Oxorl => CompCert4Lean.X86.SelectLong.xorl arg1 arg2
  | .Oshll => CompCert4Lean.X86.SelectLong.shll arg1 arg2
  | .Oshrl => CompCert4Lean.X86.SelectLong.shrl arg1 arg2
  | .Oshrlu => CompCert4Lean.X86.SelectLong.shrlu arg1 arg2
  | .Ocmp c => comp c arg1 arg2
  | .Ocmpu c => compu c arg1 arg2
  | .Ocmpf c => compf c arg1 arg2
  | .Ocmpfs c => compfs c arg1 arg2
  | .Ocmpl c => CompCert4Lean.X86.SelectLong.cmpl c arg1 arg2
  | .Ocmplu c => CompCert4Lean.X86.SelectLong.cmplu c arg1 arg2

def sel_select (ty : typ) (cnd ifso ifnot : CminorSel.expr) : CminorSel.expr :=
  let (cond, args) := condition_of_expr cnd
  if select_supported ty then select ty cond args ifso ifnot
  else .Econdition (condexpr_of_expr cnd) ifso ifnot

def sel_expr
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    : Cminor.expr → CminorSel.expr
  | .Evar id => .Evar id
  | .Econst cst => sel_constant cfg cst
  | .Eunop op arg => sel_unop
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) op
      (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg arg)
  | .Ebinop op arg1 arg2 => sel_binop cfg
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) op
      (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg arg1)
      (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg arg2)
  | .Eload chunk addr => load chunk
      (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg addr)

def sel_exprlist
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    : List Cminor.expr → exprlist
  | [] => .Enil
  | a :: rest => .Econs
      (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg a)
      (sel_exprlist
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg rest)

def sel_select_expr
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    (ty : typ)
    (arg1 arg2 arg3 : Cminor.expr) : CminorSel.expr :=
  let (cond, args) := condition_of_expr
    (sel_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg arg1)
  select ty cond args
    (sel_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg arg2)
    (sel_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg arg3)

def sel_known_builtin (bf : builtin_function) (args : exprlist) : Option CminorSel.expr :=
  match bf, args with
  | .BI_platform b, _ => platform_builtin b args
  | .BI_standard (.BI_select ty), .Econs a1 (.Econs a2 (.Econs a3 .Enil)) =>
      some (sel_select ty a1 a2 a3)
  | .BI_standard .BI_fabs, .Econs a1 .Enil => some (absf a1)
  | .BI_standard .BI_fabsf, .Econs a1 .Enil => some (absfs a1)
  | _, _ => none

inductive call_kind : Type where
  | Call_default
  | Call_imm (id : ident)
  | Call_builtin (ef : external_function)

export call_kind (Call_default Call_imm Call_builtin)

def expr_is_addrof_ident (e : Cminor.expr) : Option ident :=
  match e with
  | .Econst (.Oaddrsymbol id ofs) =>
      if Ptrofs.eq ofs Ptrofs.zero then some id else none
  | _ => none

def classify_call (e : Cminor.expr) : call_kind :=
  match expr_is_addrof_ident e with
  | none => .Call_default
  | some id =>
      match PTree.get id defmap with
      | some (.Gfun (.External ef)) => if ef_inline ef then .Call_builtin ef else .Call_imm id
      | _ => .Call_imm id

def sel_builtin_arg
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    (e : Cminor.expr)
    (c : builtin_arg_constraint) : builtin_arg CminorSel.expr :=
  let e' := sel_expr
    (binary64_certificate := binary64_certificate)
    (binary32_certificate := binary32_certificate)
    (binary64_inverse_certificate := binary64_inverse_certificate)
    (binary32_inverse_certificate := binary32_inverse_certificate) cfg e
  let ba := builtin_arg e'
  if builtin_arg_ok ba c then ba else .BA e'

def sel_builtin_args
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    :
    List Cminor.expr → List builtin_arg_constraint → List (builtin_arg CminorSel.expr)
  | [], _ => []
  | e :: rest, constraints =>
      sel_builtin_arg
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg e
        (constraints.headD .OK_default) ::
        sel_builtin_args
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg rest constraints.tail

def sel_builtin_res (optid : Option ident) : builtin_res ident :=
  match optid with
  | none => .BR_none
  | some id => .BR id

def Sno_op : CminorSel.stmt := .Sseq .Sskip .Sskip

def sel_builtin_default
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    (optid : Option ident) (ef : external_function)
    (args : List Cminor.expr) : CminorSel.stmt :=
  .Sbuiltin (sel_builtin_res optid) ef
    (sel_builtin_args
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg args
      (builtin_constraints ef))

def sel_builtin
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig)
    (optid : Option ident) (ef : external_function)
    (args : List Cminor.expr) : CminorSel.stmt :=
  match ef with
  | .EF_builtin name sg =>
      match lookup_builtin_function name sg with
      | some bf =>
          match optid with
          | some id =>
              match sel_known_builtin bf
                  (sel_exprlist
                    (binary64_certificate := binary64_certificate)
                    (binary32_certificate := binary32_certificate)
                    (binary64_inverse_certificate := binary64_inverse_certificate)
                    (binary32_inverse_certificate := binary32_inverse_certificate) cfg args) with
              | some a => .Sassign id a
              | none => sel_builtin_default
                  (binary64_certificate := binary64_certificate)
                  (binary32_certificate := binary32_certificate)
                  (binary64_inverse_certificate := binary64_inverse_certificate)
                  (binary32_inverse_certificate := binary32_inverse_certificate) cfg optid ef args
          | none => Sno_op
      | none => sel_builtin_default
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg optid ef args
  | _ => sel_builtin_default
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg optid ef args

def sel_switch (make_cmp_eq : CminorSel.expr → Z → CminorSel.expr)
    (make_cmp_ltu : CminorSel.expr → Z → CminorSel.expr)
    (make_sub : CminorSel.expr → Z → CminorSel.expr)
    (make_to_int : CminorSel.expr → CminorSel.expr) : Nat → comptree → exitexpr
  | arg, .CTaction act => .XEexit act
  | arg, .CTifeq key act t =>
      .XEcondition (condexpr_of_expr (make_cmp_eq (.Eletvar arg) key))
        (.XEexit act) (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t)
  | arg, .CTiflt key t1 t2 =>
      .XEcondition (condexpr_of_expr (make_cmp_ltu (.Eletvar arg) key))
        (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t1)
        (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int arg t2)
  | arg, .CTjumptable ofs sz tbl t =>
      .XElet (make_sub (.Eletvar arg) ofs)
        (.XEcondition (condexpr_of_expr (make_cmp_ltu (.Eletvar 0) sz))
          (.XEjumptable (make_to_int (.Eletvar 0)) tbl)
          (sel_switch make_cmp_eq make_cmp_ltu make_sub make_to_int (arg + 1) t))

def sel_switch_int : Nat → comptree → exitexpr :=
  sel_switch
    (fun arg n => comp .Ceq arg (.Eop (.Ointconst (CompCert4Lean.Lib.Integers.Int.repr n)) .Enil))
    (fun arg n => compu .Clt arg (.Eop (.Ointconst (CompCert4Lean.Lib.Integers.Int.repr n)) .Enil))
    (fun arg ofs => sub arg (.Eop (.Ointconst (CompCert4Lean.Lib.Integers.Int.repr ofs)) .Enil))
    id

def sel_switch_long : Nat → comptree → exitexpr :=
  sel_switch
    (fun arg n => CompCert4Lean.X86.SelectLong.cmpl .Ceq arg
      (CompCert4Lean.X86.SelectLong.longconst (Int64.repr n)))
    (fun arg n => CompCert4Lean.X86.SelectLong.cmplu .Clt arg
      (CompCert4Lean.X86.SelectLong.longconst (Int64.repr n)))
    (fun arg ofs => CompCert4Lean.X86.SelectLong.subl arg
      (CompCert4Lean.X86.SelectLong.longconst (Int64.repr ofs)))
    lowlong

inductive stmt_class : Type where
  | SCskip
  | SCassign (id : ident) (a : Cminor.expr)
  | SCother

export stmt_class (SCskip SCassign SCother)

def classify_stmt : Cminor.stmt → stmt_class
  | .Sskip => .SCskip
  | .Sassign id a =>
      match a with
      | .Evar id2 =>
          match ident_eq id id2 with
          | .left _ => .SCskip
          | .right _ => .SCassign id a
      | _ => .SCassign id a
  | .Sbuiltin none (.EF_debug _ _ _) _ => .SCskip
  | .Sseq s1 s2 =>
      match classify_stmt s1, classify_stmt s2 with
      | .SCskip, c2 => c2
      | c1, .SCskip => c1
      | _, _ => .SCother
  | _ => .SCother

def if_conversion_base
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (ki : known_idents) (env : typenv)
    (cond : Cminor.expr) (id : ident) (ifso ifnot : Cminor.expr)
    (kont : CminorSel.stmt) : Option CminorSel.stmt :=
  let ty := env id
  if select_supported ty && is_known ki id && safe_expr ki ifso && safe_expr ki ifnot &&
      if_conversion_heuristic oracle id cond ifso ifnot ty kont then
      some (.Sassign id (sel_select_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg ty cond ifso ifnot))
  else none

def if_conversion
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (ki : known_idents) (env : typenv)
    (cond : Cminor.expr)
    (ifso ifnot : Cminor.stmt) (kont : CminorSel.stmt) : Option CminorSel.stmt :=
  match classify_stmt ifso, classify_stmt ifnot with
  | .SCskip, .SCassign id a =>
      if_conversion_base cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        ki env cond id (.Evar id) a kont
  | .SCassign id a, .SCskip =>
      if_conversion_base cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        ki env cond id a (.Evar id) kont
  | .SCassign id1 a1, .SCassign id2 a2 =>
      match ident_eq id1 id2 with
      | .left _ => if_conversion_base cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          ki env cond id1 a1 a2 kont
      | .right _ => none
  | _, _ => none

def sel_stmt
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (defmap : PTree.t globdef)
    (ki : known_idents) (env : typenv)
    : Cminor.stmt → CminorSel.stmt → res CminorSel.stmt
  | .Sskip, _ => .OK .Sskip
  | .Sassign id e, _ => .OK (.Sassign id (sel_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg e))
  | .Sstore chunk addr rhs, _ =>
      let (mode, args) := CompCert4Lean.X86.SelectOp.addressing chunk (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg addr)
      .OK (.Sstore chunk mode args (sel_expr
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) cfg rhs))
  | .Scall optid sg fn args, _ =>
      .OK (match classify_call defmap fn with
      | Call_default => .Scall optid sg (.inl (sel_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg fn))
          (sel_exprlist
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate) cfg args)
      | Call_imm id => .Scall optid sg (.inr id)
          (sel_exprlist
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate) cfg args)
      | Call_builtin ef => sel_builtin
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg optid ef args)
  | .Sbuiltin optid ef args, _ => .OK (sel_builtin
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg optid ef args)
  | .Stailcall sg fn args, _ =>
      .OK (match classify_call defmap fn with
      | Call_imm id => .Stailcall sg (.inr id)
          (sel_exprlist
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate) cfg args)
      | _ => .Stailcall sg (.inl (sel_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg fn))
          (sel_exprlist
            (binary64_certificate := binary64_certificate)
            (binary32_certificate := binary32_certificate)
            (binary64_inverse_certificate := binary64_inverse_certificate)
            (binary32_inverse_certificate := binary32_inverse_certificate) cfg args))
  | .Sseq s1 s2, k =>
      match sel_stmt cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          defmap ki env s2 k with
      | .Error msg => .Error msg
      | .OK s2' =>
          match sel_stmt cfg oracle
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (binary64_inverse_certificate := binary64_inverse_certificate)
              (binary32_inverse_certificate := binary32_inverse_certificate)
              defmap ki env s1 s2' with
          | .Error msg => .Error msg
          | .OK s1' => .OK (.Sseq s1' s2')
  | .Sifthenelse e ifso ifnot, k =>
      match if_conversion cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          ki env e ifso ifnot k with
      | some s => .OK s
      | none =>
          match sel_stmt cfg oracle
              (binary64_certificate := binary64_certificate)
              (binary32_certificate := binary32_certificate)
              (binary64_inverse_certificate := binary64_inverse_certificate)
              (binary32_inverse_certificate := binary32_inverse_certificate)
              defmap ki env ifso k,
              sel_stmt cfg oracle
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                (binary64_inverse_certificate := binary64_inverse_certificate)
                (binary32_inverse_certificate := binary32_inverse_certificate)
                defmap ki env ifnot k with
          | .OK ifso', .OK ifnot' =>
              .OK (.Sifthenelse (condexpr_of_expr (sel_expr
                (binary64_certificate := binary64_certificate)
                (binary32_certificate := binary32_certificate)
                (binary64_inverse_certificate := binary64_inverse_certificate)
                (binary32_inverse_certificate := binary32_inverse_certificate) cfg e)) ifso' ifnot')
          | .Error msg, _ | _, .Error msg => .Error msg
  | .Sloop body, _ =>
      match sel_stmt cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          defmap ki env body .Sskip with
      | .OK body' => .OK (.Sloop body')
      | .Error msg => .Error msg
  | .Sblock body, k =>
      match sel_stmt cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          defmap ki env body k with
      | .OK body' => .OK (.Sblock body')
      | .Error msg => .Error msg
  | .Sexit n, _ => .OK (.Sexit n)
  | .Sswitch false e cases dfl, _ =>
      let t := compile_switch oracle Int.modulus dfl cases
      if validate_switch Int.modulus dfl cases t then
        .OK (.Sswitch (.XElet (sel_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg e) (sel_switch_int 0 t)))
      else .Error (msg badSwitchIntText)
  | .Sswitch true e cases dfl, _ =>
      let t := compile_switch oracle Int64.modulus dfl cases
      if validate_switch Int64.modulus dfl cases t then
        .OK (.Sswitch (.XElet (sel_expr
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate) cfg e) (sel_switch_long 0 t)))
      else .Error (msg badSwitchLongText)
  | .Sreturn none, _ => .OK (.Sreturn none)
  | .Sreturn (some e), _ => .OK (.Sreturn (some (sel_expr
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) cfg e)))
  | .Slabel lbl body, k =>
      match sel_stmt cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          defmap ki env body k with
      | .OK body' => .OK (.Slabel lbl body')
      | .Error msg => .Error msg
  | .Sgoto lbl, _ => .OK (.Sgoto lbl)

end Selection

def known_id (f : Cminor.function) : known_idents :=
  let add (ki : known_idents) (id : ident) := PTree.set id () ki
  f.fn_vars.foldl add (f.fn_params.foldl add (PTree.empty Unit))

def sel_function
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (dm : PTree.t globdef) (hf : helper_functions)
    (f : Cminor.function) : res CminorSel.function :=
  letI : helper_functions := hf
  let ki := known_id f
  match type_function f with
  | .Error msg => .Error msg
  | .OK env =>
      match sel_stmt cfg oracle
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate)
          (binary64_inverse_certificate := binary64_inverse_certificate)
          (binary32_inverse_certificate := binary32_inverse_certificate)
          dm ki env f.fn_body .Sskip with
      | .Error msg => .Error msg
      | .OK body' =>
          .OK { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_vars := f.fn_vars,
                fn_stackspace := f.fn_stackspace, fn_body := body' }

def sel_fundef
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (dm : PTree.t globdef) (hf : helper_functions)
    (f : Cminor.fundef) : res CminorSel.fundef :=
  transf_partial_fundef
    (sel_function cfg oracle
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate) dm hf) f

def globdef_of_interest (gd : globdef) : Bool :=
  match gd with
  | .Gfun (.External (.EF_runtime _ _)) => true
  | _ => false

def record_globdefs (defmap : PTree.t globdef) : PTree.t globdef :=
  PTree.fold
    (fun m id gd => if globdef_of_interest gd then PTree.set id gd m else m)
    defmap (PTree.empty globdef)

def lookup_helper_aux (name : RocqString) (sg : signature) (result : Option ident)
    (id : ident) (gd : globdef) : Option ident :=
  match gd with
  | .Gfun (.External (.EF_runtime name' sg')) =>
      if stringEq name name' && signatureEq sg sg' then some id else result
  | _ => result

def lookup_helper (globs : PTree.t globdef) (name : RocqString)
    (sg : signature) : res ident :=
  match PTree.fold (lookup_helper_aux name sg) globs none with
  | some id => .OK id
  | none => .Error (MSG name :: MSG (ofString ": missing or incorrect declaration") :: [])

def get_helpers (defmap : PTree.t globdef) : res helper_functions :=
  let globs := record_globdefs defmap
  match lookup_helper globs (ofString "__compcert_i64_dtos") sig_f_l with
  | .Error msg => .Error msg
  | .OK i64_dtos =>
    match lookup_helper globs (ofString "__compcert_i64_dtou") sig_f_l with
    | .Error msg => .Error msg
    | .OK i64_dtou =>
      match lookup_helper globs (ofString "__compcert_i64_stod") sig_l_f with
      | .Error msg => .Error msg
      | .OK i64_stod =>
        match lookup_helper globs (ofString "__compcert_i64_utod") sig_l_f with
        | .Error msg => .Error msg
        | .OK i64_utod =>
          match lookup_helper globs (ofString "__compcert_i64_stof") sig_l_s with
          | .Error msg => .Error msg
          | .OK i64_stof =>
            match lookup_helper globs (ofString "__compcert_i64_utof") sig_l_s with
            | .Error msg => .Error msg
            | .OK i64_utof =>
              match lookup_helper globs (ofString "__compcert_i64_sdiv") sig_ll_l with
              | .Error msg => .Error msg
              | .OK i64_sdiv =>
                match lookup_helper globs (ofString "__compcert_i64_udiv") sig_ll_l with
                | .Error msg => .Error msg
                | .OK i64_udiv =>
                  match lookup_helper globs (ofString "__compcert_i64_smod") sig_ll_l with
                  | .Error msg => .Error msg
                  | .OK i64_smod =>
                    match lookup_helper globs (ofString "__compcert_i64_umod") sig_ll_l with
                    | .Error msg => .Error msg
                    | .OK i64_umod =>
                      match lookup_helper globs (ofString "__compcert_i64_shl") sig_li_l with
                      | .Error msg => .Error msg
                      | .OK i64_shl =>
                        match lookup_helper globs (ofString "__compcert_i64_shr") sig_li_l with
                        | .Error msg => .Error msg
                        | .OK i64_shr =>
                          match lookup_helper globs (ofString "__compcert_i64_sar") sig_li_l with
                          | .Error msg => .Error msg
                          | .OK i64_sar =>
                            match lookup_helper globs (ofString "__compcert_i64_umulh") sig_ll_l with
                            | .Error msg => .Error msg
                            | .OK i64_umulh =>
                              match lookup_helper globs (ofString "__compcert_i64_smulh") sig_ll_l with
                              | .Error msg => .Error msg
                              | .OK i64_smulh =>
                                .OK { i64_dtos, i64_dtou, i64_stod, i64_utod, i64_stof, i64_utof,
                                      i64_sdiv, i64_udiv, i64_smod, i64_umod, i64_shl, i64_shr,
                                      i64_sar, i64_umulh, i64_smulh }

def sel_program
    [binary64_certificate : BinaryNormalizeCertificate z53 z1024]
    [binary32_certificate : BinaryNormalizeCertificate z24 z128]
    [binary64_inverse_certificate : BexactInverseCertificate z53 z1024]
    [binary32_inverse_certificate : BexactInverseCertificate z24 z128]
    (cfg : CompilerConfig) (oracle : SelectionOracle)
    (p : Cminor.program) : res CminorSel.program :=
  let dm := prog_defmap p
  match get_helpers dm with
  | .Error msg => .Error msg
  | .OK hf => transform_partial_program
      (sel_fundef cfg oracle
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate) dm hf) p

end CompCert4Lean.Backend.Selection
