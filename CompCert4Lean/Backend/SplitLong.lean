import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Lib.Integers
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.SelectOp

/-!
# Splitting 64-bit integer operations

Definition-bearing translation of CompCert's `backend/SplitLong.vp`.  The
generated `Nondetfunction` case surfaces are retained as ordinary Lean case
classifiers.  The trailing source helper outside this packet's formal roots is
intentionally not reproduced here.
-/

namespace CompCert4Lean.Backend.SplitLong

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev CCComparison := CompCert4Lean.Lib.Integers.comparison
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev intRepr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev intSigned := CompCert4Lean.Lib.Integers.Int.signed
private abbrev intZero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev intIwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev intEq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev intLtu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev intSub := CompCert4Lean.Lib.Integers.Int.sub
private abbrev int64Repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev int64Zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev int64One := CompCert4Lean.Lib.Integers.Int64.one
private abbrev int64Iwordsize := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev int64Eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev int64Neg := CompCert4Lean.Lib.Integers.Int64.neg
private abbrev int64Add := CompCert4Lean.Lib.Integers.Int64.add
private abbrev int64Sub := CompCert4Lean.Lib.Integers.Int64.sub
private abbrev int64Mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev int64IsPower2 := CompCert4Lean.Lib.Integers.Int64.is_power2'
private abbrev int64Hiword := CompCert4Lean.Lib.Integers.Int64.hiword
private abbrev int64Loword := CompCert4Lean.Lib.Integers.Int64.loword
private abbrev int64Ofwords := CompCert4Lean.Lib.Integers.Int64.ofwords

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

/-! ## Runtime helper names and signatures -/

class helper_functions : Type where
  i64_dtos : ident
  i64_dtou : ident
  i64_stod : ident
  i64_utod : ident
  i64_stof : ident
  i64_utof : ident
  i64_sdiv : ident
  i64_udiv : ident
  i64_smod : ident
  i64_umod : ident
  i64_shl : ident
  i64_shr : ident
  i64_sar : ident
  i64_umulh : ident
  i64_smulh : ident

export helper_functions (i64_dtos i64_dtou i64_stod i64_utod i64_stof i64_utof
  i64_sdiv i64_udiv i64_smod i64_umod i64_shl i64_shr i64_sar i64_umulh
  i64_smulh)

def sig_l_l : signature :=
  { sig_args := [Xlong], sig_res := Xlong, sig_cc := cc_default }

def sig_l_f : signature :=
  { sig_args := [Xlong], sig_res := Xfloat, sig_cc := cc_default }

def sig_l_s : signature :=
  { sig_args := [Xlong], sig_res := Xsingle, sig_cc := cc_default }

def sig_f_l : signature :=
  { sig_args := [Xfloat], sig_res := Xlong, sig_cc := cc_default }

def sig_ll_l : signature :=
  { sig_args := [Xlong, Xlong], sig_res := Xlong, sig_cc := cc_default }

def sig_li_l : signature :=
  { sig_args := [Xlong, Xint], sig_res := Xlong, sig_cc := cc_default }

def sig_ii_l : signature :=
  { sig_args := [Xint, Xint], sig_res := Xlong, sig_cc := cc_default }

/-! ## Long construction and generated case classifiers -/

def makelong (h l : expr) : expr :=
  Eop Omakelong (Econs h (Econs l Enil))

inductive splitlong_cases : expr -> Type where
  | splitlong_case1 (h l : expr) :
      splitlong_cases (Eop Omakelong (Econs h (Econs l Enil)))
  | splitlong_default (e : expr) : splitlong_cases e

export splitlong_cases (splitlong_case1 splitlong_default)

def splitlong_match (e : expr) : splitlong_cases e :=
  match e with
  | Eop Omakelong (Econs h (Econs l Enil)) => .splitlong_case1 h l
  | e => .splitlong_default e

def splitlong (e : expr) (f : expr -> expr -> expr) : expr :=
  match splitlong_match e with
  | .splitlong_case1 h l => f h l
  | .splitlong_default e =>
      Elet e
        (f (Eop Ohighlong (Econs (Eletvar 0) Enil))
          (Eop Olowlong (Econs (Eletvar 0) Enil)))

inductive splitlong2_cases : expr -> expr -> Type where
  | splitlong2_case1 (h1 l1 h2 l2 : expr) :
      splitlong2_cases
        (Eop Omakelong (Econs h1 (Econs l1 Enil)))
        (Eop Omakelong (Econs h2 (Econs l2 Enil)))
  | splitlong2_case2 (h1 l1 t2 : expr) :
      splitlong2_cases (Eop Omakelong (Econs h1 (Econs l1 Enil))) t2
  | splitlong2_case3 (t1 h2 l2 : expr) :
      splitlong2_cases t1 (Eop Omakelong (Econs h2 (Econs l2 Enil)))
  | splitlong2_default (e1 e2 : expr) : splitlong2_cases e1 e2

export splitlong2_cases (splitlong2_case1 splitlong2_case2 splitlong2_case3
  splitlong2_default)

def splitlong2_match (e1 e2 : expr) : splitlong2_cases e1 e2 :=
  match e1, e2 with
  | Eop Omakelong (Econs h1 (Econs l1 Enil)),
      Eop Omakelong (Econs h2 (Econs l2 Enil)) =>
      .splitlong2_case1 h1 l1 h2 l2
  | Eop Omakelong (Econs h1 (Econs l1 Enil)), t2 =>
      .splitlong2_case2 h1 l1 t2
  | t1, Eop Omakelong (Econs h2 (Econs l2 Enil)) =>
      .splitlong2_case3 t1 h2 l2
  | e1, e2 => .splitlong2_default e1 e2

def splitlong2 (e1 e2 : expr)
    (f : expr -> expr -> expr -> expr -> expr) : expr :=
  match splitlong2_match e1 e2 with
  | .splitlong2_case1 h1 l1 h2 l2 => f h1 l1 h2 l2
  | .splitlong2_case2 h1 l1 t2 =>
      Elet t2
        (f (lift h1) (lift l1)
          (Eop Ohighlong (Econs (Eletvar 0) Enil))
          (Eop Olowlong (Econs (Eletvar 0) Enil)))
  | .splitlong2_case3 t1 h2 l2 =>
      Elet t1
        (f (Eop Ohighlong (Econs (Eletvar 0) Enil))
          (Eop Olowlong (Econs (Eletvar 0) Enil))
          (lift h2) (lift l2))
  | .splitlong2_default e1 e2 =>
      Elet e1
        (Elet (lift e2)
          (f (Eop Ohighlong (Econs (Eletvar 1) Enil))
            (Eop Olowlong (Econs (Eletvar 1) Enil))
            (Eop Ohighlong (Econs (Eletvar 0) Enil))
            (Eop Olowlong (Econs (Eletvar 0) Enil))))

inductive lowlong_cases : expr -> Type where
  | lowlong_case1 (e1 e2 : expr) :
      lowlong_cases (Eop Omakelong (Econs e1 (Econs e2 Enil)))
  | lowlong_default (e : expr) : lowlong_cases e

export lowlong_cases (lowlong_case1 lowlong_default)

def lowlong_match (e : expr) : lowlong_cases e :=
  match e with
  | Eop Omakelong (Econs e1 (Econs e2 Enil)) => .lowlong_case1 e1 e2
  | e => .lowlong_default e

def lowlong (e : expr) : expr :=
  match lowlong_match e with
  | .lowlong_case1 _ e2 => e2
  | .lowlong_default e => Eop Olowlong (Econs e Enil)

inductive highlong_cases : expr -> Type where
  | highlong_case1 (e1 e2 : expr) :
      highlong_cases (Eop Omakelong (Econs e1 (Econs e2 Enil)))
  | highlong_default (e : expr) : highlong_cases e

export highlong_cases (highlong_case1 highlong_default)

def highlong_match (e : expr) : highlong_cases e :=
  match e with
  | Eop Omakelong (Econs e1 (Econs e2 Enil)) => .highlong_case1 e1 e2
  | e => .highlong_default e

def highlong (e : expr) : expr :=
  match highlong_match e with
  | .highlong_case1 e1 _ => e1
  | .highlong_default e => Eop Ohighlong (Econs e Enil)

/-! ## Constants and conversions -/

def longconst (n : CCInt64) : expr :=
  makelong (Eop (Ointconst (int64Hiword n)) Enil)
    (Eop (Ointconst (int64Loword n)) Enil)

inductive is_longconst_cases : expr -> Type where
  | is_longconst_case1 (h l : CCInt) :
      is_longconst_cases
        (Eop Omakelong
          (Econs (Eop (Ointconst h) Enil)
            (Econs (Eop (Ointconst l) Enil) Enil)))
  | is_longconst_default (e : expr) : is_longconst_cases e

export is_longconst_cases (is_longconst_case1 is_longconst_default)

def is_longconst_match (e : expr) : is_longconst_cases e :=
  match e with
  | Eop Omakelong
      (Econs (Eop (Ointconst h) Enil)
        (Econs (Eop (Ointconst l) Enil) Enil)) =>
      .is_longconst_case1 h l
  | e => .is_longconst_default e

def is_longconst (e : expr) : Option CCInt64 :=
  match is_longconst_match e with
  | .is_longconst_case1 h l => some (int64Ofwords h l)
  | .is_longconst_default _ => none

def is_longconst_zero (e : expr) : Bool :=
  match is_longconst e with
  | some n => int64Eq n int64Zero
  | none => false

def intoflong (e : expr) : expr := lowlong e

inductive longofint_cases : expr -> Type where
  | longofint_case1 (n : CCInt) :
      longofint_cases (Eop (Ointconst n) Enil)
  | longofint_default (e : expr) : longofint_cases e

export longofint_cases (longofint_case1 longofint_default)

def longofint_match (e : expr) : longofint_cases e :=
  match e with
  | Eop (Ointconst n) Enil => .longofint_case1 n
  | e => .longofint_default e

def longofint (e : expr) : expr :=
  match longofint_match e with
  | .longofint_case1 n => longconst (int64Repr (intSigned n))
  | .longofint_default e =>
      Elet e
        (makelong
          (CompCert4Lean.X86.SelectOp.shrimm (Eletvar 0)
            (intRepr (zOfNat 31)))
          (Eletvar 0))

def longofintu (e : expr) : expr :=
  makelong (Eop (Ointconst intZero) Enil) e

def negl (e : expr) : expr :=
  match is_longconst e with
  | some n => longconst (int64Neg n)
  | none =>
      Ebuiltin (EF_builtin (ofString "__builtin_negl") sig_l_l)
        (Econs e Enil)

def notl (e : expr) : expr :=
  splitlong e fun h l =>
    makelong (CompCert4Lean.X86.SelectOp.notint h)
      (CompCert4Lean.X86.SelectOp.notint l)

section HelperFunctions

variable [hf : helper_functions]

def longoffloat (arg : expr) : expr :=
  Eexternal hf.i64_dtos sig_f_l (Econs arg Enil)

def longuoffloat (arg : expr) : expr :=
  Eexternal hf.i64_dtou sig_f_l (Econs arg Enil)

def floatoflong (arg : expr) : expr :=
  Eexternal hf.i64_stod sig_l_f (Econs arg Enil)

def floatoflongu (arg : expr) : expr :=
  Eexternal hf.i64_utod sig_l_f (Econs arg Enil)

def longofsingle (arg : expr) : expr :=
  longoffloat (CompCert4Lean.X86.SelectOp.floatofsingle arg)

def longuofsingle (arg : expr) : expr :=
  longuoffloat (CompCert4Lean.X86.SelectOp.floatofsingle arg)

def singleoflong (arg : expr) : expr :=
  Eexternal hf.i64_stof sig_l_s (Econs arg Enil)

def singleoflongu (arg : expr) : expr :=
  Eexternal hf.i64_utof sig_l_s (Econs arg Enil)

/-! ## Logical and shift operations -/

def andl (e1 e2 : expr) : expr :=
  splitlong2 e1 e2 fun h1 l1 h2 l2 =>
    makelong (CompCert4Lean.X86.SelectOp.and h1 h2)
      (CompCert4Lean.X86.SelectOp.and l1 l2)

def orl (e1 e2 : expr) : expr :=
  splitlong2 e1 e2 fun h1 l1 h2 l2 =>
    makelong (CompCert4Lean.X86.SelectOp.or h1 h2)
      (CompCert4Lean.X86.SelectOp.or l1 l2)

def xorl (e1 e2 : expr) : expr :=
  splitlong2 e1 e2 fun h1 l1 h2 l2 =>
    makelong (CompCert4Lean.X86.SelectOp.xor h1 h2)
      (CompCert4Lean.X86.SelectOp.xor l1 l2)

def shllimm (e1 : expr) (n : CCInt) : expr :=
  if intEq n intZero then e1
  else if intLtu n intIwordsize then
    splitlong e1 fun h l =>
      makelong
        (CompCert4Lean.X86.SelectOp.or
          (CompCert4Lean.X86.SelectOp.shlimm h n)
          (CompCert4Lean.X86.SelectOp.shruimm l (intSub intIwordsize n)))
        (CompCert4Lean.X86.SelectOp.shlimm l n)
  else if intLtu n int64Iwordsize then
    makelong
      (CompCert4Lean.X86.SelectOp.shlimm (lowlong e1)
        (intSub n intIwordsize))
      (Eop (Ointconst intZero) Enil)
  else
    Eexternal hf.i64_shl sig_li_l
      (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))

def shrluimm (e1 : expr) (n : CCInt) : expr :=
  if intEq n intZero then e1
  else if intLtu n intIwordsize then
    splitlong e1 fun h l =>
      makelong
        (CompCert4Lean.X86.SelectOp.shruimm h n)
        (CompCert4Lean.X86.SelectOp.or
          (CompCert4Lean.X86.SelectOp.shruimm l n)
          (CompCert4Lean.X86.SelectOp.shlimm h (intSub intIwordsize n)))
  else if intLtu n int64Iwordsize then
    makelong (Eop (Ointconst intZero) Enil)
      (CompCert4Lean.X86.SelectOp.shruimm (highlong e1)
        (intSub n intIwordsize))
  else
    Eexternal hf.i64_shr sig_li_l
      (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))

def shrlimm (e1 : expr) (n : CCInt) : expr :=
  if intEq n intZero then e1
  else if intLtu n intIwordsize then
    splitlong e1 fun h l =>
      makelong
        (CompCert4Lean.X86.SelectOp.shrimm h n)
        (CompCert4Lean.X86.SelectOp.or
          (CompCert4Lean.X86.SelectOp.shruimm l n)
          (CompCert4Lean.X86.SelectOp.shlimm h (intSub intIwordsize n)))
  else if intLtu n int64Iwordsize then
    Elet (highlong e1)
      (makelong
        (CompCert4Lean.X86.SelectOp.shrimm (Eletvar 0)
          (intRepr (zOfNat 31)))
        (CompCert4Lean.X86.SelectOp.shrimm (Eletvar 0)
          (intSub n intIwordsize)))
  else
    Eexternal hf.i64_sar sig_li_l
      (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))

def is_intconst (e : expr) : Option CCInt :=
  match e with
  | Eop (Ointconst n) Enil => some n
  | _ => none

def shll (e1 e2 : expr) : expr :=
  match is_intconst e2 with
  | some n => shllimm e1 n
  | none => Eexternal hf.i64_shl sig_li_l (Econs e1 (Econs e2 Enil))

def shrlu (e1 e2 : expr) : expr :=
  match is_intconst e2 with
  | some n => shrluimm e1 n
  | none => Eexternal hf.i64_shr sig_li_l (Econs e1 (Econs e2 Enil))

def shrl (e1 e2 : expr) : expr :=
  match is_intconst e2 with
  | some n => shrlimm e1 n
  | none => Eexternal hf.i64_sar sig_li_l (Econs e1 (Econs e2 Enil))

/-! ## Arithmetic -/

def addl (e1 e2 : expr) : expr :=
  let default :=
    Ebuiltin (EF_builtin (ofString "__builtin_addl") sig_ll_l)
      (Econs e1 (Econs e2 Enil))
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 => longconst (int64Add n1 n2)
  | some n1, none => if int64Eq n1 int64Zero then e2 else default
  | none, some n2 => if int64Eq n2 int64Zero then e1 else default
  | none, none => default

def subl (e1 e2 : expr) : expr :=
  let default :=
    Ebuiltin (EF_builtin (ofString "__builtin_subl") sig_ll_l)
      (Econs e1 (Econs e2 Enil))
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 => longconst (int64Sub n1 n2)
  | some n1, none => if int64Eq n1 int64Zero then negl e2 else default
  | none, some n2 => if int64Eq n2 int64Zero then e1 else default
  | none, none => default

def mull_base (e1 e2 : expr) : expr :=
  splitlong2 e1 e2 fun h1 l1 h2 l2 =>
    Elet
      (Ebuiltin (EF_builtin (ofString "__builtin_mull") sig_ii_l)
        (Econs l1 (Econs l2 Enil)))
      (makelong
        (CompCert4Lean.X86.SelectOp.add
          (CompCert4Lean.X86.SelectOp.add
            (Eop Ohighlong (Econs (Eletvar 0) Enil))
            (CompCert4Lean.X86.SelectOp.mul (lift l1) (lift h2)))
          (CompCert4Lean.X86.SelectOp.mul (lift h1) (lift l2)))
        (Eop Olowlong (Econs (Eletvar 0) Enil)))

def mullimm (n : CCInt64) (e : expr) : expr :=
  if int64Eq n int64Zero then longconst int64Zero
  else if int64Eq n int64One then e
  else
    match int64IsPower2 n with
    | some l => shllimm e l
    | none => mull_base e (longconst n)

def mull (e1 e2 : expr) : expr :=
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 => longconst (int64Mul n1 n2)
  | some n1, none => mullimm n1 e2
  | none, some n2 => mullimm n2 e1
  | none, none => mull_base e1 e2

def mullhu (e1 : expr) (n2 : CCInt64) : expr :=
  Eexternal hf.i64_umulh sig_ll_l (Econs e1 (Econs (longconst n2) Enil))

def mullhs (e1 : expr) (n2 : CCInt64) : expr :=
  Eexternal hf.i64_smulh sig_ll_l (Econs e1 (Econs (longconst n2) Enil))

def shrxlimm (e : expr) (n : CCInt) : expr :=
  if intEq n intZero then e
  else
    Elet e
      (shrlimm
        (addl (Eletvar 0)
          (shrluimm
            (shrlimm (Eletvar 0) (intRepr (zOfNat 63)))
            (intSub (intRepr (zOfNat 64)) n)))
        n)

def divlu_base (e1 e2 : expr) : expr :=
  Eexternal hf.i64_udiv sig_ll_l (Econs e1 (Econs e2 Enil))

def modlu_base (e1 e2 : expr) : expr :=
  Eexternal hf.i64_umod sig_ll_l (Econs e1 (Econs e2 Enil))

def divls_base (e1 e2 : expr) : expr :=
  Eexternal hf.i64_sdiv sig_ll_l (Econs e1 (Econs e2 Enil))

def modls_base (e1 e2 : expr) : expr :=
  Eexternal hf.i64_smod sig_ll_l (Econs e1 (Econs e2 Enil))

/-! ## Comparisons -/

def cmpl_eq_zero (e : expr) : expr :=
  splitlong e fun h l =>
    CompCert4Lean.X86.SelectOp.comp Ceq
      (CompCert4Lean.X86.SelectOp.or h l)
      (Eop (Ointconst intZero) Enil)

def cmpl_ne_zero (e : expr) : expr :=
  splitlong e fun h l =>
    CompCert4Lean.X86.SelectOp.comp Cne
      (CompCert4Lean.X86.SelectOp.or h l)
      (Eop (Ointconst intZero) Enil)

def cmplu_gen (ch cl : CCComparison) (e1 e2 : expr) : expr :=
  splitlong2 e1 e2 fun h1 l1 h2 l2 =>
    Econdition
      (CEcond (Ccomp Ceq) (Econs h1 (Econs h2 Enil)))
      (Eop (Ocmp (Ccompu cl)) (Econs l1 (Econs l2 Enil)))
      (Eop (Ocmp (Ccompu ch)) (Econs h1 (Econs h2 Enil)))

def cmplu (c : CCComparison) (e1 e2 : expr) : expr :=
  match c with
  | .Ceq => cmpl_eq_zero (xorl e1 e2)
  | .Cne => cmpl_ne_zero (xorl e1 e2)
  | .Clt => cmplu_gen Clt Clt e1 e2
  | .Cle => cmplu_gen Clt Cle e1 e2
  | .Cgt => cmplu_gen Cgt Cgt e1 e2
  | .Cge => cmplu_gen Cgt Cge e1 e2

def cmpl_gen (ch cl : CCComparison) (e1 e2 : expr) : expr :=
  splitlong2 e1 e2 fun h1 l1 h2 l2 =>
    Econdition
      (CEcond (Ccomp Ceq) (Econs h1 (Econs h2 Enil)))
      (Eop (Ocmp (Ccompu cl)) (Econs l1 (Econs l2 Enil)))
      (Eop (Ocmp (Ccomp ch)) (Econs h1 (Econs h2 Enil)))

def cmpl (c : CCComparison) (e1 e2 : expr) : expr :=
  match c with
  | .Ceq => cmpl_eq_zero (xorl e1 e2)
  | .Cne => cmpl_ne_zero (xorl e1 e2)
  | .Clt =>
      if is_longconst_zero e2 then
        CompCert4Lean.X86.SelectOp.comp Clt (highlong e1)
          (Eop (Ointconst intZero) Enil)
      else
        cmpl_gen Clt Clt e1 e2
  | .Cle => cmpl_gen Clt Cle e1 e2
  | .Cgt => cmpl_gen Cgt Cgt e1 e2
  | .Cge =>
      if is_longconst_zero e2 then
        CompCert4Lean.X86.SelectOp.comp Cge (highlong e1)
          (Eop (Ointconst intZero) Enil)
      else
        cmpl_gen Cgt Cge e1 e2

end HelperFunctions

end CompCert4Lean.Backend.SplitLong
