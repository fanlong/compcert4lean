import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Lib.Integers
import CompCert4Lean.X86.SelectOp

/-!
# x86 long-integer instruction selection

Definition-bearing translation of the generated `x86/SelectLong.vp` surface.
The target is the pinned 64-bit x86 configuration, for which `splitlong` is
false; the generated classifiers are retained as dependent Lean inductives.
-/

namespace CompCert4Lean.X86.SelectLong

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.SelectOp

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zOpp := ZArith.BinInt.Z.opp
private abbrev z0 : Z := .Z0

namespace Int
private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
end Int

namespace Int64
private abbrev repr := CompCert4Lean.Lib.Integers.Int64.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int64.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int64.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int64.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int64.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int64.mone
private abbrev iwordsize' := CompCert4Lean.Lib.Integers.Int64.iwordsize'
private abbrev eq := CompCert4Lean.Lib.Integers.Int64.eq
private abbrev add := CompCert4Lean.Lib.Integers.Int64.add
private abbrev mul := CompCert4Lean.Lib.Integers.Int64.mul
private abbrev neg := CompCert4Lean.Lib.Integers.Int64.neg
private abbrev and := CompCert4Lean.Lib.Integers.Int64.and
private abbrev or := CompCert4Lean.Lib.Integers.Int64.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int64.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int64.not
private abbrev shl' := CompCert4Lean.Lib.Integers.Int64.shl'
private abbrev shru' := CompCert4Lean.Lib.Integers.Int64.shru'
private abbrev shr' := CompCert4Lean.Lib.Integers.Int64.shr'
private abbrev one_bits' := CompCert4Lean.Lib.Integers.Int64.one_bits'
end Int64

private def zCmp (c : comparison) (x y : Z) : Bool :=
  let x' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ x
  let y' := CompCert4Lean.Foundation.Numbers.Rocq.Coq.intOfZ y
  match c with
  | .Ceq => decide (x' = y')
  | .Cne => decide (x' != y')
  | .Clt => decide (x' < y')
  | .Cle => decide (x' <= y')
  | .Cgt => decide (x' > y')
  | .Cge => decide (x' >= y')

private def int64Cmp (c : comparison) (x y : CCInt64) : Bool :=
  zCmp c (Int64.signed x) (Int64.signed y)

private def int64Cmpu (c : comparison) (x y : CCInt64) : Bool :=
  zCmp c (Int64.unsigned x) (Int64.unsigned y)

private def is_intconst (e : expr) : Option CCInt :=
  match e with
  | Eop (Ointconst n) Enil => some n
  | _ => none

/-! ## Constants and conversions -/

def longconst (n : CCInt64) : expr :=
  Eop (Olongconst n) Enil

def is_longconst (e : expr) : Option CCInt64 :=
  match e with
  | Eop (Olongconst n) Enil => some n
  | _ => none

def intoflong (e : expr) : expr :=
  match is_longconst e with
  | some n => Eop (Ointconst (Int.repr (Int64.unsigned n))) Enil
  | none => Eop Olowlong (Econs e Enil)

def longofint (e : expr) : expr :=
  match is_intconst e with
  | some n => longconst (Int64.repr (Int.signed n))
  | none => Eop Ocast32signed (Econs e Enil)

def longofintu (e : expr) : expr :=
  match is_intconst e with
  | some n => longconst (Int64.repr (Int.unsigned n))
  | none => Eop Ocast32unsigned (Econs e Enil)

/-! ## Logical negation -/

inductive notl_cases : expr → Type where
  | notl_case1 (n : CCInt64) : notl_cases (Eop (Olongconst n) Enil)
  | notl_case2 (t1 : expr) : notl_cases (Eop Onotl (Econs t1 Enil))
  | notl_default (e : expr) : notl_cases e

export notl_cases (notl_case1 notl_case2 notl_default)

def notl_match (e : expr) : notl_cases e :=
  match e with
  | Eop (Olongconst n) Enil => .notl_case1 n
  | Eop Onotl (Econs t1 Enil) => .notl_case2 t1
  | e => .notl_default e

def notl (e : expr) : expr :=
  match notl_match e with
  | .notl_case1 n => longconst (Int64.not n)
  | .notl_case2 t1 => t1
  | .notl_default e => Eop Onotl (Econs e Enil)

/-! ## Logical and -/

inductive andlimm_cases : expr → Type where
  | andlimm_case1 (n2 : CCInt64) : andlimm_cases (Eop (Olongconst n2) Enil)
  | andlimm_case2 (n2 : CCInt64) (t2 : expr) :
      andlimm_cases (Eop (Oandlimm n2) (Econs t2 Enil))
  | andlimm_default (e2 : expr) : andlimm_cases e2

export andlimm_cases (andlimm_case1 andlimm_case2 andlimm_default)

def andlimm_match (e2 : expr) : andlimm_cases e2 :=
  match e2 with
  | Eop (Olongconst n2) Enil => .andlimm_case1 n2
  | Eop (Oandlimm n2) (Econs t2 Enil) => .andlimm_case2 n2 t2
  | e2 => .andlimm_default e2

def andlimm (n1 : CCInt64) (e2 : expr) : expr :=
  if Int64.eq n1 Int64.zero then longconst Int64.zero
  else if Int64.eq n1 Int64.mone then e2
  else
    match andlimm_match e2 with
    | .andlimm_case1 n2 => longconst (Int64.and n1 n2)
    | .andlimm_case2 n2 t2 => Eop (Oandlimm (Int64.and n1 n2)) (Econs t2 Enil)
    | .andlimm_default e2 => Eop (Oandlimm n1) (Econs e2 Enil)

inductive andl_cases : expr → expr → Type where
  | andl_case1 (n1 : CCInt64) (t2 : expr) :
      andl_cases (Eop (Olongconst n1) Enil) t2
  | andl_case2 (t1 : expr) (n2 : CCInt64) :
      andl_cases t1 (Eop (Olongconst n2) Enil)
  | andl_default (e1 e2 : expr) : andl_cases e1 e2

export andl_cases (andl_case1 andl_case2 andl_default)

def andl_match (e1 e2 : expr) : andl_cases e1 e2 :=
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => .andl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => .andl_case2 t1 n2
  | e1, e2 => .andl_default e1 e2

def andl (e1 e2 : expr) : expr :=
  match andl_match e1 e2 with
  | .andl_case1 n1 t2 => andlimm n1 t2
  | .andl_case2 t1 n2 => andlimm n2 t1
  | .andl_default e1 e2 => Eop Oandl (Econs e1 (Econs e2 Enil))

/-! ## Logical or -/

inductive orlimm_cases : expr → Type where
  | orlimm_case1 (n2 : CCInt64) : orlimm_cases (Eop (Olongconst n2) Enil)
  | orlimm_case2 (n2 : CCInt64) (t2 : expr) :
      orlimm_cases (Eop (Oorlimm n2) (Econs t2 Enil))
  | orlimm_default (e2 : expr) : orlimm_cases e2

export orlimm_cases (orlimm_case1 orlimm_case2 orlimm_default)

def orlimm_match (e2 : expr) : orlimm_cases e2 :=
  match e2 with
  | Eop (Olongconst n2) Enil => .orlimm_case1 n2
  | Eop (Oorlimm n2) (Econs t2 Enil) => .orlimm_case2 n2 t2
  | e2 => .orlimm_default e2

def orlimm (n1 : CCInt64) (e2 : expr) : expr :=
  if Int64.eq n1 Int64.zero then e2
  else if Int64.eq n1 Int64.mone then longconst Int64.mone
  else
    match orlimm_match e2 with
    | .orlimm_case1 n2 => longconst (Int64.or n1 n2)
    | .orlimm_case2 n2 t2 => Eop (Oorlimm (Int64.or n1 n2)) (Econs t2 Enil)
    | .orlimm_default e2 => Eop (Oorlimm n1) (Econs e2 Enil)

inductive orl_cases : expr → expr → Type where
  | orl_case1 (n1 : CCInt64) (t2 : expr) :
      orl_cases (Eop (Olongconst n1) Enil) t2
  | orl_case2 (t1 : expr) (n2 : CCInt64) :
      orl_cases t1 (Eop (Olongconst n2) Enil)
  | orl_case3 (n1 : CCInt) (t1 : expr) (n2 : CCInt) (t2 : expr) :
      orl_cases (Eop (Oshllimm n1) (Econs t1 Enil))
        (Eop (Oshrluimm n2) (Econs t2 Enil))
  | orl_case4 (n2 : CCInt) (t2 : expr) (n1 : CCInt) (t1 : expr) :
      orl_cases (Eop (Oshrluimm n2) (Econs t2 Enil))
        (Eop (Oshllimm n1) (Econs t1 Enil))
  | orl_default (e1 e2 : expr) : orl_cases e1 e2

export orl_cases (orl_case1 orl_case2 orl_case3 orl_case4 orl_default)

def orl_match (e1 e2 : expr) : orl_cases e1 e2 :=
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => .orl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => .orl_case2 t1 n2
  | Eop (Oshllimm n1) (Econs t1 Enil), Eop (Oshrluimm n2) (Econs t2 Enil) =>
      .orl_case3 n1 t1 n2 t2
  | Eop (Oshrluimm n2) (Econs t2 Enil), Eop (Oshllimm n1) (Econs t1 Enil) =>
      .orl_case4 n2 t2 n1 t1
  | e1, e2 => .orl_default e1 e2

def orl (e1 e2 : expr) : expr :=
  match orl_match e1 e2 with
  | .orl_case1 n1 t2 => orlimm n1 t2
  | .orl_case2 t1 n2 => orlimm n2 t1
  | .orl_case3 n1 t1 n2 t2 =>
      if Int.eq (Int.add n1 n2) Int64.iwordsize' && same_expr_pure t1 t2 then
        Eop (Ororlimm n2) (Econs t1 Enil)
      else Eop Oorl (Econs
        (Eop (Oshllimm n1) (Econs t1 Enil))
        (Econs (Eop (Oshrluimm n2) (Econs t2 Enil)) Enil))
  | .orl_case4 n2 t2 n1 t1 =>
      if Int.eq (Int.add n1 n2) Int64.iwordsize' && same_expr_pure t1 t2 then
        Eop (Ororlimm n2) (Econs t1 Enil)
      else Eop Oorl (Econs
        (Eop (Oshrluimm n2) (Econs t2 Enil))
        (Econs (Eop (Oshllimm n1) (Econs t1 Enil)) Enil))
  | .orl_default e1 e2 => Eop Oorl (Econs e1 (Econs e2 Enil))

/-! ## Logical xor -/

inductive xorlimm_cases : expr → Type where
  | xorlimm_case1 (n2 : CCInt64) : xorlimm_cases (Eop (Olongconst n2) Enil)
  | xorlimm_case2 (n2 : CCInt64) (t2 : expr) :
      xorlimm_cases (Eop (Oxorlimm n2) (Econs t2 Enil))
  | xorlimm_case3 (t2 : expr) : xorlimm_cases (Eop Onotl (Econs t2 Enil))
  | xorlimm_default (e2 : expr) : xorlimm_cases e2

export xorlimm_cases (xorlimm_case1 xorlimm_case2 xorlimm_case3 xorlimm_default)

def xorlimm_match (e2 : expr) : xorlimm_cases e2 :=
  match e2 with
  | Eop (Olongconst n2) Enil => .xorlimm_case1 n2
  | Eop (Oxorlimm n2) (Econs t2 Enil) => .xorlimm_case2 n2 t2
  | Eop Onotl (Econs t2 Enil) => .xorlimm_case3 t2
  | e2 => .xorlimm_default e2

def xorlimm (n1 : CCInt64) (e2 : expr) : expr :=
  if Int64.eq n1 Int64.zero then e2
  else if Int64.eq n1 Int64.mone then notl e2
  else
    match xorlimm_match e2 with
    | .xorlimm_case1 n2 => longconst (Int64.xor n1 n2)
    | .xorlimm_case2 n2 t2 => Eop (Oxorlimm (Int64.xor n1 n2)) (Econs t2 Enil)
    | .xorlimm_case3 t2 => Eop (Oxorlimm (Int64.not n1)) (Econs t2 Enil)
    | .xorlimm_default e2 => Eop (Oxorlimm n1) (Econs e2 Enil)

inductive xorl_cases : expr → expr → Type where
  | xorl_case1 (n1 : CCInt64) (t2 : expr) :
      xorl_cases (Eop (Olongconst n1) Enil) t2
  | xorl_case2 (t1 : expr) (n2 : CCInt64) :
      xorl_cases t1 (Eop (Olongconst n2) Enil)
  | xorl_default (e1 e2 : expr) : xorl_cases e1 e2

export xorl_cases (xorl_case1 xorl_case2 xorl_default)

def xorl_match (e1 e2 : expr) : xorl_cases e1 e2 :=
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => .xorl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => .xorl_case2 t1 n2
  | e1, e2 => .xorl_default e1 e2

def xorl (e1 e2 : expr) : expr :=
  match xorl_match e1 e2 with
  | .xorl_case1 n1 t2 => xorlimm n1 t2
  | .xorl_case2 t1 n2 => xorlimm n2 t1
  | .xorl_default e1 e2 => Eop Oxorl (Econs e1 (Econs e2 Enil))

/-! ## Shifts -/

inductive shllimm_cases : expr → Type where
  | shllimm_case1 (n1 : CCInt64) : shllimm_cases (Eop (Olongconst n1) Enil)
  | shllimm_case2 (n1 : CCInt) (t1 : expr) :
      shllimm_cases (Eop (Oshllimm n1) (Econs t1 Enil))
  | shllimm_case3 (n1 : Z) (t1 : expr) :
      shllimm_cases (Eop (Oleal (Aindexed n1)) (Econs t1 Enil))
  | shllimm_default (e1 : expr) : shllimm_cases e1

export shllimm_cases (shllimm_case1 shllimm_case2 shllimm_case3 shllimm_default)

def shllimm_match (e1 : expr) : shllimm_cases e1 :=
  match e1 with
  | Eop (Olongconst n1) Enil => .shllimm_case1 n1
  | Eop (Oshllimm n1) (Econs t1 Enil) => .shllimm_case2 n1 t1
  | Eop (Oleal (Aindexed n1)) (Econs t1 Enil) => .shllimm_case3 n1 t1
  | e1 => .shllimm_default e1

def shllimm (e1 : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e1
  else if !(Int.ltu n Int64.iwordsize') then
    Eop Oshll (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))
  else
    match shllimm_match e1 with
    | .shllimm_case1 n1 => Eop (Olongconst (Int64.shl' n1 n)) Enil
    | .shllimm_case2 n1 t1 =>
        if Int.ltu (Int.add n n1) Int64.iwordsize' then
          Eop (Oshllimm (Int.add n n1)) (Econs t1 Enil)
        else Eop (Oshllimm n)
          (Econs (Eop (Oshllimm n1) (Econs t1 Enil)) Enil)
    | .shllimm_case3 n1 t1 =>
        if shift_is_scale n then
          Eop (Oleal (Ascaled (Int64.unsigned (Int64.shl' Int64.one n))
            (Int64.unsigned (Int64.shl' (Int64.repr n1) n)))) (Econs t1 Enil)
        else Eop (Oshllimm n)
          (Econs (Eop (Oleal (Aindexed n1)) (Econs t1 Enil)) Enil)
    | .shllimm_default e1 =>
        if shift_is_scale n then
          Eop (Oleal (Ascaled (Int64.unsigned (Int64.shl' Int64.one n)) z0))
            (Econs e1 Enil)
        else Eop (Oshllimm n) (Econs e1 Enil)

inductive shrluimm_cases : expr → Type where
  | shrluimm_case1 (n1 : CCInt64) : shrluimm_cases (Eop (Olongconst n1) Enil)
  | shrluimm_case2 (n1 : CCInt) (t1 : expr) :
      shrluimm_cases (Eop (Oshrluimm n1) (Econs t1 Enil))
  | shrluimm_default (e1 : expr) : shrluimm_cases e1

export shrluimm_cases (shrluimm_case1 shrluimm_case2 shrluimm_default)

def shrluimm_match (e1 : expr) : shrluimm_cases e1 :=
  match e1 with
  | Eop (Olongconst n1) Enil => .shrluimm_case1 n1
  | Eop (Oshrluimm n1) (Econs t1 Enil) => .shrluimm_case2 n1 t1
  | e1 => .shrluimm_default e1

def shrluimm (e1 : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e1
  else if !(Int.ltu n Int64.iwordsize') then
    Eop Oshrlu (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))
  else
    match shrluimm_match e1 with
    | .shrluimm_case1 n1 => Eop (Olongconst (Int64.shru' n1 n)) Enil
    | .shrluimm_case2 n1 t1 =>
        if Int.ltu (Int.add n n1) Int64.iwordsize' then
          Eop (Oshrluimm (Int.add n n1)) (Econs t1 Enil)
        else Eop (Oshrluimm n)
          (Econs (Eop (Oshrluimm n1) (Econs t1 Enil)) Enil)
    | .shrluimm_default e1 => Eop (Oshrluimm n) (Econs e1 Enil)

inductive shrlimm_cases : expr → Type where
  | shrlimm_case1 (n1 : CCInt64) : shrlimm_cases (Eop (Olongconst n1) Enil)
  | shrlimm_case2 (n1 : CCInt) (t1 : expr) :
      shrlimm_cases (Eop (Oshrlimm n1) (Econs t1 Enil))
  | shrlimm_default (e1 : expr) : shrlimm_cases e1

export shrlimm_cases (shrlimm_case1 shrlimm_case2 shrlimm_default)

def shrlimm_match (e1 : expr) : shrlimm_cases e1 :=
  match e1 with
  | Eop (Olongconst n1) Enil => .shrlimm_case1 n1
  | Eop (Oshrlimm n1) (Econs t1 Enil) => .shrlimm_case2 n1 t1
  | e1 => .shrlimm_default e1

def shrlimm (e1 : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e1
  else if !(Int.ltu n Int64.iwordsize') then
    Eop Oshrl (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))
  else
    match shrlimm_match e1 with
    | .shrlimm_case1 n1 => Eop (Olongconst (Int64.shr' n1 n)) Enil
    | .shrlimm_case2 n1 t1 =>
        if Int.ltu (Int.add n n1) Int64.iwordsize' then
          Eop (Oshrlimm (Int.add n n1)) (Econs t1 Enil)
        else Eop (Oshrlimm n)
          (Econs (Eop (Oshrlimm n1) (Econs t1 Enil)) Enil)
    | .shrlimm_default e1 => Eop (Oshrlimm n) (Econs e1 Enil)

def shll (e1 e2 : expr) : expr :=
  match is_intconst e2 with
  | some n2 => shllimm e1 n2
  | none => Eop Oshll (Econs e1 (Econs e2 Enil))

def shrl (e1 e2 : expr) : expr :=
  match is_intconst e2 with
  | some n2 => shrlimm e1 n2
  | none => Eop Oshrl (Econs e1 (Econs e2 Enil))

def shrlu (e1 e2 : expr) : expr :=
  match is_intconst e2 with
  | some n2 => shrluimm e1 n2
  | none => Eop Oshrlu (Econs e1 (Econs e2 Enil))

/-! ## Address arithmetic -/

inductive addlimm_cases : expr → Type where
  | addlimm_case1 (m : CCInt64) : addlimm_cases (Eop (Olongconst m) Enil)
  | addlimm_case2 (addr : addressing) (args : exprlist) :
      addlimm_cases (Eop (Oleal addr) args)
  | addlimm_default (e : expr) : addlimm_cases e

export addlimm_cases (addlimm_case1 addlimm_case2 addlimm_default)

def addlimm_match (e : expr) : addlimm_cases e :=
  match e with
  | Eop (Olongconst m) Enil => .addlimm_case1 m
  | Eop (Oleal addr) args => .addlimm_case2 addr args
  | e => .addlimm_default e

def addlimm (n : CCInt64) (e : expr) : expr :=
  if Int64.eq n Int64.zero then e
  else
    match addlimm_match e with
    | .addlimm_case1 m => longconst (Int64.add n m)
    | .addlimm_case2 addr args =>
        Eop (Oleal (offset_addressing_total addr (Int64.signed n))) args
    | .addlimm_default e => Eop (Oleal (Aindexed (Int64.signed n))) (Econs e Enil)

/-! ## Address addition -/

inductive addl_cases : expr → expr → Type where
  | addl_case1 (n1 : CCInt64) (t2 : expr) :
      addl_cases (Eop (Olongconst n1) Enil) t2
  | addl_case2 (t1 : expr) (n2 : CCInt64) :
      addl_cases t1 (Eop (Olongconst n2) Enil)
  | addl_case3 (n1 : Z) (t1 : expr) (n2 : Z) (t2 : expr) :
      addl_cases (Eop (Oleal (Aindexed n1)) (Econs t1 Enil))
        (Eop (Oleal (Aindexed n2)) (Econs t2 Enil))
  | addl_case4 (n1 : Z) (t1 : expr) (sc n2 : Z) (t2 : expr) :
      addl_cases (Eop (Oleal (Aindexed n1)) (Econs t1 Enil))
        (Eop (Oleal (Ascaled sc n2)) (Econs t2 Enil))
  | addl_case5 (sc n1 : Z) (t1 : expr) (n2 : Z) (t2 : expr) :
      addl_cases (Eop (Oleal (Ascaled sc n1)) (Econs t1 Enil))
        (Eop (Oleal (Aindexed n2)) (Econs t2 Enil))
  | addl_case6 (sc n : Z) (t1 t2 : expr) :
      addl_cases (Eop (Oleal (Ascaled sc n)) (Econs t1 Enil)) t2
  | addl_case7 (t1 : expr) (sc n : Z) (t2 : expr) :
      addl_cases t1 (Eop (Oleal (Ascaled sc n)) (Econs t2 Enil))
  | addl_case8 (n : Z) (t1 t2 : expr) :
      addl_cases (Eop (Oleal (Aindexed n)) (Econs t1 Enil)) t2
  | addl_case9 (t1 : expr) (n : Z) (t2 : expr) :
      addl_cases t1 (Eop (Oleal (Aindexed n)) (Econs t2 Enil))
  | addl_default (e1 e2 : expr) : addl_cases e1 e2

export addl_cases (addl_case1 addl_case2 addl_case3 addl_case4 addl_case5
  addl_case6 addl_case7 addl_case8 addl_case9 addl_default)

def addl_match (e1 e2 : expr) : addl_cases e1 e2 :=
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => .addl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => .addl_case2 t1 n2
  | Eop (Oleal (Aindexed n1)) (Econs t1 Enil),
      Eop (Oleal (Aindexed n2)) (Econs t2 Enil) => .addl_case3 n1 t1 n2 t2
  | Eop (Oleal (Aindexed n1)) (Econs t1 Enil),
      Eop (Oleal (Ascaled sc n2)) (Econs t2 Enil) => .addl_case4 n1 t1 sc n2 t2
  | Eop (Oleal (Ascaled sc n1)) (Econs t1 Enil),
      Eop (Oleal (Aindexed n2)) (Econs t2 Enil) => .addl_case5 sc n1 t1 n2 t2
  | Eop (Oleal (Ascaled sc n)) (Econs t1 Enil), t2 => .addl_case6 sc n t1 t2
  | t1, Eop (Oleal (Ascaled sc n)) (Econs t2 Enil) => .addl_case7 t1 sc n t2
  | Eop (Oleal (Aindexed n)) (Econs t1 Enil), t2 => .addl_case8 n t1 t2
  | t1, Eop (Oleal (Aindexed n)) (Econs t2 Enil) => .addl_case9 t1 n t2
  | e1, e2 => .addl_default e1 e2

def addl (e1 e2 : expr) : expr :=
  match addl_match e1 e2 with
  | .addl_case1 n1 t2 => addlimm n1 t2
  | .addl_case2 t1 n2 => addlimm n2 t1
  | .addl_case3 n1 t1 n2 t2 =>
      Eop (Oleal (Aindexed2 (zAdd n1 n2))) (Econs t1 (Econs t2 Enil))
  | .addl_case4 n1 t1 sc n2 t2 =>
      Eop (Oleal (Aindexed2scaled sc (zAdd n1 n2))) (Econs t1 (Econs t2 Enil))
  | .addl_case5 sc n1 t1 n2 t2 =>
      Eop (Oleal (Aindexed2scaled sc (zAdd n1 n2))) (Econs t2 (Econs t1 Enil))
  | .addl_case6 sc n t1 t2 =>
      Eop (Oleal (Aindexed2scaled sc n)) (Econs t2 (Econs t1 Enil))
  | .addl_case7 t1 sc n t2 =>
      Eop (Oleal (Aindexed2scaled sc n)) (Econs t1 (Econs t2 Enil))
  | .addl_case8 n t1 t2 =>
      Eop (Oleal (Aindexed2 n)) (Econs t1 (Econs t2 Enil))
  | .addl_case9 t1 n t2 =>
      Eop (Oleal (Aindexed2 n)) (Econs t1 (Econs t2 Enil))
  | .addl_default e1 e2 =>
      Eop (Oleal (Aindexed2 z0)) (Econs e1 (Econs e2 Enil))

def negl (e : expr) : expr :=
  match is_longconst e with
  | some n => longconst (Int64.neg n)
  | none => Eop Onegl (Econs e Enil)

/-! ## Subtraction -/

inductive subl_cases : expr → expr → Type where
  | subl_case1 (t1 : expr) (n2 : CCInt64) :
      subl_cases t1 (Eop (Olongconst n2) Enil)
  | subl_case2 (n1 : Z) (t1 : expr) (n2 : Z) (t2 : expr) :
      subl_cases (Eop (Oleal (Aindexed n1)) (Econs t1 Enil))
        (Eop (Oleal (Aindexed n2)) (Econs t2 Enil))
  | subl_case3 (n1 : Z) (t1 t2 : expr) :
      subl_cases (Eop (Oleal (Aindexed n1)) (Econs t1 Enil)) t2
  | subl_case4 (t1 : expr) (n2 : Z) (t2 : expr) :
      subl_cases t1 (Eop (Oleal (Aindexed n2)) (Econs t2 Enil))
  | subl_default (e1 e2 : expr) : subl_cases e1 e2

export subl_cases (subl_case1 subl_case2 subl_case3 subl_case4 subl_default)

def subl_match (e1 e2 : expr) : subl_cases e1 e2 :=
  match e1, e2 with
  | t1, Eop (Olongconst n2) Enil => .subl_case1 t1 n2
  | Eop (Oleal (Aindexed n1)) (Econs t1 Enil),
      Eop (Oleal (Aindexed n2)) (Econs t2 Enil) => .subl_case2 n1 t1 n2 t2
  | Eop (Oleal (Aindexed n1)) (Econs t1 Enil), t2 => .subl_case3 n1 t1 t2
  | t1, Eop (Oleal (Aindexed n2)) (Econs t2 Enil) => .subl_case4 t1 n2 t2
  | e1, e2 => .subl_default e1 e2

def subl (e1 e2 : expr) : expr :=
  match subl_match e1 e2 with
  | .subl_case1 t1 n2 => addlimm (Int64.neg n2) t1
  | .subl_case2 n1 t1 n2 t2 =>
      addlimm (Int64.repr (zSub n1 n2)) (Eop Osubl (Econs t1 (Econs t2 Enil)))
  | .subl_case3 n1 t1 t2 =>
      addlimm (Int64.repr n1) (Eop Osubl (Econs t1 (Econs t2 Enil)))
  | .subl_case4 t1 n2 t2 =>
      addlimm (Int64.repr (zOpp n2)) (Eop Osubl (Econs t1 (Econs t2 Enil)))
  | .subl_default e1 e2 => Eop Osubl (Econs e1 (Econs e2 Enil))

/-! ## Multiplication -/

def mullimm_base (n1 : CCInt64) (e2 : expr) : expr :=
  match Int64.one_bits' n1 with
  | i :: [] => shllimm e2 i
  | i :: j :: [] =>
      Elet e2 (addl (shllimm (Eletvar 0) i) (shllimm (Eletvar 0) j))
  | _ => Eop (Omullimm n1) (Econs e2 Enil)

inductive mullimm_cases : expr → Type where
  | mullimm_case1 (n2 : CCInt64) : mullimm_cases (Eop (Olongconst n2) Enil)
  | mullimm_case2 (n2 : Z) (t2 : expr) :
      mullimm_cases (Eop (Oleal (Aindexed n2)) (Econs t2 Enil))
  | mullimm_default (e2 : expr) : mullimm_cases e2

export mullimm_cases (mullimm_case1 mullimm_case2 mullimm_default)

def mullimm_match (e2 : expr) : mullimm_cases e2 :=
  match e2 with
  | Eop (Olongconst n2) Enil => .mullimm_case1 n2
  | Eop (Oleal (Aindexed n2)) (Econs t2 Enil) => .mullimm_case2 n2 t2
  | e2 => .mullimm_default e2

def mullimm (n1 : CCInt64) (e2 : expr) : expr :=
  if Int64.eq n1 Int64.zero then longconst Int64.zero
  else if Int64.eq n1 Int64.one then e2
  else
    match mullimm_match e2 with
    | .mullimm_case1 n2 => longconst (Int64.mul n1 n2)
    | .mullimm_case2 n2 t2 =>
        addlimm (Int64.mul n1 (Int64.repr n2)) (mullimm_base n1 t2)
    | .mullimm_default e2 => mullimm_base n1 e2

inductive mull_cases : expr → expr → Type where
  | mull_case1 (n1 : CCInt64) (t2 : expr) :
      mull_cases (Eop (Olongconst n1) Enil) t2
  | mull_case2 (t1 : expr) (n2 : CCInt64) :
      mull_cases t1 (Eop (Olongconst n2) Enil)
  | mull_default (e1 e2 : expr) : mull_cases e1 e2

export mull_cases (mull_case1 mull_case2 mull_default)

def mull_match (e1 e2 : expr) : mull_cases e1 e2 :=
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => .mull_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => .mull_case2 t1 n2
  | e1, e2 => .mull_default e1 e2

def mull (e1 e2 : expr) : expr :=
  match mull_match e1 e2 with
  | .mull_case1 n1 t2 => mullimm n1 t2
  | .mull_case2 t1 n2 => mullimm n2 t1
  | .mull_default e1 e2 => Eop Omull (Econs e1 (Econs e2 Enil))

def mullhu (e1 : expr) (n2 : CCInt64) : expr :=
  Eop Omullhu (Econs e1 (Econs (longconst n2) Enil))

def mullhs (e1 : expr) (n2 : CCInt64) : expr :=
  Eop Omullhs (Econs e1 (Econs (longconst n2) Enil))

def shrxlimm (e : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e else Eop (Oshrxlimm n) (Econs e Enil)

def divlu_base (e1 e2 : expr) : expr := Eop Odivlu (Econs e1 (Econs e2 Enil))
def modlu_base (e1 e2 : expr) : expr := Eop Omodlu (Econs e1 (Econs e2 Enil))
def divls_base (e1 e2 : expr) : expr := Eop Odivl (Econs e1 (Econs e2 Enil))
def modls_base (e1 e2 : expr) : expr := Eop Omodl (Econs e1 (Econs e2 Enil))

/-! ## Comparisons and floating conversions -/

def cmplu (c : comparison) (e1 e2 : expr) : expr :=
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 =>
      Eop (Ointconst (if int64Cmpu c n1 n2 then Int.one else Int.zero)) Enil
  | some n1, none => Eop (Ocmp (Ccompluimm (swap_comparison c) n1)) (Econs e2 Enil)
  | none, some n2 => Eop (Ocmp (Ccompluimm c n2)) (Econs e1 Enil)
  | none, none => Eop (Ocmp (Ccomplu c)) (Econs e1 (Econs e2 Enil))

def cmpl (c : comparison) (e1 e2 : expr) : expr :=
  match is_longconst e1, is_longconst e2 with
  | some n1, some n2 =>
      Eop (Ointconst (if int64Cmp c n1 n2 then Int.one else Int.zero)) Enil
  | some n1, none => Eop (Ocmp (Ccomplimm (swap_comparison c) n1)) (Econs e2 Enil)
  | none, some n2 => Eop (Ocmp (Ccomplimm c n2)) (Econs e1 Enil)
  | none, none => Eop (Ocmp (Ccompl c)) (Econs e1 (Econs e2 Enil))

def longoffloat (e : expr) : expr := Eop Olongoffloat (Econs e Enil)
def floatoflong (e : expr) : expr := Eop Ofloatoflong (Econs e Enil)
def longofsingle (e : expr) : expr := Eop Olongofsingle (Econs e Enil)
def singleoflong (e : expr) : expr := Eop Osingleoflong (Econs e Enil)

end CompCert4Lean.X86.SelectLong
