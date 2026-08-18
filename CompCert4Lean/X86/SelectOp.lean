import CompCert4Lean.Backend.CminorSel
import CompCert4Lean.Lib.Zbits
import CompCert4Lean.X86.Builtins1

/-!
# x86 instruction-selection smart constructors

Definition-bearing translation of CompCert's `x86/SelectOp.vp`.  The generated
`Nondetfunction` case surfaces are retained as ordinary Lean case classifiers.
The extracted relocation oracle is represented by the accepted explicit,
immutable Linux ELF relocation context.
-/

namespace CompCert4Lean.X86.SelectOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Floats
open CompCert4Lean.Backend.CminorSel
open CompCert4Lean.X86.Op

private abbrev CCInt := CompCert4Lean.Lib.Integers.int
private abbrev CCInt64 := CompCert4Lean.Lib.Integers.int64
private abbrev Ptrofs := CompCert4Lean.Lib.Integers.ptrofs
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison
private abbrev op_addressing := CompCert4Lean.X86.Op.addressing
private abbrev z0 : Z := .Z0
private abbrev z8 : Z := ZArith.BinInt.Z.of_nat 8
private abbrev z16 : Z := ZArith.BinInt.Z.of_nat 16
private abbrev z255 : Z := ZArith.BinInt.Z.of_nat 255
private abbrev z65535 : Z := ZArith.BinInt.Z.of_nat 65535
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zSub := ZArith.BinInt.Z.sub
private abbrev zOpp := ZArith.BinInt.Z.opp

private def zltBool (x y : Z) : Bool :=
  match CompCert4Lean.Lib.Coqlib.zlt x y with
  | .left _ => true
  | .right _ => false

namespace Int

private abbrev repr := CompCert4Lean.Lib.Integers.Int.repr
private abbrev unsigned := CompCert4Lean.Lib.Integers.Int.unsigned
private abbrev signed := CompCert4Lean.Lib.Integers.Int.signed
private abbrev zero := CompCert4Lean.Lib.Integers.Int.zero
private abbrev one := CompCert4Lean.Lib.Integers.Int.one
private abbrev mone := CompCert4Lean.Lib.Integers.Int.mone
private abbrev wordsize := CompCert4Lean.Lib.Integers.Int.wordsize
private abbrev iwordsize := CompCert4Lean.Lib.Integers.Int.iwordsize
private abbrev eq := CompCert4Lean.Lib.Integers.Int.eq
private abbrev ltu := CompCert4Lean.Lib.Integers.Int.ltu
private abbrev neg := CompCert4Lean.Lib.Integers.Int.neg
private abbrev add := CompCert4Lean.Lib.Integers.Int.add
private abbrev mul := CompCert4Lean.Lib.Integers.Int.mul
private abbrev and := CompCert4Lean.Lib.Integers.Int.and
private abbrev or := CompCert4Lean.Lib.Integers.Int.or
private abbrev xor := CompCert4Lean.Lib.Integers.Int.xor
private abbrev not := CompCert4Lean.Lib.Integers.Int.not
private abbrev shl := CompCert4Lean.Lib.Integers.Int.shl
private abbrev shru := CompCert4Lean.Lib.Integers.Int.shru
private abbrev shr := CompCert4Lean.Lib.Integers.Int.shr
private abbrev zero_ext := CompCert4Lean.Lib.Integers.Int.zero_ext

private def sign_ext (n : Z) (x : CCInt) : CCInt :=
  let modulus := ZArith.Zpower.two_p n
  let residue := ZArith.BinInt.Z.modulo (unsigned x) modulus
  if zltBool (ZArith.Zpower.two_p (zSub n (ZArith.BinInt.Z.of_nat 1))) residue then
    repr (zSub residue modulus)
  else
    repr residue

end Int

private def intOneBits (x : CCInt) : List CCInt :=
  List.map Int.repr
    (CompCert4Lean.Lib.Zbits.Z_one_bits Int.wordsize (Int.unsigned x) z0)

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

private def intCmp (c : comparison) (x y : CCInt) : Bool :=
  zCmp c (Int.signed x) (Int.signed y)

private def intCmpu (c : comparison) (x y : CCInt) : Bool :=
  zCmp c (Int.unsigned x) (Int.unsigned y)

/-! ## Explicit relocation service -/

inductive StorageClass : Type where
  | storageDefault
  | storageExtern
  | storageStatic
deriving DecidableEq

structure SymbolLinkageFacts : Type where
  storage : StorageClass
  definedHere : Bool
  size : Option _root_.Int64

structure RelocationContext : Type where
  pic : Bool
  pie : Bool
  common : Bool
  facts : ident -> Option SymbolLinkageFacts

private def symbolIsStatic : Option SymbolLinkageFacts -> Bool
  | some facts => facts.storage == .storageStatic
  | none => false

private def symbolIsExternal (common : Bool) : Option SymbolLinkageFacts -> Bool
  | none => true
  | some facts =>
      if facts.definedHere then false
      else if facts.storage == .storageStatic then false
      else
        match facts.storage, facts.size with
        | .storageDefault, some _ => common
        | _, _ => true

def symbol_is_relocatable (ctx : RelocationContext) (id : ident) : Bool :=
  if ctx.pic then
    !(symbolIsStatic (ctx.facts id))
  else if ctx.pie then
    symbolIsExternal ctx.common (ctx.facts id)
  else
    false

def Olea_ptr (a : addressing) : operation :=
  if CompCert4Lean.X86_64.Archi.ptr64 then Oleal a else Olea a

def addrsymbol (ctx : RelocationContext) (id : ident) (ofs : Ptrofs) : expr :=
  if symbol_is_relocatable ctx id then
    if Ptrofs.eq ofs Ptrofs.zero then
      Eop (Oindirectsymbol id) Enil
    else
      Eop (Olea_ptr (Aindexed (Ptrofs.unsigned ofs)))
        (Econs (Eop (Oindirectsymbol id) Enil) Enil)
  else
    Eop (Olea_ptr (Aglobal id ofs)) Enil

def addrstack (ofs : Ptrofs) : expr :=
  Eop (Olea_ptr (Ainstack ofs)) Enil

/-! ## Integer logical negation -/

inductive notint_cases : Type where
  | notint_case1 (n : CCInt)
  | notint_case2 (n : CCInt) (e1 : expr)
  | notint_default (e : expr)

export notint_cases (notint_case1 notint_case2 notint_default)

def notint_match (e : expr) : notint_cases :=
  match e with
  | Eop (Ointconst n) Enil => .notint_case1 n
  | Eop (Oxorimm n) (Econs e1 Enil) => .notint_case2 n e1
  | _ => .notint_default e

def notint (e : expr) : expr :=
  match notint_match e with
  | .notint_case1 n => Eop (Ointconst (Int.not n)) Enil
  | .notint_case2 n e1 => Eop (Oxorimm (Int.not n)) (Econs e1 Enil)
  | .notint_default e => Eop Onot (Econs e Enil)

/-! ## Integer addition and pointer addition -/

inductive addimm_cases : Type where
  | addimm_case1 (m : CCInt)
  | addimm_case2 (addr : addressing) (args : exprlist)
  | addimm_default (e : expr)

export addimm_cases (addimm_case1 addimm_case2 addimm_default)

def addimm_match (e : expr) : addimm_cases :=
  match e with
  | Eop (Ointconst m) Enil => .addimm_case1 m
  | Eop (Olea addr) args => .addimm_case2 addr args
  | _ => .addimm_default e

def addimm (n : CCInt) (e : expr) : expr :=
  if Int.eq n Int.zero then e
  else
    match addimm_match e with
    | .addimm_case1 m => Eop (Ointconst (Int.add n m)) Enil
    | .addimm_case2 addr args =>
        Eop (Olea (offset_addressing_total addr (Int.signed n))) args
    | .addimm_default e => Eop (Olea (Aindexed (Int.signed n))) (Econs e Enil)

inductive add_cases : Type where
  | add_case1 (n1 : CCInt) (t2 : expr)
  | add_case2 (t1 : expr) (n2 : CCInt)
  | add_case3 (n1 : Z) (t1 : expr) (n2 : Z) (t2 : expr)
  | add_case4 (n1 : Z) (t1 : expr) (sc n2 : Z) (t2 : expr)
  | add_case5 (sc n1 : Z) (t1 : expr) (n2 : Z) (t2 : expr)
  | add_case6 (n1 : Z) (t1 : expr) (id : ident) (ofs : Ptrofs)
  | add_case7 (id : ident) (ofs : Ptrofs) (n2 : Z) (t2 : expr)
  | add_case8 (sc n1 : Z) (t1 : expr) (id : ident) (ofs : Ptrofs)
  | add_case9 (id : ident) (ofs : Ptrofs) (sc n2 : Z) (t2 : expr)
  | add_case10 (sc n : Z) (t1 t2 : expr)
  | add_case11 (t1 : expr) (sc n : Z) (t2 : expr)
  | add_case12 (n : Z) (t1 t2 : expr)
  | add_case13 (t1 : expr) (n : Z) (t2 : expr)
  | add_default (e1 e2 : expr)

export add_cases (add_case1 add_case2 add_case3 add_case4 add_case5 add_case6
  add_case7 add_case8 add_case9 add_case10 add_case11 add_case12 add_case13 add_default)

def add_match (e1 e2 : expr) : add_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .add_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .add_case2 t1 n2
  | Eop (Olea (Aindexed n1)) (Econs t1 Enil),
      Eop (Olea (Aindexed n2)) (Econs t2 Enil) => .add_case3 n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (Econs t1 Enil),
      Eop (Olea (Ascaled sc n2)) (Econs t2 Enil) => .add_case4 n1 t1 sc n2 t2
  | Eop (Olea (Ascaled sc n1)) (Econs t1 Enil),
      Eop (Olea (Aindexed n2)) (Econs t2 Enil) => .add_case5 sc n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (Econs t1 Enil), Eop (Olea (Aglobal id ofs)) Enil =>
      .add_case6 n1 t1 id ofs
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Aindexed n2)) (Econs t2 Enil) =>
      .add_case7 id ofs n2 t2
  | Eop (Olea (Ascaled sc n1)) (Econs t1 Enil), Eop (Olea (Aglobal id ofs)) Enil =>
      .add_case8 sc n1 t1 id ofs
  | Eop (Olea (Aglobal id ofs)) Enil, Eop (Olea (Ascaled sc n2)) (Econs t2 Enil) =>
      .add_case9 id ofs sc n2 t2
  | Eop (Olea (Ascaled sc n)) (Econs t1 Enil), t2 => .add_case10 sc n t1 t2
  | t1, Eop (Olea (Ascaled sc n)) (Econs t2 Enil) => .add_case11 t1 sc n t2
  | Eop (Olea (Aindexed n)) (Econs t1 Enil), t2 => .add_case12 n t1 t2
  | t1, Eop (Olea (Aindexed n)) (Econs t2 Enil) => .add_case13 t1 n t2
  | _, _ => .add_default e1 e2

def add (e1 e2 : expr) : expr :=
  match add_match e1 e2 with
  | .add_case1 n1 t2 => addimm n1 t2
  | .add_case2 t1 n2 => addimm n2 t1
  | .add_case3 n1 t1 n2 t2 =>
      Eop (Olea (Aindexed2 (zAdd n1 n2))) (Econs t1 (Econs t2 Enil))
  | .add_case4 n1 t1 sc n2 t2 =>
      Eop (Olea (Aindexed2scaled sc (zAdd n1 n2))) (Econs t1 (Econs t2 Enil))
  | .add_case5 sc n1 t1 n2 t2 =>
      Eop (Olea (Aindexed2scaled sc (zAdd n1 n2))) (Econs t2 (Econs t1 Enil))
  | .add_case6 n1 t1 id ofs =>
      Eop (Olea (Abased id (Ptrofs.add ofs (Ptrofs.repr n1)))) (Econs t1 Enil)
  | .add_case7 id ofs n2 t2 =>
      Eop (Olea (Abased id (Ptrofs.add ofs (Ptrofs.repr n2)))) (Econs t2 Enil)
  | .add_case8 sc n1 t1 id ofs =>
      Eop (Olea (Abasedscaled sc id (Ptrofs.add ofs (Ptrofs.repr n1)))) (Econs t1 Enil)
  | .add_case9 id ofs sc n2 t2 =>
      Eop (Olea (Abasedscaled sc id (Ptrofs.add ofs (Ptrofs.repr n2)))) (Econs t2 Enil)
  | .add_case10 sc n t1 t2 =>
      Eop (Olea (Aindexed2scaled sc n)) (Econs t2 (Econs t1 Enil))
  | .add_case11 t1 sc n t2 =>
      Eop (Olea (Aindexed2scaled sc n)) (Econs t1 (Econs t2 Enil))
  | .add_case12 n t1 t2 => Eop (Olea (Aindexed2 n)) (Econs t1 (Econs t2 Enil))
  | .add_case13 t1 n t2 => Eop (Olea (Aindexed2 n)) (Econs t1 (Econs t2 Enil))
  | .add_default e1 e2 => Eop (Olea (Aindexed2 z0)) (Econs e1 (Econs e2 Enil))

/-! ## Opposite and subtraction -/

inductive negint_cases : Type where
  | negint_case1 (n : CCInt)
  | negint_default (e : expr)

export negint_cases (negint_case1 negint_default)

def negint_match (e : expr) : negint_cases :=
  match e with
  | Eop (Ointconst n) Enil => .negint_case1 n
  | _ => .negint_default e

def negint (e : expr) : expr :=
  match negint_match e with
  | .negint_case1 n => Eop (Ointconst (Int.neg n)) Enil
  | .negint_default e => Eop Oneg (Econs e Enil)

inductive sub_cases : Type where
  | sub_case1 (t1 : expr) (n2 : CCInt)
  | sub_case2 (n1 : Z) (t1 : expr) (n2 : Z) (t2 : expr)
  | sub_case3 (n1 : Z) (t1 t2 : expr)
  | sub_case4 (t1 : expr) (n2 : Z) (t2 : expr)
  | sub_default (e1 e2 : expr)

export sub_cases (sub_case1 sub_case2 sub_case3 sub_case4 sub_default)

def sub_match (e1 e2 : expr) : sub_cases :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil => .sub_case1 t1 n2
  | Eop (Olea (Aindexed n1)) (Econs t1 Enil),
      Eop (Olea (Aindexed n2)) (Econs t2 Enil) => .sub_case2 n1 t1 n2 t2
  | Eop (Olea (Aindexed n1)) (Econs t1 Enil), t2 => .sub_case3 n1 t1 t2
  | t1, Eop (Olea (Aindexed n2)) (Econs t2 Enil) => .sub_case4 t1 n2 t2
  | _, _ => .sub_default e1 e2

def sub (e1 e2 : expr) : expr :=
  match sub_match e1 e2 with
  | .sub_case1 t1 n2 => addimm (Int.neg n2) t1
  | .sub_case2 n1 t1 n2 t2 =>
      addimm (Int.repr (zSub n1 n2)) (Eop Osub (Econs t1 (Econs t2 Enil)))
  | .sub_case3 n1 t1 t2 =>
      addimm (Int.repr n1) (Eop Osub (Econs t1 (Econs t2 Enil)))
  | .sub_case4 t1 n2 t2 =>
      addimm (Int.repr (zOpp n2)) (Eop Osub (Econs t1 (Econs t2 Enil)))
  | .sub_default e1 e2 => Eop Osub (Econs e1 (Econs e2 Enil))

/-! ## Shifts and multiplication -/

def shift_is_scale (n : CCInt) : Bool :=
  Int.eq n (Int.repr (ZArith.BinInt.Z.of_nat 1)) ||
    Int.eq n (Int.repr (ZArith.BinInt.Z.of_nat 2)) ||
    Int.eq n (Int.repr (ZArith.BinInt.Z.of_nat 3))

inductive shlimm_cases : Type where
  | shlimm_case1 (n1 : CCInt)
  | shlimm_case2 (n1 : CCInt) (t1 : expr)
  | shlimm_case3 (n1 : Z) (t1 : expr)
  | shlimm_default (e1 : expr)

export shlimm_cases (shlimm_case1 shlimm_case2 shlimm_case3 shlimm_default)

def shlimm_match (e1 : expr) : shlimm_cases :=
  match e1 with
  | Eop (Ointconst n1) Enil => .shlimm_case1 n1
  | Eop (Oshlimm n1) (Econs t1 Enil) => .shlimm_case2 n1 t1
  | Eop (Olea (Aindexed n1)) (Econs t1 Enil) => .shlimm_case3 n1 t1
  | _ => .shlimm_default e1

def shlimm (e1 : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e1
  else if !(Int.ltu n Int.iwordsize) then Eop Oshl (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))
  else
    match shlimm_match e1 with
    | .shlimm_case1 n1 => Eop (Ointconst (Int.shl n1 n)) Enil
    | .shlimm_case2 n1 t1 =>
        if Int.ltu (Int.add n n1) Int.iwordsize then
          Eop (Oshlimm (Int.add n n1)) (Econs t1 Enil)
        else Eop (Oshlimm n) (Econs e1 Enil)
    | .shlimm_case3 n1 t1 =>
        if shift_is_scale n then
          Eop (Olea (Ascaled (Int.unsigned (Int.shl Int.one n))
            (Int.unsigned (Int.shl (Int.repr n1) n)))) (Econs t1 Enil)
        else Eop (Oshlimm n) (Econs e1 Enil)
    | .shlimm_default e1 =>
        if shift_is_scale n then
          Eop (Olea (Ascaled (Int.unsigned (Int.shl Int.one n)) z0)) (Econs e1 Enil)
        else Eop (Oshlimm n) (Econs e1 Enil)

inductive shruimm_cases : Type where
  | shruimm_case1 (n1 : CCInt)
  | shruimm_case2 (n1 : CCInt) (t1 : expr)
  | shruimm_default (e1 : expr)

export shruimm_cases (shruimm_case1 shruimm_case2 shruimm_default)

def shruimm_match (e1 : expr) : shruimm_cases :=
  match e1 with
  | Eop (Ointconst n1) Enil => .shruimm_case1 n1
  | Eop (Oshruimm n1) (Econs t1 Enil) => .shruimm_case2 n1 t1
  | _ => .shruimm_default e1

def shruimm (e1 : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e1
  else if !(Int.ltu n Int.iwordsize) then Eop Oshru (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))
  else
    match shruimm_match e1 with
    | .shruimm_case1 n1 => Eop (Ointconst (Int.shru n1 n)) Enil
    | .shruimm_case2 n1 t1 =>
        if Int.ltu (Int.add n n1) Int.iwordsize then
          Eop (Oshruimm (Int.add n n1)) (Econs t1 Enil)
        else Eop (Oshruimm n) (Econs e1 Enil)
    | .shruimm_default e1 => Eop (Oshruimm n) (Econs e1 Enil)

inductive shrimm_cases : Type where
  | shrimm_case1 (n1 : CCInt)
  | shrimm_case2 (n1 : CCInt) (t1 : expr)
  | shrimm_default (e1 : expr)

export shrimm_cases (shrimm_case1 shrimm_case2 shrimm_default)

def shrimm_match (e1 : expr) : shrimm_cases :=
  match e1 with
  | Eop (Ointconst n1) Enil => .shrimm_case1 n1
  | Eop (Oshrimm n1) (Econs t1 Enil) => .shrimm_case2 n1 t1
  | _ => .shrimm_default e1

def shrimm (e1 : expr) (n : CCInt) : expr :=
  if Int.eq n Int.zero then e1
  else if !(Int.ltu n Int.iwordsize) then Eop Oshr (Econs e1 (Econs (Eop (Ointconst n) Enil) Enil))
  else
    match shrimm_match e1 with
    | .shrimm_case1 n1 => Eop (Ointconst (Int.shr n1 n)) Enil
    | .shrimm_case2 n1 t1 =>
        if Int.ltu (Int.add n n1) Int.iwordsize then
          Eop (Oshrimm (Int.add n n1)) (Econs t1 Enil)
        else Eop (Oshrimm n) (Econs e1 Enil)
    | .shrimm_default e1 => Eop (Oshrimm n) (Econs e1 Enil)

def mulimm_base (n1 : CCInt) (e2 : expr) : expr :=
  match intOneBits n1 with
  | [i] => shlimm e2 i
  | [i, j] =>
      Elet e2 (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ => Eop (Omulimm n1) (Econs e2 Enil)

inductive mulimm_cases : Type where
  | mulimm_case1 (n2 : CCInt)
  | mulimm_case2 (n2 : Z) (t2 : expr)
  | mulimm_default (e2 : expr)

export mulimm_cases (mulimm_case1 mulimm_case2 mulimm_default)

def mulimm_match (e2 : expr) : mulimm_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .mulimm_case1 n2
  | Eop (Olea (Aindexed n2)) (Econs t2 Enil) => .mulimm_case2 n2 t2
  | _ => .mulimm_default e2

def mulimm (n1 : CCInt) (e2 : expr) : expr :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.one then e2
  else
    match mulimm_match e2 with
    | .mulimm_case1 n2 => Eop (Ointconst (Int.mul n1 n2)) Enil
    | .mulimm_case2 n2 t2 => addimm (Int.mul n1 (Int.repr n2)) (mulimm_base n1 t2)
    | .mulimm_default e2 => mulimm_base n1 e2

inductive mul_cases : Type where
  | mul_case1 (n1 : CCInt) (t2 : expr)
  | mul_case2 (t1 : expr) (n2 : CCInt)
  | mul_default (e1 e2 : expr)

export mul_cases (mul_case1 mul_case2 mul_default)

def mul_match (e1 e2 : expr) : mul_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .mul_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .mul_case2 t1 n2
  | _, _ => .mul_default e1 e2

def mul (e1 e2 : expr) : expr :=
  match mul_match e1 e2 with
  | .mul_case1 n1 t2 => mulimm n1 t2
  | .mul_case2 t1 n2 => mulimm n2 t1
  | .mul_default e1 e2 => Eop Omul (Econs e1 (Econs e2 Enil))

def mulhs (e1 e2 : expr) : expr := Eop Omulhs (Econs e1 (Econs e2 Enil))
def mulhu (e1 e2 : expr) : expr := Eop Omulhu (Econs e1 (Econs e2 Enil))

/-! ## Bitwise operations -/

inductive andimm_cases : Type where
  | andimm_case1 (n2 : CCInt)
  | andimm_case2 (n2 : CCInt) (t2 : expr)
  | andimm_case3 (t2 : expr)
  | andimm_case4 (t2 : expr)
  | andimm_default (e2 : expr)

export andimm_cases (andimm_case1 andimm_case2 andimm_case3 andimm_case4 andimm_default)

def andimm_match (e2 : expr) : andimm_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .andimm_case1 n2
  | Eop (Oandimm n2) (Econs t2 Enil) => .andimm_case2 n2 t2
  | Eop Ocast8unsigned (Econs t2 Enil) => .andimm_case3 t2
  | Eop Ocast16unsigned (Econs t2 Enil) => .andimm_case4 t2
  | _ => .andimm_default e2

def andimm (n1 : CCInt) (e2 : expr) : expr :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.mone then e2
  else
    match andimm_match e2 with
    | .andimm_case1 n2 => Eop (Ointconst (Int.and n1 n2)) Enil
    | .andimm_case2 n2 t2 => Eop (Oandimm (Int.and n1 n2)) (Econs t2 Enil)
    | .andimm_case3 t2 => Eop (Oandimm (Int.and n1 (Int.repr z255))) (Econs t2 Enil)
    | .andimm_case4 t2 => Eop (Oandimm (Int.and n1 (Int.repr z65535))) (Econs t2 Enil)
    | .andimm_default e2 => Eop (Oandimm n1) (Econs e2 Enil)

inductive and_cases : Type where
  | and_case1 (n1 : CCInt) (t2 : expr)
  | and_case2 (t1 : expr) (n2 : CCInt)
  | and_default (e1 e2 : expr)

export and_cases (and_case1 and_case2 and_default)

def and_match (e1 e2 : expr) : and_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .and_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .and_case2 t1 n2
  | _, _ => .and_default e1 e2

def and (e1 e2 : expr) : expr :=
  match and_match e1 e2 with
  | .and_case1 n1 t2 => andimm n1 t2
  | .and_case2 t1 n2 => andimm n2 t1
  | .and_default e1 e2 => Eop Oand (Econs e1 (Econs e2 Enil))

inductive orimm_cases : Type where
  | orimm_case1 (n2 : CCInt)
  | orimm_case2 (n2 : CCInt) (t2 : expr)
  | orimm_default (e2 : expr)

export orimm_cases (orimm_case1 orimm_case2 orimm_default)

def orimm_match (e2 : expr) : orimm_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .orimm_case1 n2
  | Eop (Oorimm n2) (Econs t2 Enil) => .orimm_case2 n2 t2
  | _ => .orimm_default e2

def orimm (n1 : CCInt) (e2 : expr) : expr :=
  if Int.eq n1 Int.zero then e2
  else if Int.eq n1 Int.mone then Eop (Ointconst Int.mone) Enil
  else
    match orimm_match e2 with
    | .orimm_case1 n2 => Eop (Ointconst (Int.or n1 n2)) Enil
    | .orimm_case2 n2 t2 => Eop (Oorimm (Int.or n1 n2)) (Econs t2 Enil)
    | .orimm_default e2 => Eop (Oorimm n1) (Econs e2 Enil)

def same_expr_pure (e1 e2 : expr) : Bool :=
  match e1, e2 with
  | Evar v1, Evar v2 => decide (v1 = v2)
  | _, _ => false

inductive or_cases : Type where
  | or_case1 (n1 : CCInt) (t2 : expr)
  | or_case2 (t1 : expr) (n2 : CCInt)
  | or_case3 (n1 : CCInt) (t1 : expr) (n2 : CCInt) (t2 : expr)
  | or_case4 (n2 : CCInt) (t2 : expr) (n1 : CCInt) (t1 : expr)
  | or_default (e1 e2 : expr)

export or_cases (or_case1 or_case2 or_case3 or_case4 or_default)

def or_match (e1 e2 : expr) : or_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .or_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .or_case2 t1 n2
  | Eop (Oshlimm n1) (Econs t1 Enil), Eop (Oshruimm n2) (Econs t2 Enil) =>
      .or_case3 n1 t1 n2 t2
  | Eop (Oshruimm n2) (Econs t2 Enil), Eop (Oshlimm n1) (Econs t1 Enil) =>
      .or_case4 n2 t2 n1 t1
  | _, _ => .or_default e1 e2

def or (e1 e2 : expr) : expr :=
  match or_match e1 e2 with
  | .or_case1 n1 t2 => orimm n1 t2
  | .or_case2 t1 n2 => orimm n2 t1
  | .or_case3 n1 t1 n2 t2 =>
      if Int.eq (Int.add n1 n2) Int.iwordsize then
        if same_expr_pure t1 t2 then Eop (Ororimm n2) (Econs t1 Enil)
        else Eop (Oshldimm n1) (Econs t1 (Econs t2 Enil))
      else Eop Oor (Econs e1 (Econs e2 Enil))
  | .or_case4 n2 t2 n1 t1 =>
      if Int.eq (Int.add n1 n2) Int.iwordsize then
        if same_expr_pure t1 t2 then Eop (Ororimm n2) (Econs t1 Enil)
        else Eop (Oshldimm n1) (Econs t1 (Econs t2 Enil))
      else Eop Oor (Econs e1 (Econs e2 Enil))
  | .or_default e1 e2 => Eop Oor (Econs e1 (Econs e2 Enil))

inductive xorimm_cases : Type where
  | xorimm_case1 (n2 : CCInt)
  | xorimm_case2 (n2 : CCInt) (t2 : expr)
  | xorimm_case3 (t2 : expr)
  | xorimm_default (e2 : expr)

export xorimm_cases (xorimm_case1 xorimm_case2 xorimm_case3 xorimm_default)

def xorimm_match (e2 : expr) : xorimm_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .xorimm_case1 n2
  | Eop (Oxorimm n2) (Econs t2 Enil) => .xorimm_case2 n2 t2
  | Eop Onot (Econs t2 Enil) => .xorimm_case3 t2
  | _ => .xorimm_default e2

def xorimm (n1 : CCInt) (e2 : expr) : expr :=
  if Int.eq n1 Int.zero then e2
  else
    match xorimm_match e2 with
    | .xorimm_case1 n2 => Eop (Ointconst (Int.xor n1 n2)) Enil
    | .xorimm_case2 n2 t2 => Eop (Oxorimm (Int.xor n1 n2)) (Econs t2 Enil)
    | .xorimm_case3 t2 => Eop (Oxorimm (Int.not n1)) (Econs t2 Enil)
    | .xorimm_default e2 => Eop (Oxorimm n1) (Econs e2 Enil)

inductive xor_cases : Type where
  | xor_case1 (n1 : CCInt) (t2 : expr)
  | xor_case2 (t1 : expr) (n2 : CCInt)
  | xor_default (e1 e2 : expr)

export xor_cases (xor_case1 xor_case2 xor_default)

def xor_match (e1 e2 : expr) : xor_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .xor_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .xor_case2 t1 n2
  | _, _ => .xor_default e1 e2

def xor (e1 e2 : expr) : expr :=
  match xor_match e1 e2 with
  | .xor_case1 n1 t2 => xorimm n1 t2
  | .xor_case2 t1 n2 => xorimm n2 t1
  | .xor_default e1 e2 => Eop Oxor (Econs e1 (Econs e2 Enil))

/-! ## Division, general shifts, and floating arithmetic -/

def divu_base (e1 e2 : expr) : expr := Eop Odivu (Econs e1 (Econs e2 Enil))
def modu_base (e1 e2 : expr) : expr := Eop Omodu (Econs e1 (Econs e2 Enil))
def divs_base (e1 e2 : expr) : expr := Eop Odiv (Econs e1 (Econs e2 Enil))
def mods_base (e1 e2 : expr) : expr := Eop Omod (Econs e1 (Econs e2 Enil))

def shrximm (e1 : expr) (n2 : CCInt) : expr :=
  if Int.eq n2 Int.zero then e1 else Eop (Oshrximm n2) (Econs e1 Enil)

inductive shl_cases : Type where
  | shl_case1 (n2 : CCInt)
  | shl_default (e2 : expr)

export shl_cases (shl_case1 shl_default)

def shl_match (e2 : expr) : shl_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .shl_case1 n2
  | _ => .shl_default e2

def shl (e1 e2 : expr) : expr :=
  match shl_match e2 with
  | .shl_case1 n2 => shlimm e1 n2
  | .shl_default e2 => Eop Oshl (Econs e1 (Econs e2 Enil))

inductive shr_cases : Type where
  | shr_case1 (n2 : CCInt)
  | shr_default (e2 : expr)

export shr_cases (shr_case1 shr_default)

def shr_match (e2 : expr) : shr_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .shr_case1 n2
  | _ => .shr_default e2

def shr (e1 e2 : expr) : expr :=
  match shr_match e2 with
  | .shr_case1 n2 => shrimm e1 n2
  | .shr_default e2 => Eop Oshr (Econs e1 (Econs e2 Enil))

inductive shru_cases : Type where
  | shru_case1 (n2 : CCInt)
  | shru_default (e2 : expr)

export shru_cases (shru_case1 shru_default)

def shru_match (e2 : expr) : shru_cases :=
  match e2 with
  | Eop (Ointconst n2) Enil => .shru_case1 n2
  | _ => .shru_default e2

def shru (e1 e2 : expr) : expr :=
  match shru_match e2 with
  | .shru_case1 n2 => shruimm e1 n2
  | .shru_default e2 => Eop Oshru (Econs e1 (Econs e2 Enil))

def negf (e : expr) : expr := Eop Onegf (Econs e Enil)
def absf (e : expr) : expr := Eop Oabsf (Econs e Enil)
def addf (e1 e2 : expr) : expr := Eop Oaddf (Econs e1 (Econs e2 Enil))
def subf (e1 e2 : expr) : expr := Eop Osubf (Econs e1 (Econs e2 Enil))
def mulf (e1 e2 : expr) : expr := Eop Omulf (Econs e1 (Econs e2 Enil))

def negfs (e : expr) : expr := Eop Onegfs (Econs e Enil)
def absfs (e : expr) : expr := Eop Oabsfs (Econs e Enil)
def addfs (e1 e2 : expr) : expr := Eop Oaddfs (Econs e1 (Econs e2 Enil))
def subfs (e1 e2 : expr) : expr := Eop Osubfs (Econs e1 (Econs e2 Enil))
def mulfs (e1 e2 : expr) : expr := Eop Omulfs (Econs e1 (Econs e2 Enil))

/-! ## Comparisons -/

inductive compimm_cases : Type where
  | compimm_case1 (c : comparison) (n1 : CCInt)
  | compimm_case2 (cond : condition) (el : exprlist)
  | compimm_case3 (cond : condition) (el : exprlist)
  | compimm_case4 (n1 : CCInt) (t1 : expr)
  | compimm_case5 (n1 : CCInt) (t1 : expr)
  | compimm_default (c : comparison) (e1 : expr)

export compimm_cases (compimm_case1 compimm_case2 compimm_case3 compimm_case4
  compimm_case5 compimm_default)

def compimm_match (c : comparison) (e1 : expr) : compimm_cases :=
  match c, e1 with
  | c, Eop (Ointconst n1) Enil => .compimm_case1 c n1
  | .Ceq, Eop (Ocmp cond) el => .compimm_case2 cond el
  | .Cne, Eop (Ocmp cond) el => .compimm_case3 cond el
  | .Ceq, Eop (Oandimm n1) (Econs t1 Enil) => .compimm_case4 n1 t1
  | .Cne, Eop (Oandimm n1) (Econs t1 Enil) => .compimm_case5 n1 t1
  | _, _ => .compimm_default c e1

def compimm (default : comparison -> CCInt -> condition)
    (sem : comparison -> CCInt -> CCInt -> Bool) (c : comparison)
    (e1 : expr) (n2 : CCInt) : expr :=
  match compimm_match c e1 with
  | .compimm_case1 c n1 =>
      Eop (Ointconst (if sem c n1 n2 then Int.one else Int.zero)) Enil
  | .compimm_case2 cond el =>
      if Int.eq n2 Int.zero then Eop (Ocmp (negate_condition cond)) el
      else if Int.eq n2 Int.one then Eop (Ocmp cond) el
      else Eop (Ointconst Int.zero) Enil
  | .compimm_case3 cond el =>
      if Int.eq n2 Int.zero then Eop (Ocmp cond) el
      else if Int.eq n2 Int.one then Eop (Ocmp (negate_condition cond)) el
      else Eop (Ointconst Int.one) Enil
  | .compimm_case4 n1 t1 =>
      if Int.eq n2 Int.zero then Eop (Ocmp (Cmaskzero n1)) (Econs t1 Enil)
      else Eop (Ocmp (default c n2)) (Econs e1 Enil)
  | .compimm_case5 n1 t1 =>
      if Int.eq n2 Int.zero then Eop (Ocmp (Cmasknotzero n1)) (Econs t1 Enil)
      else Eop (Ocmp (default c n2)) (Econs e1 Enil)
  | .compimm_default c e1 => Eop (Ocmp (default c n2)) (Econs e1 Enil)

inductive comp_cases : Type where
  | comp_case1 (n1 : CCInt) (t2 : expr)
  | comp_case2 (t1 : expr) (n2 : CCInt)
  | comp_default (e1 e2 : expr)

export comp_cases (comp_case1 comp_case2 comp_default)

def comp_match (e1 e2 : expr) : comp_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .comp_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .comp_case2 t1 n2
  | _, _ => .comp_default e1 e2

def comp (c : comparison) (e1 e2 : expr) : expr :=
  match comp_match e1 e2 with
  | .comp_case1 n1 t2 => compimm Ccompimm intCmp (swap_comparison c) t2 n1
  | .comp_case2 t1 n2 => compimm Ccompimm intCmp c t1 n2
  | .comp_default e1 e2 => Eop (Ocmp (Ccomp c)) (Econs e1 (Econs e2 Enil))

inductive compu_cases : Type where
  | compu_case1 (n1 : CCInt) (t2 : expr)
  | compu_case2 (t1 : expr) (n2 : CCInt)
  | compu_default (e1 e2 : expr)

export compu_cases (compu_case1 compu_case2 compu_default)

def compu_match (e1 e2 : expr) : compu_cases :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => .compu_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => .compu_case2 t1 n2
  | _, _ => .compu_default e1 e2

def compu (c : comparison) (e1 e2 : expr) : expr :=
  match compu_match e1 e2 with
  | .compu_case1 n1 t2 => compimm Ccompuimm intCmpu (swap_comparison c) t2 n1
  | .compu_case2 t1 n2 => compimm Ccompuimm intCmpu c t1 n2
  | .compu_default e1 e2 => Eop (Ocmp (Ccompu c)) (Econs e1 (Econs e2 Enil))

def compf (c : comparison) (e1 e2 : expr) : expr :=
  Eop (Ocmp (Ccompf c)) (Econs e1 (Econs e2 Enil))

def compfs (c : comparison) (e1 e2 : expr) : expr :=
  Eop (Ocmp (Ccompfs c)) (Econs e1 (Econs e2 Enil))

/-! ## Integer conversions and selection -/

inductive cast8unsigned_cases : Type where
  | cast8unsigned_case1 (n : CCInt)
  | cast8unsigned_case2 (n : CCInt) (t : expr)
  | cast8unsigned_default (e : expr)

export cast8unsigned_cases (cast8unsigned_case1 cast8unsigned_case2 cast8unsigned_default)

def cast8unsigned_match (e : expr) : cast8unsigned_cases :=
  match e with
  | Eop (Ointconst n) Enil => .cast8unsigned_case1 n
  | Eop (Oandimm n) (Econs t Enil) => .cast8unsigned_case2 n t
  | _ => .cast8unsigned_default e

def cast8unsigned (e : expr) : expr :=
  match cast8unsigned_match e with
  | .cast8unsigned_case1 n => Eop (Ointconst (Int.zero_ext z8 n)) Enil
  | .cast8unsigned_case2 n t => andimm (Int.and (Int.repr z255) n) t
  | .cast8unsigned_default e => Eop Ocast8unsigned (Econs e Enil)

inductive cast8signed_cases : Type where
  | cast8signed_case1 (n : CCInt)
  | cast8signed_default (e : expr)

export cast8signed_cases (cast8signed_case1 cast8signed_default)

def cast8signed_match (e : expr) : cast8signed_cases :=
  match e with
  | Eop (Ointconst n) Enil => .cast8signed_case1 n
  | _ => .cast8signed_default e

def cast8signed (e : expr) : expr :=
  match cast8signed_match e with
  | .cast8signed_case1 n => Eop (Ointconst (Int.sign_ext z8 n)) Enil
  | .cast8signed_default e => Eop Ocast8signed (Econs e Enil)

inductive cast16unsigned_cases : Type where
  | cast16unsigned_case1 (n : CCInt)
  | cast16unsigned_case2 (n : CCInt) (t : expr)
  | cast16unsigned_default (e : expr)

export cast16unsigned_cases (cast16unsigned_case1 cast16unsigned_case2 cast16unsigned_default)

def cast16unsigned_match (e : expr) : cast16unsigned_cases :=
  match e with
  | Eop (Ointconst n) Enil => .cast16unsigned_case1 n
  | Eop (Oandimm n) (Econs t Enil) => .cast16unsigned_case2 n t
  | _ => .cast16unsigned_default e

def cast16unsigned (e : expr) : expr :=
  match cast16unsigned_match e with
  | .cast16unsigned_case1 n => Eop (Ointconst (Int.zero_ext z16 n)) Enil
  | .cast16unsigned_case2 n t => andimm (Int.and (Int.repr z65535) n) t
  | .cast16unsigned_default e => Eop Ocast16unsigned (Econs e Enil)

inductive cast16signed_cases : Type where
  | cast16signed_case1 (n : CCInt)
  | cast16signed_default (e : expr)

export cast16signed_cases (cast16signed_case1 cast16signed_default)

def cast16signed_match (e : expr) : cast16signed_cases :=
  match e with
  | Eop (Ointconst n) Enil => .cast16signed_case1 n
  | _ => .cast16signed_default e

def cast16signed (e : expr) : expr :=
  match cast16signed_match e with
  | .cast16signed_case1 n => Eop (Ointconst (Int.sign_ext z16 n)) Enil
  | .cast16signed_default e => Eop Ocast16signed (Econs e Enil)

def select_supported (ty : typ) : Bool :=
  match ty with
  | .Tint => true
  | .Tlong => CompCert4Lean.X86_64.Archi.ptr64
  | _ => false

def select_swap (cond : condition) : Bool :=
  match cond with
  | .Ccompf .Cne | .Ccompfs .Cne | .Cnotcompf .Ceq | .Cnotcompfs .Ceq => true
  | _ => false

def select (ty : typ) (cond : condition) (args : exprlist) (e1 e2 : expr) : expr :=
  if select_swap cond then
    Eop (Osel (negate_condition cond) ty) (Econs e2 (Econs e1 args))
  else
    Eop (Osel cond ty) (Econs e1 (Econs e2 args))

/-! ## Floating-point conversions -/

def singleoffloat (e : expr) : expr := Eop Osingleoffloat (Econs e Enil)
def floatofsingle (e : expr) : expr := Eop Ofloatofsingle (Econs e Enil)
def intoffloat (e : expr) : expr := Eop Ointoffloat (Econs e Enil)

inductive floatofint_cases : Type where
  | floatofint_case1 (n : CCInt)
  | floatofint_default (e : expr)

export floatofint_cases (floatofint_case1 floatofint_default)

def floatofint_match (e : expr) : floatofint_cases :=
  match e with
  | Eop (Ointconst n) Enil => .floatofint_case1 n
  | _ => .floatofint_default e

def floatofint (e : expr) : expr :=
  match floatofint_match e with
  | .floatofint_case1 n => Eop (Ofloatconst (Float.of_int n)) Enil
  | .floatofint_default e => Eop Ofloatofint (Econs e Enil)

def intuoffloat (e : expr) : expr :=
  if CompCert4Lean.X86_64.Archi.splitlong then
    Elet e
      (Elet (Eop (Ofloatconst (Float.of_intu Float.ox8000_0000)) Enil)
        (Econdition
          (CEcond (Ccompf Clt) (Econs (Eletvar 1) (Econs (Eletvar 0) Enil)))
          (intoffloat (Eletvar 1))
          (addimm Float.ox8000_0000
            (intoffloat (subf (Eletvar 1) (Eletvar 0))))))
  else
    Eop Olowlong (Econs (Eop Olongoffloat (Econs e Enil)) Enil)

inductive floatofintu_cases : Type where
  | floatofintu_case1 (n : CCInt)
  | floatofintu_default (e : expr)

export floatofintu_cases (floatofintu_case1 floatofintu_default)

def floatofintu_match (e : expr) : floatofintu_cases :=
  match e with
  | Eop (Ointconst n) Enil => .floatofintu_case1 n
  | _ => .floatofintu_default e

def floatofintu (e : expr) : expr :=
  match floatofintu_match e with
  | .floatofintu_case1 n => Eop (Ofloatconst (Float.of_intu n)) Enil
  | .floatofintu_default e =>
      if CompCert4Lean.X86_64.Archi.splitlong then
        let f := Eop (Ofloatconst (Float.of_intu Float.ox8000_0000)) Enil
        Elet e
          (Econdition
            (CEcond (Ccompuimm Clt Float.ox8000_0000) (Econs (Eletvar 0) Enil))
            (floatofint (Eletvar 0))
            (addf
              (floatofint (addimm (Int.neg Float.ox8000_0000) (Eletvar 0))) f))
      else
        Eop Ofloatoflong (Econs (Eop Ocast32unsigned (Econs e Enil)) Enil)

def intofsingle (e : expr) : expr := Eop Ointofsingle (Econs e Enil)

inductive singleofint_cases : Type where
  | singleofint_case1 (n : CCInt)
  | singleofint_default (e : expr)

export singleofint_cases (singleofint_case1 singleofint_default)

def singleofint_match (e : expr) : singleofint_cases :=
  match e with
  | Eop (Ointconst n) Enil => .singleofint_case1 n
  | _ => .singleofint_default e

def singleofint (e : expr) : expr :=
  match singleofint_match e with
  | .singleofint_case1 n => Eop (Osingleconst (Float32.of_int n)) Enil
  | .singleofint_default e => Eop Osingleofint (Econs e Enil)

def intuofsingle (e : expr) : expr := intuoffloat (floatofsingle e)

inductive singleofintu_cases : Type where
  | singleofintu_case1 (n : CCInt)
  | singleofintu_default (e : expr)

export singleofintu_cases (singleofintu_case1 singleofintu_default)

def singleofintu_match (e : expr) : singleofintu_cases :=
  match e with
  | Eop (Ointconst n) Enil => .singleofintu_case1 n
  | _ => .singleofintu_default e

def singleofintu (e : expr) : expr :=
  match singleofintu_match e with
  | .singleofintu_case1 n => Eop (Osingleconst (Float32.of_intu n)) Enil
  | .singleofintu_default e => singleoffloat (floatofintu e)

/-! ## Addressing modes -/

inductive addressing_cases : Type where
  | addressing_case1 (addr : addressing) (args : exprlist)
  | addressing_case2 (addr : addressing) (args : exprlist)
  | addressing_default (e : expr)

export addressing_cases (addressing_case1 addressing_case2 addressing_default)

def addressing_match (e : expr) : addressing_cases :=
  match e with
  | Eop (Olea addr) args => .addressing_case1 addr args
  | Eop (Oleal addr) args => .addressing_case2 addr args
  | _ => .addressing_default e

def addressing (_chunk : memory_chunk) (e : expr) : addressing × exprlist :=
  match addressing_match e with
  | .addressing_case1 addr args =>
      if !CompCert4Lean.X86_64.Archi.ptr64 && addressing_valid addr then
        (addr, args)
      else (Aindexed z0, Econs e Enil)
  | .addressing_case2 addr args =>
      if CompCert4Lean.X86_64.Archi.ptr64 && addressing_valid addr then
        (addr, args)
      else (Aindexed z0, Econs e Enil)
  | .addressing_default e => (Aindexed z0, Econs e Enil)

/-! ## Builtin arguments -/

inductive builtin_arg_addr_cases : Type where
  | builtin_arg_addr_case1 (n : Z) (e1 : expr)
  | builtin_arg_addr_case2 (id : ident) (ofs : Ptrofs)
  | builtin_arg_addr_case3 (ofs : Ptrofs)
  | builtin_arg_addr_default (addr : op_addressing) (el : exprlist)

export builtin_arg_addr_cases (builtin_arg_addr_case1 builtin_arg_addr_case2
  builtin_arg_addr_case3 builtin_arg_addr_default)

def builtin_arg_addr_match (addr : op_addressing) (el : exprlist) : builtin_arg_addr_cases :=
  match addr, el with
  | Aindexed n, Econs e1 Enil => .builtin_arg_addr_case1 n e1
  | Aglobal id ofs, Enil => .builtin_arg_addr_case2 id ofs
  | Ainstack ofs, Enil => .builtin_arg_addr_case3 ofs
  | _, _ => .builtin_arg_addr_default addr el

def builtin_arg_addr (addr : op_addressing) (el : exprlist) : builtin_arg expr :=
  match builtin_arg_addr_match addr el with
  | .builtin_arg_addr_case1 n e1 =>
      BA_addptr (BA e1)
        (if CompCert4Lean.X86_64.Archi.ptr64 then BA_long (Int64.repr n)
         else BA_int (Int.repr n))
  | .builtin_arg_addr_case2 id ofs => BA_addrglobal id ofs
  | .builtin_arg_addr_case3 ofs => BA_addrstack ofs
  | .builtin_arg_addr_default addr el => BA (Eop (Olea_ptr addr) el)

inductive builtin_arg_cases : Type where
  | builtin_arg_case1 (n : CCInt)
  | builtin_arg_case2 (n : CCInt64)
  | builtin_arg_case3 (addr : op_addressing) (el : exprlist)
  | builtin_arg_case4 (addr : op_addressing) (el : exprlist)
  | builtin_arg_case5 (h l : CCInt)
  | builtin_arg_case6 (h l : expr)
  | builtin_arg_case7 (chunk : memory_chunk) (id : ident) (ofs : Ptrofs)
  | builtin_arg_case8 (chunk : memory_chunk) (ofs : Ptrofs)
  | builtin_arg_default (e : expr)

export builtin_arg_cases (builtin_arg_case1 builtin_arg_case2 builtin_arg_case3
  builtin_arg_case4 builtin_arg_case5 builtin_arg_case6 builtin_arg_case7
  builtin_arg_case8 builtin_arg_default)

def builtin_arg_match (e : expr) : builtin_arg_cases :=
  match e with
  | Eop (Ointconst n) Enil => .builtin_arg_case1 n
  | Eop (Olongconst n) Enil => .builtin_arg_case2 n
  | Eop (Olea addr) el => .builtin_arg_case3 addr el
  | Eop (Oleal addr) el => .builtin_arg_case4 addr el
  | Eop Omakelong
      (Econs (Eop (Ointconst h) Enil) (Econs (Eop (Ointconst l) Enil) Enil)) =>
      .builtin_arg_case5 h l
  | Eop Omakelong (Econs h (Econs l Enil)) => .builtin_arg_case6 h l
  | Eload chunk (Aglobal id ofs) Enil => .builtin_arg_case7 chunk id ofs
  | Eload chunk (Ainstack ofs) Enil => .builtin_arg_case8 chunk ofs
  | _ => .builtin_arg_default e

def builtin_arg (e : expr) : builtin_arg expr :=
  match builtin_arg_match e with
  | .builtin_arg_case1 n => BA_int n
  | .builtin_arg_case2 n => BA_long n
  | .builtin_arg_case3 addr el =>
      if CompCert4Lean.X86_64.Archi.ptr64 then BA e else builtin_arg_addr addr el
  | .builtin_arg_case4 addr el =>
      if CompCert4Lean.X86_64.Archi.ptr64 then builtin_arg_addr addr el else BA e
  | .builtin_arg_case5 h l => BA_long (Int64.ofwords h l)
  | .builtin_arg_case6 h l => BA_splitlong (BA h) (BA l)
  | .builtin_arg_case7 chunk id ofs => BA_loadglobal chunk id ofs
  | .builtin_arg_case8 chunk ofs => BA_loadstack chunk ofs
  | .builtin_arg_default e => BA e

def platform_builtin (b : CompCert4Lean.X86.Builtins1.platform_builtin)
    (args : exprlist) : Option expr :=
  match b, args with
  | .BI_fmax, Econs e1 (Econs e2 Enil) => some (Eop Omaxf (Econs e1 (Econs e2 Enil)))
  | .BI_fmin, Econs e1 (Econs e2 Enil) => some (Eop Ominf (Econs e1 (Econs e2 Enil)))
  | _, _ => none

end CompCert4Lean.X86.SelectOp
