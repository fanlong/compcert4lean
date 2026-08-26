import CompCert4Lean.Backend.CSEdomain
import CompCert4Lean.X86.Op

/-!
# Combined x86 operations and addressing modes

Definition-bearing translation of CompCert's `x86/CombineOp.v`.
-/

namespace CompCert4Lean.X86.CombineOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op

private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev condition := CompCert4Lean.X86.Op.condition
private abbrev addressing := CompCert4Lean.X86.Op.addressing
private abbrev rhs := CompCert4Lean.Backend.CSEdomain.rhs

def valnum : Type := positive

def combine_compimm_ne_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | some (.Op (.Oandimm n) ys) => some (.Cmasknotzero n, ys)
  | some (.Op (.Oxorimm n) ys) => some (.Ccompimm .Cne n, ys)
  | _ => none

def combine_compimm_eq_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negate_condition c, ys)
  | some (.Op (.Oandimm n) ys) => some (.Cmaskzero n, ys)
  | some (.Op (.Oxorimm n) ys) => some (.Ccompimm .Ceq n, ys)
  | _ => none

def combine_compimm_eq_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | _ => none

def combine_compimm_ne_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negate_condition c, ys)
  | _ => none

def combine_cond (get : valnum → Option rhs) (cond : condition)
    (args : List valnum) : Option (condition × List valnum) :=
  match cond, args with
  | .Ccompimm .Cne n, [x] =>
      if n = Int.zero then combine_compimm_ne_0 get x
      else if n = Int.one then combine_compimm_ne_1 get x
      else none
  | .Ccompimm .Ceq n, [x] =>
      if n = Int.zero then combine_compimm_eq_0 get x
      else if n = Int.one then combine_compimm_eq_1 get x
      else none
  | .Ccompuimm .Cne n, [x] =>
      if n = Int.zero then combine_compimm_ne_0 get x
      else if n = Int.one then combine_compimm_ne_1 get x
      else none
  | .Ccompuimm .Ceq n, [x] =>
      if n = Int.zero then combine_compimm_eq_0 get x
      else if n = Int.one then combine_compimm_eq_1 get x
      else none
  | _, _ => none

def combine_cond' (cond : condition) (args : List valnum) : Option Bool :=
  match cond with
  | .Ccomp c | .Ccompu c | .Ccompl c | .Ccomplu c =>
      match args with
      | [x, y] => CompCert4Lean.Backend.CSEdomain.combine_comparison c x y
      | _ => none
  | _ => none

def combine_addr_32 (get : valnum → Option rhs) (addr : addressing)
    (args : List valnum) : Option (addressing × List valnum) :=
  match addr, args with
  | .Aindexed n, [x] =>
      match get x with
      | some (.Op (.Olea a) ys) =>
          match offset_addressing a n with
          | some a' => some (a', ys)
          | none => none
      | _ => none
  | _, _ => none

def combine_addr_64 (get : valnum → Option rhs) (addr : addressing)
    (args : List valnum) : Option (addressing × List valnum) :=
  match addr, args with
  | .Aindexed n, [x] =>
      match get x with
      | some (.Op (.Oleal a) ys) =>
          match offset_addressing a n with
          | some a' => some (a', ys)
          | none => none
      | _ => none
  | _, _ => none

def combine_addr (get : valnum → Option rhs) (addr : addressing)
    (args : List valnum) : Option (addressing × List valnum) :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    combine_addr_64 get addr args
  else
    combine_addr_32 get addr args

def combine_op (get : valnum → Option rhs) (op : operation)
    (args : List valnum) : Option (operation × List valnum) :=
  match op, args with
  | .Olea addr, _ =>
      match combine_addr_32 get addr args with
      | some (addr', args') => some (.Olea addr', args')
      | none => none
  | .Oleal addr, _ =>
      match combine_addr_64 get addr args with
      | some (addr', args') => some (.Oleal addr', args')
      | none => none
  | .Oandimm n, [x] =>
      match get x with
      | some (.Op (.Oandimm m) ys) => some (.Oandimm (Int.and m n), ys)
      | _ => none
  | .Oorimm n, [x] =>
      match get x with
      | some (.Op (.Oorimm m) ys) => some (.Oorimm (Int.or m n), ys)
      | _ => none
  | .Oxorimm n, [x] =>
      match get x with
      | some (.Op (.Oxorimm m) ys) => some (.Oxorimm (Int.xor m n), ys)
      | _ => none
  | .Oandlimm n, [x] =>
      match get x with
      | some (.Op (.Oandlimm m) ys) =>
          some (.Oandlimm (CompCert4Lean.Lib.Integers.Int64.and m n), ys)
      | _ => none
  | .Oorlimm n, [x] =>
      match get x with
      | some (.Op (.Oorlimm m) ys) =>
          some (.Oorlimm (CompCert4Lean.Lib.Integers.Int64.or m n), ys)
      | _ => none
  | .Oxorlimm n, [x] =>
      match get x with
      | some (.Op (.Oxorlimm m) ys) =>
          some (.Oxorlimm (CompCert4Lean.Lib.Integers.Int64.xor m n), ys)
      | _ => none
  | .Ocmp cond, _ =>
      match combine_cond' cond args with
      | some b => some ((if b then .Ointconst Int.one else .Ointconst Int.zero), [])
      | none =>
          match combine_cond get cond args with
          | some (cond', args') => some (.Ocmp cond', args')
          | none => none
  | .Osel cond ty, x :: y :: rest =>
      match combine_cond' cond rest with
      | some b => some (.Omove, [(if b then x else y)])
      | none =>
          match eq_valnum x y with
          | .left _ => some (.Omove, [x])
          | .right _ =>
              match combine_cond get cond rest with
              | some (cond', args') => some (.Osel cond' ty, x :: y :: args')
              | none => none
  | _, _ => none

/-! ## Selected Rocq `Function` case surface

The pinned Rocq compiler generates the relation `R_combine_op` for
`functional inversion` of `combine_op`.  This is the only generated case
surface selected by the SCC-141 closure; the generic recursors are left to
Lean's inductive eliminators and are not re-exported as unused Rocq
machinery.  `combine_op_cases` is the source-facing spelling used by the
repair/audit closure.
-/

inductive R_combine_op (get : valnum → Option rhs) :
    operation → List valnum → Option (operation × List valnum) → Type where
  | R_combine_op_0 (op : operation) (args : List valnum) (addr : addressing) :
      op = .Olea addr →
      (xs : List valnum) → args = xs →
      (addr' : addressing) → (args' : List valnum) →
      combine_addr_32 get addr args = some (addr', args') →
      R_combine_op get (.Olea addr) xs (some (.Olea addr', args'))
  | R_combine_op_1 (op : operation) (args : List valnum) (addr : addressing) :
      op = .Olea addr →
      (xs : List valnum) → args = xs →
      combine_addr_32 get addr args = none →
      R_combine_op get (.Olea addr) xs none
  | R_combine_op_2 (op : operation) (args : List valnum) (addr : addressing) :
      op = .Oleal addr →
      (xs : List valnum) → args = xs →
      (addr' : addressing) → (args' : List valnum) →
      combine_addr_64 get addr args = some (addr', args') →
      R_combine_op get (.Oleal addr) xs (some (.Oleal addr', args'))
  | R_combine_op_3 (op : operation) (args : List valnum) (addr : addressing) :
      op = .Oleal addr →
      (xs : List valnum) → args = xs →
      combine_addr_64 get addr args = none →
      R_combine_op get (.Oleal addr) xs none
  | R_combine_op_4 (op : operation) (args : List valnum) (n : Int.int) :
      op = .Oandimm n →
      (x : valnum) → args = [x] →
      (m : Int.int) → (ys : List valnum) →
      get x = some (.Op (.Oandimm m) ys) →
      R_combine_op get (.Oandimm n) [x]
        (some (.Oandimm (Int.and m n), ys))
  | R_combine_op_5 (op : operation) (args : List valnum) (n : Int.int) :
      op = .Oandimm n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oandimm _) _) => False
       | _ => True) →
      R_combine_op get (.Oandimm n) [x] none
  | R_combine_op_6 (op : operation) (args : List valnum) (n : Int.int) :
      op = .Oorimm n →
      (x : valnum) → args = [x] →
      (m : Int.int) → (ys : List valnum) →
      get x = some (.Op (.Oorimm m) ys) →
      R_combine_op get (.Oorimm n) [x]
        (some (.Oorimm (Int.or m n), ys))
  | R_combine_op_7 (op : operation) (args : List valnum) (n : Int.int) :
      op = .Oorimm n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oorimm _) _) => False
       | _ => True) →
      R_combine_op get (.Oorimm n) [x] none
  | R_combine_op_8 (op : operation) (args : List valnum) (n : Int.int) :
      op = .Oxorimm n →
      (x : valnum) → args = [x] →
      (m : Int.int) → (ys : List valnum) →
      get x = some (.Op (.Oxorimm m) ys) →
      R_combine_op get (.Oxorimm n) [x]
        (some (.Oxorimm (Int.xor m n), ys))
  | R_combine_op_9 (op : operation) (args : List valnum) (n : Int.int) :
      op = .Oxorimm n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oxorimm _) _) => False
       | _ => True) →
      R_combine_op get (.Oxorimm n) [x] none
  | R_combine_op_10 (op : operation) (args : List valnum) (n : Int64.int) :
      op = .Oandlimm n →
      (x : valnum) → args = [x] →
      (m : Int64.int) → (ys : List valnum) →
      get x = some (.Op (.Oandlimm m) ys) →
      R_combine_op get (.Oandlimm n) [x]
        (some (.Oandlimm (Int64.and m n), ys))
  | R_combine_op_11 (op : operation) (args : List valnum) (n : Int64.int) :
      op = .Oandlimm n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oandlimm _) _) => False
       | _ => True) →
      R_combine_op get (.Oandlimm n) [x] none
  | R_combine_op_12 (op : operation) (args : List valnum) (n : Int64.int) :
      op = .Oorlimm n →
      (x : valnum) → args = [x] →
      (m : Int64.int) → (ys : List valnum) →
      get x = some (.Op (.Oorlimm m) ys) →
      R_combine_op get (.Oorlimm n) [x]
        (some (.Oorlimm (Int64.or m n), ys))
  | R_combine_op_13 (op : operation) (args : List valnum) (n : Int64.int) :
      op = .Oorlimm n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oorlimm _) _) => False
       | _ => True) →
      R_combine_op get (.Oorlimm n) [x] none
  | R_combine_op_14 (op : operation) (args : List valnum) (n : Int64.int) :
      op = .Oxorlimm n →
      (x : valnum) → args = [x] →
      (m : Int64.int) → (ys : List valnum) →
      get x = some (.Op (.Oxorlimm m) ys) →
      R_combine_op get (.Oxorlimm n) [x]
        (some (.Oxorlimm (CompCert4Lean.Lib.Integers.Int64.xor m n), ys))
  | R_combine_op_15 (op : operation) (args : List valnum) (n : Int64.int) :
      op = .Oxorlimm n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oxorlimm _) _) => False
       | _ => True) →
      R_combine_op get (.Oxorlimm n) [x] none
  | R_combine_op_16 (op : operation) (args : List valnum) (cond : condition) :
      op = .Ocmp cond →
      (xs : List valnum) → args = xs →
      (b : Bool) → combine_cond' cond args = some b → b = true →
      R_combine_op get (.Ocmp cond) xs
        (some (.Ointconst Int.one, []))
  | R_combine_op_17 (op : operation) (args : List valnum) (cond : condition) :
      op = .Ocmp cond →
      (xs : List valnum) → args = xs →
      (b : Bool) → combine_cond' cond args = some b → b = false →
      R_combine_op get (.Ocmp cond) xs
        (some (.Ointconst Int.zero, []))
  | R_combine_op_18 (op : operation) (args : List valnum) (cond : condition) :
      op = .Ocmp cond →
      (xs : List valnum) → args = xs →
      combine_cond' cond args = none →
      (cond' : condition) → (args' : List valnum) →
      combine_cond get cond args = some (cond', args') →
      R_combine_op get (.Ocmp cond) xs (some (.Ocmp cond', args'))
  | R_combine_op_19 (op : operation) (args : List valnum) (cond : condition) :
      op = .Ocmp cond →
      (xs : List valnum) → args = xs →
      combine_cond' cond args = none →
      combine_cond get cond args = none →
      R_combine_op get (.Ocmp cond) xs none
  | R_combine_op_20 (op : operation) (args : List valnum)
      (cond : condition) (ty : CompCert4Lean.Common.AST.typ) :
      op = .Osel cond ty →
      (x y : valnum) → (args0 : List valnum) → args = x :: y :: args0 →
      (b : Bool) → combine_cond' cond args0 = some b → b = true →
      R_combine_op get (.Osel cond ty) (x :: y :: args0)
        (some (.Omove, [x]))
  | R_combine_op_21 (op : operation) (args : List valnum)
      (cond : condition) (ty : CompCert4Lean.Common.AST.typ) :
      op = .Osel cond ty →
      (x y : valnum) → (args0 : List valnum) → args = x :: y :: args0 →
      (b : Bool) → combine_cond' cond args0 = some b → b = false →
      R_combine_op get (.Osel cond ty) (x :: y :: args0)
        (some (.Omove, [y]))
  | R_combine_op_22 (op : operation) (args : List valnum)
      (cond : condition) (ty : CompCert4Lean.Common.AST.typ) :
      op = .Osel cond ty →
      (x y : valnum) → (args0 : List valnum) → args = x :: y :: args0 →
      combine_cond' cond args0 = none →
      (hxy : x = y) → eq_valnum x y = .left hxy →
      R_combine_op get (.Osel cond ty) (x :: y :: args0)
        (some (.Omove, [x]))
  | R_combine_op_23 (op : operation) (args : List valnum)
      (cond : condition) (ty : CompCert4Lean.Common.AST.typ) :
      op = .Osel cond ty →
      (x y : valnum) → (args0 : List valnum) → args = x :: y :: args0 →
      combine_cond' cond args0 = none →
      (hxy : x ≠ y) → eq_valnum x y = .right hxy →
      (cond' : condition) → (args' : List valnum) →
      combine_cond get cond args0 = some (cond', args') →
      R_combine_op get (.Osel cond ty) (x :: y :: args0)
        (some (.Osel cond' ty, x :: y :: args'))
  | R_combine_op_24 (op : operation) (args : List valnum)
      (cond : condition) (ty : CompCert4Lean.Common.AST.typ) :
      op = .Osel cond ty →
      (x y : valnum) → (args0 : List valnum) → args = x :: y :: args0 →
      combine_cond' cond args0 = none →
      (hxy : x ≠ y) → eq_valnum x y = .right hxy →
      combine_cond get cond args0 = none →
      R_combine_op get (.Osel cond ty) (x :: y :: args0) none
  | R_combine_op_25 (op : operation) (args : List valnum) (op0 : operation) :
      op = op0 →
      (args0 : List valnum) → args = args0 →
      (match op0 with
       | .Oandimm _ | .Oorimm _ | .Oxorimm _ |
         .Oandlimm _ | .Oorlimm _ | .Oxorlimm _ =>
           match args0 with
           | [_] => False
           | _ => True
       | .Olea _ | .Oleal _ | .Ocmp _ => False
       | .Osel _ _ =>
           match args0 with
           | _ :: _ :: _ => False
           | _ => True
       | _ => True) →
      R_combine_op get op0 args0 none

abbrev combine_op_cases := R_combine_op

export R_combine_op
  (R_combine_op_0 R_combine_op_1 R_combine_op_2 R_combine_op_3
   R_combine_op_4 R_combine_op_5 R_combine_op_6 R_combine_op_7
   R_combine_op_8 R_combine_op_9 R_combine_op_10 R_combine_op_11
   R_combine_op_12 R_combine_op_13 R_combine_op_14 R_combine_op_15
   R_combine_op_16 R_combine_op_17 R_combine_op_18 R_combine_op_19
   R_combine_op_20 R_combine_op_21 R_combine_op_22 R_combine_op_23
   R_combine_op_24 R_combine_op_25)

def R_combine_op_correctStatement : Type :=
  ∀ (get : valnum → Option rhs) (op : operation) (args : List valnum)
    (res : Option (operation × List valnum)),
    res = combine_op get op args → R_combine_op get op args res

def R_combine_op_completeStatement : Prop :=
  ∀ (get : valnum → Option rhs) (op : operation) (args : List valnum)
    (res : Option (operation × List valnum)),
    R_combine_op get op args res → res = combine_op get op args

end CompCert4Lean.X86.CombineOp
