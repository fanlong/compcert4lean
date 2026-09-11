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
      match Int.eq_dec n Int.zero with
      | .left _ => combine_compimm_ne_0 get x
      | .right _ =>
          match Int.eq_dec n Int.one with
          | .left _ => combine_compimm_ne_1 get x
          | .right _ => none
  | .Ccompimm .Ceq n, [x] =>
      match Int.eq_dec n Int.zero with
      | .left _ => combine_compimm_eq_0 get x
      | .right _ =>
          match Int.eq_dec n Int.one with
          | .left _ => combine_compimm_eq_1 get x
          | .right _ => none
  | .Ccompuimm .Cne n, [x] =>
      match Int.eq_dec n Int.zero with
      | .left _ => combine_compimm_ne_0 get x
      | .right _ =>
          match Int.eq_dec n Int.one with
          | .left _ => combine_compimm_ne_1 get x
          | .right _ => none
  | .Ccompuimm .Ceq n, [x] =>
      match Int.eq_dec n Int.zero with
      | .left _ => combine_compimm_eq_0 get x
      | .right _ =>
          match Int.eq_dec n Int.one with
          | .left _ => combine_compimm_eq_1 get x
          | .right _ => none
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

/-! ## Selected Rocq `Function` graph surfaces

Each relation below is the graph generated by Rocq's `Function` command for
the corresponding selected definition.  The propositions on the fallback
constructors are retained verbatim; they are proof obligations for the later
proof-grinding phase, not executable tests or inhabited placeholders.
-/

inductive R_combine_compimm_ne_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) → Type where
  | R_combine_compimm_ne_0_0 (c : condition) (ys : List valnum) :
      get x = some (.Op (.Ocmp c) ys) →
      R_combine_compimm_ne_0 get x (some (c, ys))
  | R_combine_compimm_ne_0_1 (n : Int.int) (ys : List valnum) :
      get x = some (.Op (.Oandimm n) ys) →
      R_combine_compimm_ne_0 get x (some (.Cmasknotzero n, ys))
  | R_combine_compimm_ne_0_2 (n : Int.int) (ys : List valnum) :
      get x = some (.Op (.Oxorimm n) ys) →
      R_combine_compimm_ne_0 get x (some (.Ccompimm .Cne n, ys))
  | R_combine_compimm_ne_0_3 (r : Option rhs) :
      get x = r →
      (match r with
       | some (.Op (.Oandimm _) _) | some (.Op (.Oxorimm _) _) |
         some (.Op (.Ocmp _) _) => False
       | _ => True) →
      R_combine_compimm_ne_0 get x none

inductive R_combine_compimm_eq_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) → Type where
  | R_combine_compimm_eq_0_0 (c : condition) (ys : List valnum) :
      get x = some (.Op (.Ocmp c) ys) →
      R_combine_compimm_eq_0 get x (some (negate_condition c, ys))
  | R_combine_compimm_eq_0_1 (n : Int.int) (ys : List valnum) :
      get x = some (.Op (.Oandimm n) ys) →
      R_combine_compimm_eq_0 get x (some (.Cmaskzero n, ys))
  | R_combine_compimm_eq_0_2 (n : Int.int) (ys : List valnum) :
      get x = some (.Op (.Oxorimm n) ys) →
      R_combine_compimm_eq_0 get x (some (.Ccompimm .Ceq n, ys))
  | R_combine_compimm_eq_0_3 (r : Option rhs) :
      get x = r →
      (match r with
       | some (.Op (.Oandimm _) _) | some (.Op (.Oxorimm _) _) |
         some (.Op (.Ocmp _) _) => False
       | _ => True) →
      R_combine_compimm_eq_0 get x none

inductive R_combine_compimm_eq_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) → Type where
  | R_combine_compimm_eq_1_0 (c : condition) (ys : List valnum) :
      get x = some (.Op (.Ocmp c) ys) →
      R_combine_compimm_eq_1 get x (some (c, ys))
  | R_combine_compimm_eq_1_1 (r : Option rhs) :
      get x = r →
      (match r with
       | some (.Op (.Ocmp _) _) => False
       | _ => True) →
      R_combine_compimm_eq_1 get x none

inductive R_combine_compimm_ne_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) → Type where
  | R_combine_compimm_ne_1_0 (c : condition) (ys : List valnum) :
      get x = some (.Op (.Ocmp c) ys) →
      R_combine_compimm_ne_1 get x (some (negate_condition c, ys))
  | R_combine_compimm_ne_1_1 (r : Option rhs) :
      get x = r →
      (match r with
       | some (.Op (.Ocmp _) _) => False
       | _ => True) →
      R_combine_compimm_ne_1 get x none

inductive R_combine_cond (get : valnum → Option rhs) :
    condition → List valnum → Option (condition × List valnum) → Type where
  | R_combine_cond_0 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompimm .Cne n →
      (x : valnum) → args = [x] →
      (h0 : n = Int.zero) → Int.eq_dec n Int.zero = .left h0 →
      R_combine_cond get (.Ccompimm .Cne n) [x]
        (combine_compimm_ne_0 get x)
  | R_combine_cond_1 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompimm .Cne n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n = Int.one) → Int.eq_dec n Int.one = .left h1 →
      R_combine_cond get (.Ccompimm .Cne n) [x]
        (combine_compimm_ne_1 get x)
  | R_combine_cond_2 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompimm .Cne n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n ≠ Int.one) → Int.eq_dec n Int.one = .right h1 →
      R_combine_cond get (.Ccompimm .Cne n) [x] none
  | R_combine_cond_3 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompimm .Ceq n →
      (x : valnum) → args = [x] →
      (h0 : n = Int.zero) → Int.eq_dec n Int.zero = .left h0 →
      R_combine_cond get (.Ccompimm .Ceq n) [x]
        (combine_compimm_eq_0 get x)
  | R_combine_cond_4 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompimm .Ceq n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n = Int.one) → Int.eq_dec n Int.one = .left h1 →
      R_combine_cond get (.Ccompimm .Ceq n) [x]
        (combine_compimm_eq_1 get x)
  | R_combine_cond_5 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompimm .Ceq n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n ≠ Int.one) → Int.eq_dec n Int.one = .right h1 →
      R_combine_cond get (.Ccompimm .Ceq n) [x] none
  | R_combine_cond_6 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompuimm .Cne n →
      (x : valnum) → args = [x] →
      (h0 : n = Int.zero) → Int.eq_dec n Int.zero = .left h0 →
      R_combine_cond get (.Ccompuimm .Cne n) [x]
        (combine_compimm_ne_0 get x)
  | R_combine_cond_7 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompuimm .Cne n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n = Int.one) → Int.eq_dec n Int.one = .left h1 →
      R_combine_cond get (.Ccompuimm .Cne n) [x]
        (combine_compimm_ne_1 get x)
  | R_combine_cond_8 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompuimm .Cne n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n ≠ Int.one) → Int.eq_dec n Int.one = .right h1 →
      R_combine_cond get (.Ccompuimm .Cne n) [x] none
  | R_combine_cond_9 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompuimm .Ceq n →
      (x : valnum) → args = [x] →
      (h0 : n = Int.zero) → Int.eq_dec n Int.zero = .left h0 →
      R_combine_cond get (.Ccompuimm .Ceq n) [x]
        (combine_compimm_eq_0 get x)
  | R_combine_cond_10 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompuimm .Ceq n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n = Int.one) → Int.eq_dec n Int.one = .left h1 →
      R_combine_cond get (.Ccompuimm .Ceq n) [x]
        (combine_compimm_eq_1 get x)
  | R_combine_cond_11 (cond : condition) (args : List valnum) (n : Int.int) :
      cond = .Ccompuimm .Ceq n →
      (x : valnum) → args = [x] →
      (h0 : n ≠ Int.zero) → Int.eq_dec n Int.zero = .right h0 →
      (h1 : n ≠ Int.one) → Int.eq_dec n Int.one = .right h1 →
      R_combine_cond get (.Ccompuimm .Ceq n) [x] none
  | R_combine_cond_12 (cond : condition) (args : List valnum) (c : condition) :
      cond = c →
      (xs : List valnum) → args = xs →
      (match c with
       | .Ccompimm .Ceq _ | .Ccompimm .Cne _ |
         .Ccompuimm .Ceq _ | .Ccompuimm .Cne _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) →
      R_combine_cond get c xs none

inductive R_combine_addr_32 (get : valnum → Option rhs) :
    addressing → List valnum → Option (addressing × List valnum) → Type where
  | R_combine_addr_32_0 (addr : addressing) (args : List valnum) (n : Z) :
      addr = .Aindexed n →
      (x : valnum) → args = [x] →
      (a : addressing) → (ys : List valnum) →
      get x = some (.Op (.Olea a) ys) →
      (a' : addressing) → offset_addressing a n = some a' →
      R_combine_addr_32 get (.Aindexed n) [x] (some (a', ys))
  | R_combine_addr_32_1 (addr : addressing) (args : List valnum) (n : Z) :
      addr = .Aindexed n →
      (x : valnum) → args = [x] →
      (a : addressing) → (ys : List valnum) →
      get x = some (.Op (.Olea a) ys) →
      offset_addressing a n = none →
      R_combine_addr_32 get (.Aindexed n) [x] none
  | R_combine_addr_32_2 (addr : addressing) (args : List valnum) (n : Z) :
      addr = .Aindexed n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Olea _) _) => False
       | _ => True) →
      R_combine_addr_32 get (.Aindexed n) [x] none
  | R_combine_addr_32_3 (addr : addressing) (args : List valnum) (a : addressing) :
      addr = a →
      (xs : List valnum) → args = xs →
      (match a with
       | .Aindexed _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) →
      R_combine_addr_32 get a xs none

inductive R_combine_addr_64 (get : valnum → Option rhs) :
    addressing → List valnum → Option (addressing × List valnum) → Type where
  | R_combine_addr_64_0 (addr : addressing) (args : List valnum) (n : Z) :
      addr = .Aindexed n →
      (x : valnum) → args = [x] →
      (a : addressing) → (ys : List valnum) →
      get x = some (.Op (.Oleal a) ys) →
      (a' : addressing) → offset_addressing a n = some a' →
      R_combine_addr_64 get (.Aindexed n) [x] (some (a', ys))
  | R_combine_addr_64_1 (addr : addressing) (args : List valnum) (n : Z) :
      addr = .Aindexed n →
      (x : valnum) → args = [x] →
      (a : addressing) → (ys : List valnum) →
      get x = some (.Op (.Oleal a) ys) →
      offset_addressing a n = none →
      R_combine_addr_64 get (.Aindexed n) [x] none
  | R_combine_addr_64_2 (addr : addressing) (args : List valnum) (n : Z) :
      addr = .Aindexed n →
      (x : valnum) → args = [x] →
      (r : Option rhs) → get x = r →
      (match r with
       | some (.Op (.Oleal _) _) => False
       | _ => True) →
      R_combine_addr_64 get (.Aindexed n) [x] none
  | R_combine_addr_64_3 (addr : addressing) (args : List valnum) (a : addressing) :
      addr = a →
      (xs : List valnum) → args = xs →
      (match a with
       | .Aindexed _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) →
      R_combine_addr_64 get a xs none

export R_combine_compimm_ne_0
  (R_combine_compimm_ne_0_0 R_combine_compimm_ne_0_1
   R_combine_compimm_ne_0_2 R_combine_compimm_ne_0_3)

export R_combine_compimm_eq_0
  (R_combine_compimm_eq_0_0 R_combine_compimm_eq_0_1
   R_combine_compimm_eq_0_2 R_combine_compimm_eq_0_3)

export R_combine_compimm_eq_1
  (R_combine_compimm_eq_1_0 R_combine_compimm_eq_1_1)

export R_combine_compimm_ne_1
  (R_combine_compimm_ne_1_0 R_combine_compimm_ne_1_1)

export R_combine_cond
  (R_combine_cond_0 R_combine_cond_1 R_combine_cond_2 R_combine_cond_3
   R_combine_cond_4 R_combine_cond_5 R_combine_cond_6 R_combine_cond_7
   R_combine_cond_8 R_combine_cond_9 R_combine_cond_10 R_combine_cond_11
   R_combine_cond_12)

export R_combine_addr_32
  (R_combine_addr_32_0 R_combine_addr_32_1 R_combine_addr_32_2
   R_combine_addr_32_3)

export R_combine_addr_64
  (R_combine_addr_64_0 R_combine_addr_64_1 R_combine_addr_64_2
   R_combine_addr_64_3)

def R_combine_cond_correctStatement : Type :=
  ∀ (get : valnum → Option rhs) (cond : condition) (args : List valnum)
    (res : Option (condition × List valnum)),
    res = combine_cond get cond args → R_combine_cond get cond args res

def R_combine_cond_completeStatement : Prop :=
  ∀ (get : valnum → Option rhs) (cond : condition) (args : List valnum)
    (res : Option (condition × List valnum)),
    R_combine_cond get cond args res → res = combine_cond get cond args

def R_combine_addr_32_correctStatement : Type :=
  ∀ (get : valnum → Option rhs) (addr : addressing) (args : List valnum)
    (res : Option (addressing × List valnum)),
    res = combine_addr_32 get addr args → R_combine_addr_32 get addr args res

def R_combine_addr_32_completeStatement : Prop :=
  ∀ (get : valnum → Option rhs) (addr : addressing) (args : List valnum)
    (res : Option (addressing × List valnum)),
    R_combine_addr_32 get addr args res → res = combine_addr_32 get addr args

def R_combine_addr_64_correctStatement : Type :=
  ∀ (get : valnum → Option rhs) (addr : addressing) (args : List valnum)
    (res : Option (addressing × List valnum)),
    res = combine_addr_64 get addr args → R_combine_addr_64 get addr args res

def R_combine_addr_64_completeStatement : Prop :=
  ∀ (get : valnum → Option rhs) (addr : addressing) (args : List valnum)
    (res : Option (addressing × List valnum)),
    R_combine_addr_64 get addr args res → res = combine_addr_64 get addr args

/-! ## Selected Rocq `Function` case surface

The pinned Rocq compiler generates the relation `R_combine_op` for
`functional inversion` of `combine_op`.  It is retained alongside the seven
other selected graph relations above; generic recursors remain represented by
the exact `_indStatement` descriptors below.  `combine_op_cases` is the
source-facing spelling used by the repair/audit closure.
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

/-! ## Exact induction-principle statement descriptors

These are the source-facing propositions of Rocq's generated `_ind` schemes.
The descriptors deliberately carry all branch equalities, decision witnesses,
and negative match obligations; proof terms are supplied during proof grinding.
-/

def combine_compimm_ne_0_indStatement : Prop :=
  ∀ (get : valnum → Option rhs) (x : valnum)
    (P : Option (condition × List valnum) → Prop),
    (∀ (c : condition) (ys : List valnum),
      get x = some (.Op (.Ocmp c) ys) → P (some (c, ys))) →
    (∀ (n : Int.int) (ys : List valnum),
      get x = some (.Op (.Oandimm n) ys) →
        P (some (.Cmasknotzero n, ys))) →
    (∀ (n : Int.int) (ys : List valnum),
      get x = some (.Op (.Oxorimm n) ys) →
        P (some (.Ccompimm .Cne n, ys))) →
    (∀ (r : Option rhs), get x = r →
      (match r with
       | some (.Op (.Oandimm _) _) | some (.Op (.Oxorimm _) _) |
         some (.Op (.Ocmp _) _) => False
       | _ => True) → P none) →
    P (combine_compimm_ne_0 get x)

def combine_compimm_eq_0_indStatement : Prop :=
  ∀ (get : valnum → Option rhs) (x : valnum)
    (P : Option (condition × List valnum) → Prop),
    (∀ (c : condition) (ys : List valnum),
      get x = some (.Op (.Ocmp c) ys) →
        P (some (negate_condition c, ys))) →
    (∀ (n : Int.int) (ys : List valnum),
      get x = some (.Op (.Oandimm n) ys) →
        P (some (.Cmaskzero n, ys))) →
    (∀ (n : Int.int) (ys : List valnum),
      get x = some (.Op (.Oxorimm n) ys) →
        P (some (.Ccompimm .Ceq n, ys))) →
    (∀ (r : Option rhs), get x = r →
      (match r with
       | some (.Op (.Oandimm _) _) | some (.Op (.Oxorimm _) _) |
         some (.Op (.Ocmp _) _) => False
       | _ => True) → P none) →
    P (combine_compimm_eq_0 get x)

def combine_compimm_eq_1_indStatement : Prop :=
  ∀ (get : valnum → Option rhs) (x : valnum)
    (P : Option (condition × List valnum) → Prop),
    (∀ (c : condition) (ys : List valnum),
      get x = some (.Op (.Ocmp c) ys) → P (some (c, ys))) →
    (∀ (r : Option rhs), get x = r →
      (match r with
       | some (.Op (.Ocmp _) _) => False
       | _ => True) → P none) →
    P (combine_compimm_eq_1 get x)

def combine_compimm_ne_1_indStatement : Prop :=
  ∀ (get : valnum → Option rhs) (x : valnum)
    (P : Option (condition × List valnum) → Prop),
    (∀ (c : condition) (ys : List valnum),
      get x = some (.Op (.Ocmp c) ys) →
        P (some (negate_condition c, ys))) →
    (∀ (r : Option rhs), get x = r →
      (match r with
       | some (.Op (.Ocmp _) _) => False
       | _ => True) → P none) →
    P (combine_compimm_ne_1 get x)

def combine_addr_32_indStatement : Prop :=
  ∀ (get : valnum → Option rhs)
    (P : addressing → List valnum →
      Option (addressing × List valnum) → Prop),
    (∀ (addr : addressing) (args : List valnum) (n : Z),
      addr = .Aindexed n →
      ∀ (x : valnum), args = [x] →
      ∀ (a : addressing) (ys : List valnum),
        get x = some (.Op (.Olea a) ys) →
        ∀ (a' : addressing), offset_addressing a n = some a' →
          P (.Aindexed n) [x] (some (a', ys))) →
    (∀ (addr : addressing) (args : List valnum) (n : Z),
      addr = .Aindexed n →
      ∀ (x : valnum), args = [x] →
      ∀ (a : addressing) (ys : List valnum),
        get x = some (.Op (.Olea a) ys) →
        offset_addressing a n = none → P (.Aindexed n) [x] none) →
    (∀ (addr : addressing) (args : List valnum) (n : Z),
      addr = .Aindexed n →
      ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Olea _) _) => False
         | _ => True) → P (.Aindexed n) [x] none) →
    (∀ (addr : addressing) (args : List valnum) (a : addressing),
      addr = a → ∀ (xs : List valnum), args = xs →
      (match a with
       | .Aindexed _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) → P a xs none) →
    ∀ (addr : addressing) (args : List valnum),
      P addr args (combine_addr_32 get addr args)

def combine_addr_64_indStatement : Prop :=
  ∀ (get : valnum → Option rhs)
    (P : addressing → List valnum →
      Option (addressing × List valnum) → Prop),
    (∀ (addr : addressing) (args : List valnum) (n : Z),
      addr = .Aindexed n →
      ∀ (x : valnum), args = [x] →
      ∀ (a : addressing) (ys : List valnum),
        get x = some (.Op (.Oleal a) ys) →
        ∀ (a' : addressing), offset_addressing a n = some a' →
          P (.Aindexed n) [x] (some (a', ys))) →
    (∀ (addr : addressing) (args : List valnum) (n : Z),
      addr = .Aindexed n →
      ∀ (x : valnum), args = [x] →
      ∀ (a : addressing) (ys : List valnum),
        get x = some (.Op (.Oleal a) ys) →
        offset_addressing a n = none → P (.Aindexed n) [x] none) →
    (∀ (addr : addressing) (args : List valnum) (n : Z),
      addr = .Aindexed n →
      ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oleal _) _) => False
         | _ => True) → P (.Aindexed n) [x] none) →
    (∀ (addr : addressing) (args : List valnum) (a : addressing),
      addr = a → ∀ (xs : List valnum), args = xs →
      (match a with
       | .Aindexed _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) → P a xs none) →
    ∀ (addr : addressing) (args : List valnum),
      P addr args (combine_addr_64 get addr args)

def combine_cond_indStatement : Prop :=
  ∀ (get : valnum → Option rhs)
    (P : condition → List valnum →
      Option (condition × List valnum) → Prop),
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompimm .Cne n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n = Int.zero), Int.eq_dec n Int.zero = .left h0 →
        P (.Ccompimm .Cne n) [x] (combine_compimm_ne_0 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompimm .Cne n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n = Int.one), Int.eq_dec n Int.one = .left h1 →
        P (.Ccompimm .Cne n) [x] (combine_compimm_ne_1 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompimm .Cne n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n ≠ Int.one), Int.eq_dec n Int.one = .right h1 →
        P (.Ccompimm .Cne n) [x] none) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompimm .Ceq n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n = Int.zero), Int.eq_dec n Int.zero = .left h0 →
        P (.Ccompimm .Ceq n) [x] (combine_compimm_eq_0 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompimm .Ceq n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n = Int.one), Int.eq_dec n Int.one = .left h1 →
        P (.Ccompimm .Ceq n) [x] (combine_compimm_eq_1 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompimm .Ceq n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n ≠ Int.one), Int.eq_dec n Int.one = .right h1 →
        P (.Ccompimm .Ceq n) [x] none) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompuimm .Cne n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n = Int.zero), Int.eq_dec n Int.zero = .left h0 →
        P (.Ccompuimm .Cne n) [x] (combine_compimm_ne_0 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompuimm .Cne n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n = Int.one), Int.eq_dec n Int.one = .left h1 →
        P (.Ccompuimm .Cne n) [x] (combine_compimm_ne_1 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompuimm .Cne n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n ≠ Int.one), Int.eq_dec n Int.one = .right h1 →
        P (.Ccompuimm .Cne n) [x] none) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompuimm .Ceq n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n = Int.zero), Int.eq_dec n Int.zero = .left h0 →
        P (.Ccompuimm .Ceq n) [x] (combine_compimm_eq_0 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompuimm .Ceq n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n = Int.one), Int.eq_dec n Int.one = .left h1 →
        P (.Ccompuimm .Ceq n) [x] (combine_compimm_eq_1 get x)) →
    (∀ (cond : condition) (args : List valnum) (n : Int.int),
      cond = .Ccompuimm .Ceq n →
      ∀ (x : valnum), args = [x] →
      ∀ (h0 : n ≠ Int.zero), Int.eq_dec n Int.zero = .right h0 →
      ∀ (h1 : n ≠ Int.one), Int.eq_dec n Int.one = .right h1 →
        P (.Ccompuimm .Ceq n) [x] none) →
    (∀ (cond : condition) (args : List valnum) (c : condition),
      cond = c → ∀ (xs : List valnum), args = xs →
      (match c with
       | .Ccompimm .Ceq _ | .Ccompimm .Cne _ |
         .Ccompuimm .Ceq _ | .Ccompuimm .Cne _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) → P c xs none) →
    ∀ (cond : condition) (args : List valnum),
      P cond args (combine_cond get cond args)

def combine_op_indStatement : Prop :=
  ∀ (get : valnum → Option rhs)
    (P : operation → List valnum →
      Option (operation × List valnum) → Prop),
    (∀ (op : operation) (args : List valnum) (addr : addressing),
      op = .Olea addr → ∀ (xs : List valnum), args = xs →
      ∀ (addr' : addressing) (args' : List valnum),
        combine_addr_32 get addr args = some (addr', args') →
          P (.Olea addr) xs (some (.Olea addr', args'))) →
    (∀ (op : operation) (args : List valnum) (addr : addressing),
      op = .Olea addr → ∀ (xs : List valnum), args = xs →
      combine_addr_32 get addr args = none → P (.Olea addr) xs none) →
    (∀ (op : operation) (args : List valnum) (addr : addressing),
      op = .Oleal addr → ∀ (xs : List valnum), args = xs →
      ∀ (addr' : addressing) (args' : List valnum),
        combine_addr_64 get addr args = some (addr', args') →
          P (.Oleal addr) xs (some (.Oleal addr', args'))) →
    (∀ (op : operation) (args : List valnum) (addr : addressing),
      op = .Oleal addr → ∀ (xs : List valnum), args = xs →
      combine_addr_64 get addr args = none → P (.Oleal addr) xs none) →
    (∀ (op : operation) (args : List valnum) (n : Int.int),
      op = .Oandimm n → ∀ (x : valnum), args = [x] →
      ∀ (m : Int.int) (ys : List valnum),
        get x = some (.Op (.Oandimm m) ys) →
          P (.Oandimm n) [x] (some (.Oandimm (Int.and m n), ys))) →
    (∀ (op : operation) (args : List valnum) (n : Int.int),
      op = .Oandimm n → ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oandimm _) _) => False
         | _ => True) → P (.Oandimm n) [x] none) →
    (∀ (op : operation) (args : List valnum) (n : Int.int),
      op = .Oorimm n → ∀ (x : valnum), args = [x] →
      ∀ (m : Int.int) (ys : List valnum),
        get x = some (.Op (.Oorimm m) ys) →
          P (.Oorimm n) [x] (some (.Oorimm (Int.or m n), ys))) →
    (∀ (op : operation) (args : List valnum) (n : Int.int),
      op = .Oorimm n → ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oorimm _) _) => False
         | _ => True) → P (.Oorimm n) [x] none) →
    (∀ (op : operation) (args : List valnum) (n : Int.int),
      op = .Oxorimm n → ∀ (x : valnum), args = [x] →
      ∀ (m : Int.int) (ys : List valnum),
        get x = some (.Op (.Oxorimm m) ys) →
          P (.Oxorimm n) [x] (some (.Oxorimm (Int.xor m n), ys))) →
    (∀ (op : operation) (args : List valnum) (n : Int.int),
      op = .Oxorimm n → ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oxorimm _) _) => False
         | _ => True) → P (.Oxorimm n) [x] none) →
    (∀ (op : operation) (args : List valnum) (n : Int64.int),
      op = .Oandlimm n → ∀ (x : valnum), args = [x] →
      ∀ (m : Int64.int) (ys : List valnum),
        get x = some (.Op (.Oandlimm m) ys) →
          P (.Oandlimm n) [x]
        (some (.Oandlimm (CompCert4Lean.Lib.Integers.Int64.and m n), ys))) →
    (∀ (op : operation) (args : List valnum) (n : Int64.int),
      op = .Oandlimm n → ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oandlimm _) _) => False
         | _ => True) → P (.Oandlimm n) [x] none) →
    (∀ (op : operation) (args : List valnum) (n : Int64.int),
      op = .Oorlimm n → ∀ (x : valnum), args = [x] →
      ∀ (m : Int64.int) (ys : List valnum),
        get x = some (.Op (.Oorlimm m) ys) →
          P (.Oorlimm n) [x]
        (some (.Oorlimm (CompCert4Lean.Lib.Integers.Int64.or m n), ys))) →
    (∀ (op : operation) (args : List valnum) (n : Int64.int),
      op = .Oorlimm n → ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oorlimm _) _) => False
         | _ => True) → P (.Oorlimm n) [x] none) →
    (∀ (op : operation) (args : List valnum) (n : Int64.int),
      op = .Oxorlimm n → ∀ (x : valnum), args = [x] →
      ∀ (m : Int64.int) (ys : List valnum),
        get x = some (.Op (.Oxorlimm m) ys) →
          P (.Oxorlimm n) [x]
        (some (.Oxorlimm (CompCert4Lean.Lib.Integers.Int64.xor m n), ys))) →
    (∀ (op : operation) (args : List valnum) (n : Int64.int),
      op = .Oxorlimm n → ∀ (x : valnum), args = [x] →
      ∀ (r : Option rhs), get x = r →
        (match r with
         | some (.Op (.Oxorlimm _) _) => False
         | _ => True) → P (.Oxorlimm n) [x] none) →
    (∀ (op : operation) (args : List valnum) (cond : condition),
      op = .Ocmp cond → ∀ (xs : List valnum), args = xs →
      ∀ (b : Bool), combine_cond' cond args = some b → b = true →
        P (.Ocmp cond) xs (some (.Ointconst Int.one, []))) →
    (∀ (op : operation) (args : List valnum) (cond : condition),
      op = .Ocmp cond → ∀ (xs : List valnum), args = xs →
      ∀ (b : Bool), combine_cond' cond args = some b → b = false →
        P (.Ocmp cond) xs (some (.Ointconst Int.zero, []))) →
    (∀ (op : operation) (args : List valnum) (cond : condition),
      op = .Ocmp cond → ∀ (xs : List valnum), args = xs →
      combine_cond' cond args = none →
      ∀ (cond' : condition) (args' : List valnum),
        combine_cond get cond args = some (cond', args') →
          P (.Ocmp cond) xs (some (.Ocmp cond', args'))) →
    (∀ (op : operation) (args : List valnum) (cond : condition),
      op = .Ocmp cond → ∀ (xs : List valnum), args = xs →
      combine_cond' cond args = none →
      combine_cond get cond args = none → P (.Ocmp cond) xs none) →
    (∀ (op : operation) (args : List valnum) (cond : condition)
      (ty : CompCert4Lean.Common.AST.typ),
      op = .Osel cond ty →
      ∀ (x y : valnum) (args0 : List valnum), args = x :: y :: args0 →
      ∀ (b : Bool), combine_cond' cond args0 = some b → b = true →
        P (.Osel cond ty) (x :: y :: args0) (some (.Omove, [x]))) →
    (∀ (op : operation) (args : List valnum) (cond : condition)
      (ty : CompCert4Lean.Common.AST.typ),
      op = .Osel cond ty →
      ∀ (x y : valnum) (args0 : List valnum), args = x :: y :: args0 →
      ∀ (b : Bool), combine_cond' cond args0 = some b → b = false →
        P (.Osel cond ty) (x :: y :: args0) (some (.Omove, [y]))) →
    (∀ (op : operation) (args : List valnum) (cond : condition)
      (ty : CompCert4Lean.Common.AST.typ),
      op = .Osel cond ty →
      ∀ (x y : valnum) (args0 : List valnum), args = x :: y :: args0 →
      combine_cond' cond args0 = none →
      ∀ (hxy : x = y), eq_valnum x y = .left hxy →
        P (.Osel cond ty) (x :: y :: args0) (some (.Omove, [x]))) →
    (∀ (op : operation) (args : List valnum) (cond : condition)
      (ty : CompCert4Lean.Common.AST.typ),
      op = .Osel cond ty →
      ∀ (x y : valnum) (args0 : List valnum), args = x :: y :: args0 →
      combine_cond' cond args0 = none →
      ∀ (hxy : x ≠ y), eq_valnum x y = .right hxy →
      ∀ (cond' : condition) (args' : List valnum),
        combine_cond get cond args0 = some (cond', args') →
          P (.Osel cond ty) (x :: y :: args0)
            (some (.Osel cond' ty, x :: y :: args'))) →
    (∀ (op : operation) (args : List valnum) (cond : condition)
      (ty : CompCert4Lean.Common.AST.typ),
      op = .Osel cond ty →
      ∀ (x y : valnum) (args0 : List valnum), args = x :: y :: args0 →
      combine_cond' cond args0 = none →
      ∀ (hxy : x ≠ y), eq_valnum x y = .right hxy →
      combine_cond get cond args0 = none →
        P (.Osel cond ty) (x :: y :: args0) none) →
    (∀ (op : operation) (args : List valnum) (op0 : operation),
      op = op0 → ∀ (xs : List valnum), args = xs →
      (match op0 with
       | .Oandimm _ | .Oorimm _ | .Oxorimm _ |
         .Oandlimm _ | .Oorlimm _ | .Oxorlimm _ =>
           match xs with
           | [_] => False
           | _ => True
       | .Olea _ | .Oleal _ | .Ocmp _ => False
       | .Osel _ _ =>
           match xs with
           | _ :: _ :: _ => False
           | _ => True
       | _ => True) → P op0 xs none) →
    ∀ (op : operation) (args : List valnum),
      P op args (combine_op get op args)

end CompCert4Lean.X86.CombineOp

namespace CompCert4Lean.X86.CombineOp

theorem combine_compimm_ne_0_ind : combine_compimm_ne_0_indStatement := by
  intro get x P hcmp hand hxor hnone
  cases h : get x with
  | none =>
      simpa [combine_compimm_ne_0, h] using hnone none h (by simp)
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simpa [combine_compimm_ne_0, h] using hnone _ h (by simp)
      | Builtin bf args =>
          simpa [combine_compimm_ne_0, h] using hnone _ h (by simp)
      | Op op ys =>
          cases op <;> simp_all [combine_compimm_ne_0] <;>
            first | exact hcmp _ _ rfl | exact hand _ _ rfl | exact hxor _ _ rfl

theorem combine_compimm_eq_0_ind : combine_compimm_eq_0_indStatement := by
  intro get x P hcmp hand hxor hnone
  cases h : get x with
  | none =>
      simpa [combine_compimm_eq_0, h] using hnone none h (by simp)
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simpa [combine_compimm_eq_0, h] using hnone _ h (by simp)
      | Builtin bf args =>
          simpa [combine_compimm_eq_0, h] using hnone _ h (by simp)
      | Op op ys =>
          cases op <;> simp_all [combine_compimm_eq_0] <;>
            first | exact hcmp _ _ rfl | exact hand _ _ rfl | exact hxor _ _ rfl

theorem combine_compimm_eq_1_ind : combine_compimm_eq_1_indStatement := by
  intro get x P hcmp hnone
  cases h : get x with
  | none =>
      simpa [combine_compimm_eq_1, h] using hnone none h (by simp)
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simpa [combine_compimm_eq_1, h] using hnone _ h (by simp)
      | Builtin bf args =>
          simpa [combine_compimm_eq_1, h] using hnone _ h (by simp)
      | Op op ys =>
          cases op <;> simp_all [combine_compimm_eq_1] <;>
            exact hcmp _ _ rfl

theorem combine_compimm_ne_1_ind : combine_compimm_ne_1_indStatement := by
  intro get x P hcmp hnone
  cases h : get x with
  | none =>
      simpa [combine_compimm_ne_1, h] using hnone none h (by simp)
  | some r =>
      cases r with
      | Load chunk addr vl p =>
          simpa [combine_compimm_ne_1, h] using hnone _ h (by simp)
      | Builtin bf args =>
          simpa [combine_compimm_ne_1, h] using hnone _ h (by simp)
      | Op op ys =>
          cases op <;> simp_all [combine_compimm_ne_1] <;>
            exact hcmp _ _ rfl

end CompCert4Lean.X86.CombineOp

namespace CompCert4Lean.X86.CombineOp

theorem R_combine_addr_32_complete : R_combine_addr_32_completeStatement := by
  intro get addr args res h
  cases h with
  | R_combine_addr_32_0 addr args n haddr x hargs a ys hg a' ho =>
      subst addr; subst args; simp [combine_addr_32, hg, ho]
  | R_combine_addr_32_1 addr args n haddr x hargs a ys hg ho =>
      subst addr; subst args; simp [combine_addr_32, hg, ho]
  | R_combine_addr_32_2 addr args n haddr x hargs r hg hb =>
      subst addr; subst args
      cases r with
      | none => simp [combine_addr_32, hg]
      | some r =>
          cases r with
          | Load chunk addr vl p => simp [combine_addr_32, hg]
          | Builtin bf args => simp [combine_addr_32, hg]
          | Op op ys => cases op <;> simp_all [combine_addr_32]
  | R_combine_addr_32_3 addr args a haddr xs hargs hb =>
      cases haddr; cases hargs; simp [combine_addr_32]; split <;> simp_all

theorem R_combine_addr_64_complete : R_combine_addr_64_completeStatement := by
  intro get addr args res h
  cases h with
  | R_combine_addr_64_0 addr args n haddr x hargs a ys hg a' ho =>
      subst addr; subst args; simp [combine_addr_64, hg, ho]
  | R_combine_addr_64_1 addr args n haddr x hargs a ys hg ho =>
      subst addr; subst args; simp [combine_addr_64, hg, ho]
  | R_combine_addr_64_2 addr args n haddr x hargs r hg hb =>
      subst addr; subst args
      cases r with
      | none => simp [combine_addr_64, hg]
      | some r =>
          cases r with
          | Load chunk addr vl p => simp [combine_addr_64, hg]
          | Builtin bf args => simp [combine_addr_64, hg]
          | Op op ys => cases op <;> simp_all [combine_addr_64]
  | R_combine_addr_64_3 addr args a haddr xs hargs hb =>
      cases haddr; cases hargs; simp [combine_addr_64]; split <;> simp_all

end CompCert4Lean.X86.CombineOp

namespace CompCert4Lean.X86.CombineOp

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.X86.Op

def R_combine_addr_32_correct : R_combine_addr_32_correctStatement := by
  intro get addr args res hres
  subst res
  have mk3 : ∀ (a : addressing) (xs : List valnum),
      (match a with
       | .Aindexed _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) → R_combine_addr_32 get a xs none := by
    intro a xs h
    exact R_combine_addr_32_3 a xs a rfl xs rfl h
  have mk2 : ∀ (n : Z) (x : valnum) (r : Option rhs),
      get x = r →
      (match r with
       | some (.Op (.Olea _) _) => False
       | _ => True) →
      R_combine_addr_32 get (.Aindexed n) [x] none := by
    intro n x r hr hb
    exact R_combine_addr_32_2 (.Aindexed n) [x] n rfl x rfl r hr hb
  cases addr with
  | Aindexed n =>
      cases args with
      | nil =>
          simpa [combine_addr_32] using mk3 (.Aindexed n) [] (by simp)
      | cons x xs =>
          cases xs with
          | nil =>
              cases hg : get x with
              | none =>
                  simpa [combine_addr_32, hg] using mk2 n x none hg (by simp)
              | some r =>
                  cases r with
                  | Load chunk addr vl p =>
                      simpa [combine_addr_32, hg] using
                        mk2 n x (some (.Load chunk addr vl p)) hg (by simp)
                  | Builtin bf args =>
                      simpa [combine_addr_32, hg] using
                        mk2 n x (some (.Builtin bf args)) hg (by simp)
                  | Op op ys =>
                      cases op with
                      | Olea a =>
                          cases ho : offset_addressing a n with
                          | none =>
                              simpa [combine_addr_32, hg, ho] using
                                R_combine_addr_32_1 (.Aindexed n) [x] n rfl x rfl a ys hg ho
                          | some a' =>
                              simpa [combine_addr_32, hg, ho] using
                                R_combine_addr_32_0 (.Aindexed n) [x] n rfl x rfl a ys hg a' ho
                      | _ =>
                          simpa [combine_addr_32, hg] using
                            mk2 n x _ hg (by simp)
          | cons y ys =>
              simpa [combine_addr_32] using mk3 (.Aindexed n) (x :: y :: ys) (by simp)
  | Aindexed2 ofs =>
      simpa [combine_addr_32] using mk3 (.Aindexed2 ofs) args (by simp)
  | Ascaled scale ofs =>
      simpa [combine_addr_32] using mk3 (.Ascaled scale ofs) args (by simp)
  | Aindexed2scaled scale ofs =>
      simpa [combine_addr_32] using mk3 (.Aindexed2scaled scale ofs) args (by simp)
  | Aglobal id ofs =>
      simpa [combine_addr_32] using mk3 (.Aglobal id ofs) args (by simp)
  | Abased id ofs =>
      simpa [combine_addr_32] using mk3 (.Abased id ofs) args (by simp)
  | Abasedscaled scale id ofs =>
      simpa [combine_addr_32] using mk3 (.Abasedscaled scale id ofs) args (by simp)
  | Ainstack ofs =>
      simpa [combine_addr_32] using mk3 (.Ainstack ofs) args (by simp)

def R_combine_addr_64_correct : R_combine_addr_64_correctStatement := by
  intro get addr args res hres
  subst res
  have mk3 : ∀ (a : addressing) (xs : List valnum),
      (match a with
       | .Aindexed _ =>
           match xs with
           | [_] => False
           | _ => True
       | _ => True) → R_combine_addr_64 get a xs none := by
    intro a xs h
    exact R_combine_addr_64_3 a xs a rfl xs rfl h
  have mk2 : ∀ (n : Z) (x : valnum) (r : Option rhs),
      get x = r →
      (match r with
       | some (.Op (.Oleal _) _) => False
       | _ => True) →
      R_combine_addr_64 get (.Aindexed n) [x] none := by
    intro n x r hr hb
    exact R_combine_addr_64_2 (.Aindexed n) [x] n rfl x rfl r hr hb
  cases addr with
  | Aindexed n =>
      cases args with
      | nil =>
          simpa [combine_addr_64] using mk3 (.Aindexed n) [] (by simp)
      | cons x xs =>
          cases xs with
          | nil =>
              cases hg : get x with
              | none =>
                  simpa [combine_addr_64, hg] using mk2 n x none hg (by simp)
              | some r =>
                  cases r with
                  | Load chunk addr vl p =>
                      simpa [combine_addr_64, hg] using
                        mk2 n x (some (.Load chunk addr vl p)) hg (by simp)
                  | Builtin bf args =>
                      simpa [combine_addr_64, hg] using
                        mk2 n x (some (.Builtin bf args)) hg (by simp)
                  | Op op ys =>
                      cases op with
                      | Oleal a =>
                          cases ho : offset_addressing a n with
                          | none =>
                              simpa [combine_addr_64, hg, ho] using
                                R_combine_addr_64_1 (.Aindexed n) [x] n rfl x rfl a ys hg ho
                          | some a' =>
                              simpa [combine_addr_64, hg, ho] using
                                R_combine_addr_64_0 (.Aindexed n) [x] n rfl x rfl a ys hg a' ho
                      | _ =>
                          simpa [combine_addr_64, hg] using
                            mk2 n x _ hg (by simp)
          | cons y ys =>
              simpa [combine_addr_64] using mk3 (.Aindexed n) (x :: y :: ys) (by simp)
  | Aindexed2 ofs =>
      simpa [combine_addr_64] using mk3 (.Aindexed2 ofs) args (by simp)
  | Ascaled scale ofs =>
      simpa [combine_addr_64] using mk3 (.Ascaled scale ofs) args (by simp)
  | Aindexed2scaled scale ofs =>
      simpa [combine_addr_64] using mk3 (.Aindexed2scaled scale ofs) args (by simp)
  | Aglobal id ofs =>
      simpa [combine_addr_64] using mk3 (.Aglobal id ofs) args (by simp)
  | Abased id ofs =>
      simpa [combine_addr_64] using mk3 (.Abased id ofs) args (by simp)
  | Abasedscaled scale id ofs =>
      simpa [combine_addr_64] using mk3 (.Abasedscaled scale id ofs) args (by simp)
  | Ainstack ofs =>
      simpa [combine_addr_64] using mk3 (.Ainstack ofs) args (by simp)

end CompCert4Lean.X86.CombineOp

namespace CompCert4Lean.X86.CombineOp

theorem R_combine_cond_complete : R_combine_cond_completeStatement := by
  intro get cond args res h
  cases h with
  | R_combine_cond_0 cond args n hcond x hargs h0 heq =>
      subst cond; subst args
      simp [combine_cond, h0, heq]
  | R_combine_cond_1 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_2 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_3 cond args n hcond x hargs h0 heq =>
      subst cond; subst args
      simp [combine_cond, h0, heq]
  | R_combine_cond_4 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_5 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_6 cond args n hcond x hargs h0 heq =>
      subst cond; subst args
      simp [combine_cond, h0, heq]
  | R_combine_cond_7 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_8 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_9 cond args n hcond x hargs h0 heq =>
      subst cond; subst args
      simp [combine_cond, h0, heq]
  | R_combine_cond_10 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_11 cond args n hcond x hargs h0 heq0 h1 heq1 =>
      subst cond; subst args
      simp [combine_cond, h0, h1, heq0, heq1]
  | R_combine_cond_12 cond args c hcond xs hargs hb =>
      unfold combine_cond
      split <;> simp_all

end CompCert4Lean.X86.CombineOp

namespace CompCert4Lean.X86.CombineOp

def R_combine_cond_correct : R_combine_cond_correctStatement := by
  intro get cond args res hres
  subst res
  cases args with
  | nil =>
      simpa [combine_cond] using
        (R_combine_cond_12 cond [] cond rfl [] rfl (by
        cases cond with
        | Ccompimm c n => cases c <;> simp
        | Ccompuimm c n => cases c <;> simp
        | _ => simp))
  | cons x xs =>
      cases xs with
      | cons y ys =>
          simpa [combine_cond] using
            (R_combine_cond_12 cond (x :: y :: ys) cond rfl (x :: y :: ys) rfl (by
            cases cond with
            | Ccompimm c n => cases c <;> simp
            | Ccompuimm c n => cases c <;> simp
            | _ => simp))
      | nil =>
          cases cond with
          | Ccompimm c n =>
              cases c with
              | Cne =>
                  cases h0 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                      CompCert4Lean.Lib.Integers.Int.zero with
                  | left hzero =>
                      simpa [combine_cond, h0] using
                        (R_combine_cond_0 _ _ n rfl x rfl hzero h0)
                  | right hne =>
                      cases h1 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                          CompCert4Lean.Lib.Integers.Int.one with
                      | left hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_1 _ _ n rfl x rfl hne h0 hone h1)
                      | right hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_2 _ _ n rfl x rfl hne h0 hone h1)
              | Ceq =>
                  cases h0 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                      CompCert4Lean.Lib.Integers.Int.zero with
                  | left hzero =>
                      simpa [combine_cond, h0] using
                        (R_combine_cond_3 _ _ n rfl x rfl hzero h0)
                  | right hne =>
                      cases h1 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                          CompCert4Lean.Lib.Integers.Int.one with
                      | left hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_4 _ _ n rfl x rfl hne h0 hone h1)
                      | right hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_5 _ _ n rfl x rfl hne h0 hone h1)
              | _ =>
                  simpa [combine_cond] using
                    (R_combine_cond_12 _ [x] _ rfl [x] rfl (by simp_all))
          | Ccompuimm c n =>
              cases c with
              | Cne =>
                  cases h0 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                      CompCert4Lean.Lib.Integers.Int.zero with
                  | left hzero =>
                      simpa [combine_cond, h0] using
                        (R_combine_cond_6 _ _ n rfl x rfl hzero h0)
                  | right hne =>
                      cases h1 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                          CompCert4Lean.Lib.Integers.Int.one with
                      | left hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_7 _ _ n rfl x rfl hne h0 hone h1)
                      | right hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_8 _ _ n rfl x rfl hne h0 hone h1)
              | Ceq =>
                  cases h0 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                      CompCert4Lean.Lib.Integers.Int.zero with
                  | left hzero =>
                      simpa [combine_cond, h0] using
                        (R_combine_cond_9 _ _ n rfl x rfl hzero h0)
                  | right hne =>
                      cases h1 : CompCert4Lean.Lib.Integers.Int.eq_dec n
                          CompCert4Lean.Lib.Integers.Int.one with
                      | left hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_10 _ _ n rfl x rfl hne h0 hone h1)
                      | right hone =>
                          simpa [combine_cond, h0, h1] using
                            (R_combine_cond_11 _ _ n rfl x rfl hne h0 hone h1)
              | _ =>
                  simpa [combine_cond] using
                    (R_combine_cond_12 _ [x] _ rfl [x] rfl (by simp_all))
          | _ =>
              simpa [combine_cond] using
                (R_combine_cond_12 _ [x] _ rfl [x] rfl (by simp_all))

end CompCert4Lean.X86.CombineOp
