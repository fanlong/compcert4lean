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

end CompCert4Lean.X86.CombineOp
