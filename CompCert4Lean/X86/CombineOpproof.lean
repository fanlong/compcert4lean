import CompCert4Lean.X86.CombineOp
import CompCert4Lean.Backend.RTL

/-!
# Correctness surface for combined x86 operations

The source proofs in `x86/CombineOpproof.v` are migrated in a later proof
phase.  This module records their exact proposition statements and keeps the
source combinators available through private adapters while their definition
provider is completed.
-/

namespace CompCert4Lean.X86.CombineOpproof

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.CSEdomain
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.CombineOp

private abbrev valnum := CompCert4Lean.X86.CombineOp.valnum
private abbrev rhs := CompCert4Lean.Backend.CSEdomain.rhs
private abbrev condition := CompCert4Lean.X86.Op.condition
private abbrev addressing := CompCert4Lean.X86.Op.addressing
private abbrev operation := CompCert4Lean.X86.Op.operation
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem

private def combine_compimm_ne_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | some (.Op (.Oandimm n) ys) => some (.Cmasknotzero n, ys)
  | some (.Op (.Oxorimm n) ys) => some (.Ccompimm .Cne n, ys)
  | _ => none

private def combine_compimm_eq_0 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negate_condition c, ys)
  | some (.Op (.Oandimm n) ys) => some (.Cmaskzero n, ys)
  | some (.Op (.Oxorimm n) ys) => some (.Ccompimm .Ceq n, ys)
  | _ => none

private def combine_compimm_eq_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | _ => none

private def combine_compimm_ne_1 (get : valnum → Option rhs) (x : valnum) :
    Option (condition × List valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negate_condition c, ys)
  | _ => none

private def combine_cond (get : valnum → Option rhs) (cond : condition)
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

private def combine_addr_32 (get : valnum → Option rhs) (addr : addressing)
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

private def combine_addr_64 (get : valnum → Option rhs) (addr : addressing)
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

private def combine_op (get : valnum → Option rhs) (op : operation)
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

def combine_compimm_ne_0_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_ne_0 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Cne (valu x) (.Vint Int.zero) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Cne (valu x) (.Vint Int.zero)

def combine_compimm_eq_0_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_eq_0 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Ceq (valu x) (.Vint Int.zero) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Ceq (valu x) (.Vint Int.zero)

def combine_compimm_eq_1_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_eq_1 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Ceq (valu x) (.Vint Int.one) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Ceq (valu x) (.Vint Int.one)

def combine_compimm_ne_1_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (x : valnum) (cond : condition) (args : List valnum),
    combine_compimm_ne_1 get x = some (cond, args) →
    eval_condition cond (List.map valu args) m =
        Val.cmp_bool .Cne (valu x) (.Vint Int.one) ∧
    eval_condition cond (List.map valu args) m =
        Val.cmpu_bool (Mem.valid_pointer m) .Cne (valu x) (.Vint Int.one)

def combine_cond_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (cond : condition) (args : List valnum) (cond' : condition)
      (args' : List valnum),
    combine_cond get cond args = some (cond', args') →
    eval_condition cond' (List.map valu args') m =
      eval_condition cond (List.map valu args) m

def combine_cond'_soundStatement : Prop :=
  ∀ (m : mem) (valu : valnum → val) (cond : condition)
    (args : List valnum) (res res' : Bool),
    combine_cond' cond args = some res' →
    eval_condition cond (List.map valu args) m = some res →
    res = res'

def combine_addr_32_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (addr : addressing) (args : List valnum) (addr' : addressing)
      (args' : List valnum),
    combine_addr_32 get addr args = some (addr', args') →
    eval_addressing32 ge sp addr' (List.map valu args') =
      eval_addressing32 ge sp addr (List.map valu args)

def combine_addr_64_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (addr : addressing) (args : List valnum) (addr' : addressing)
      (args' : List valnum),
    combine_addr_64 get addr args = some (addr', args') →
    eval_addressing64 ge sp addr' (List.map valu args') =
      eval_addressing64 ge sp addr (List.map valu args)

def combine_addr_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (addr : addressing) (args : List valnum) (addr' : addressing)
      (args' : List valnum),
    combine_addr get addr args = some (addr', args') →
    eval_addressing ge sp addr' (List.map valu args') =
      eval_addressing ge sp addr (List.map valu args)

def combine_op_soundStatement : Prop :=
  ∀ (ge : genv) (sp : val) (m : mem) (get : valnum → Option rhs)
    (valu : valnum → val),
    (∀ (v : valnum) (rh : rhs), get v = some rh →
      rhs_eval_to valu ge sp m rh (valu v)) →
    ∀ (op : operation) (args : List valnum) (op' : operation)
      (args' : List valnum) (r : val),
    combine_op get op args = some (op', args') →
    eval_operation ge sp op (List.map valu args) m = some r →
    ∃ r', eval_operation ge sp op' (List.map valu args') m = some r' ∧
      Val.lessdef r r'

end CompCert4Lean.X86.CombineOpproof
