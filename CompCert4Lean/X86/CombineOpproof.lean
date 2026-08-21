import CompCert4Lean.X86.CombineOp
import CompCert4Lean.Backend.RTL

/-!
# Correctness surface for combined x86 operations

The source proofs in `x86/CombineOpproof.v` are migrated in a later proof
phase.  This module records their exact proposition statements against the
canonical combinators from `CombineOp`.
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
