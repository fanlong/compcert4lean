import CompCert4Lean.Backend.ValueDomain

/-!
# Common-subexpression elimination value-numbering domain

Definition-bearing translation of CompCert's `backend/CSEdomain.v`. Proofs
assigned to later migration are retained as exact proposition descriptors.
-/

namespace CompCert4Lean.Backend.CSEdomain

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Backend.ValueDomain
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Builtins
open CompCert4Lean.Common.Events
open CompCert4Lean.Common.Globalenvs
open CompCert4Lean.Common.Memory
open CompCert4Lean.Common.Values
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev val := CompCert4Lean.Common.Values.val
private abbrev mem := CompCert4Lean.Common.Memory.mem
private abbrev genv := CompCert4Lean.Backend.RTL.genv
private abbrev regset := CompCert4Lean.Backend.RTL.regset
private abbrev reg := CompCert4Lean.Backend.Registers.reg
private abbrev comparison := CompCert4Lean.Lib.Integers.comparison

private def boolOfSumbool {P Q : Prop} : Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

def valnum : Type := positive

inductive rhs : Type where
  | Op (op : operation) (vl : List valnum)
  | Load (chunk : memory_chunk) (addr : addressing) (vl : List valnum) (p : aptr)
  | Builtin (bf : builtin_function) (args : List (builtin_arg valnum))

export rhs (Op Load Builtin)

inductive equation : Type where
  | Eq (v : valnum) (strict : Bool) (r : rhs)

export equation (Eq)

def eq_valnum (x y : valnum) : Sumbool (x = y) (x ≠ y) :=
  peq x y

def eq_list_valnum (x y : List valnum) : Sumbool (x = y) (x ≠ y) :=
  list_eq_dec peq x y

/- Equality of right-hand sides, ignoring the region carried by loads. -/

def rhs_compat (r1 r2 : rhs) : Prop :=
  match r1, r2 with
  | Op op1 vl1, Op op2 vl2 => op1 = op2 ∧ vl1 = vl2
  | Load chunk1 addr1 vl1 _, Load chunk2 addr2 vl2 _ =>
      chunk1 = chunk2 ∧ addr1 = addr2 ∧ vl1 = vl2
  | Builtin bf1 args1, Builtin bf2 args2 => bf1 = bf2 ∧ args1 = args2
  | _, _ => False

def compat_rhs (r1 r2 : rhs) : Bool :=
  match r1, r2 with
  | Op op1 vl1, Op op2 vl2 =>
      boolOfSumbool (eq_operation op1 op2) &&
        boolOfSumbool (eq_list_valnum vl1 vl2)
  | Load chunk1 addr1 vl1 _, Load chunk2 addr2 vl2 _ =>
      boolOfSumbool (chunk_eq chunk1 chunk2) &&
        boolOfSumbool (eq_addressing addr1 addr2) &&
        boolOfSumbool (eq_list_valnum vl1 vl2)
  | Builtin bf1 args1, Builtin bf2 args2 =>
      boolOfSumbool (eq_builtin_function bf1 bf2) &&
        boolOfSumbool (list_eq_dec (eq_builtin_arg eq_valnum) args1 args2)
  | _, _ => false

structure numbering : Type where
  num_next : valnum
  num_eqs : List equation
  num_reg : PTree.t valnum
  num_val : PMap.t (List reg)

export numbering (num_next num_eqs num_reg num_val)

def empty_numbering : numbering :=
  { num_next := .xH
    num_eqs := []
    num_reg := PTree.empty valnum
    num_val := PMap.init ([] : List reg) }

def valnums_rhs (r : rhs) : List valnum :=
  match r with
  | Op _ vl => vl
  | Load _ _ vl _ => vl
  | Builtin _ args => params_of_builtin_args args

def wf_rhs (next : valnum) (r : rhs) : Prop :=
  ∀ v, In v (valnums_rhs r) → Plt v next

def wf_equation (next : valnum) (e : equation) : Prop :=
  match e with
  | Eq l _ r => Plt l next ∧ wf_rhs next r

/- The reverse-map consistency field is retained in the parent proposition;
   only the packet-owned generated projections are exposed below. -/
def wf_numbering (n : numbering) : Prop :=
  (∀ e, In e n.num_eqs → wf_equation n.num_next e) ∧
  (∀ r v, PTree.get r n.num_reg = some v → Plt v n.num_next) ∧
  (∀ r v, In r (PMap.get v n.num_val) → PTree.get r n.num_reg = some v)

def wf_num_eqs {n : numbering} (h : wf_numbering n) :
    ∀ e, In e n.num_eqs → wf_equation n.num_next e := h.1

def wf_num_reg {n : numbering} (h : wf_numbering n) :
    ∀ r v, PTree.get r n.num_reg = some v → Plt v n.num_next := h.2.1

def wf_num_val {n : numbering} (h : wf_numbering n) :
    ∀ r v, In r (PMap.get v n.num_val) → PTree.get r n.num_reg = some v := h.2.2

def valuation : Type := valnum → val

def rhs_eval_to (valu : valuation) (ge : genv) (sp : val) (m : mem)
    (r : rhs) (v : val) : Prop :=
  match r with
  | Op op vl => eval_operation ge sp op (List.map valu vl) m = some v
  | Load chunk addr vl _ =>
      ∃ a, eval_addressing ge sp addr (List.map valu vl) = some a ∧
        Mem.loadv chunk m a = some v
  | Builtin bf args =>
      ∃ vargs, eval_builtin_args (Genv.to_senv ge) valu sp m args vargs ∧
        builtin_function_sem bf vargs = some v

def load_eval_to (valu : valuation) (ge : genv) (sp : val) (m : mem)
    (chunk : memory_chunk) (addr : addressing) (vl : List valnum)
    (a v : val) (p : aptr)
    (haddr : eval_addressing ge sp addr (List.map valu vl) = some a)
    (hload : Mem.loadv chunk m a = some v) :
    rhs_eval_to valu ge sp m (Load chunk addr vl p) v :=
  ⟨a, haddr, hload⟩

def rhs_valid (valu : valuation) (ge : genv) (sp : val) (r : rhs) : Prop :=
  match r with
  | Op _ _ => True
  | Load chunk addr vl p =>
      ∃ spb b ofs bc,
        sp = Vptr spb Ptrofs.zero ∧
        eval_addressing ge (Vptr spb Ptrofs.zero) addr (List.map valu vl) =
          some (Vptr b ofs) ∧
        pmatch bc b ofs p ∧ genv_match bc ge ∧ bc spb = BCstack
  | Builtin _ _ => True

def equation_holds (valu : valuation) (ge : genv) (sp : val) (m : mem)
    (e : equation) : Prop :=
  match e with
  | Eq l true r => rhs_eval_to valu ge sp m r (valu l) ∧ rhs_valid valu ge sp r
  | Eq l false r =>
      ∃ v, rhs_eval_to valu ge sp m r v ∧ Val.lessdef v (valu l) ∧
        rhs_valid valu ge sp r

def eq_holds_strict (valu : valuation) (ge : genv) (sp : val) (m : mem)
    (l : valnum) (r : rhs)
    (hev : rhs_eval_to valu ge sp m r (valu l))
    (hvalid : rhs_valid valu ge sp r) :
    equation_holds valu ge sp m (Eq l true r) :=
  ⟨hev, hvalid⟩

def eq_holds_lessdef (valu : valuation) (ge : genv) (sp : val) (m : mem)
    (l : valnum) (r : rhs) (v : val)
    (hev : rhs_eval_to valu ge sp m r v)
    (hlessdef : Val.lessdef v (valu l))
    (hvalid : rhs_valid valu ge sp r) :
    equation_holds valu ge sp m (Eq l false r) :=
  ⟨v, hev, hlessdef, hvalid⟩

def numbering_holds (valu : valuation) (ge : genv) (sp : val)
    (rs : regset) (m : mem) (n : numbering) : Prop :=
  wf_numbering n ∧
  (∀ e, In e n.num_eqs → equation_holds valu ge sp m e) ∧
  (∀ r v, PTree.get r n.num_reg = some v → Regmap.get r rs = valu v)

def num_holds_wf {valu : valuation} {ge : genv} {sp : val} {rs : regset}
    {m : mem} {n : numbering} (h : numbering_holds valu ge sp rs m n) :
    wf_numbering n := h.1

def num_holds_eq {valu : valuation} {ge : genv} {sp : val} {rs : regset}
    {m : mem} {n : numbering} (h : numbering_holds valu ge sp rs m n) :
    ∀ e, In e n.num_eqs → equation_holds valu ge sp m e := h.2.1

def num_holds_reg {valu : valuation} {ge : genv} {sp : val} {rs : regset}
    {m : mem} {n : numbering} (h : numbering_holds valu ge sp rs m n) :
    ∀ r v, PTree.get r n.num_reg = some v → Regmap.get r rs = valu v := h.2.2

def combine_comparison (c : comparison) (x y : valnum) : Option Bool :=
  match eq_valnum x y with
  | .left _ =>
      some (match c with
        | .Ceq | .Cle | .Cge => true
        | .Cne | .Clt | .Cgt => false)
  | .right _ => none

/-! Exact statements of proofs assigned to the later proof-migration phase. -/

def rhs_compat_symStatement : Prop :=
  ∀ rh1 rh2, rhs_compat rh1 rh2 → rhs_compat rh2 rh1

def compat_rhs_soundStatement : Prop :=
  ∀ r1 r2, compat_rhs r1 r2 = true → rhs_compat r1 r2

def rhs_eval_to_compatStatement : Prop :=
  ∀ valu ge sp m rh v rh',
    rhs_eval_to valu ge sp m rh v →
    rhs_compat rh rh' →
    rhs_eval_to valu ge sp m rh' v

def empty_numbering_holdsStatement : Prop :=
  ∀ valu ge sp rs m, numbering_holds valu ge sp rs m empty_numbering

def combine_comparison_cmp_soundStatement : Prop :=
  ∀ (valu : valnum → val) c x y res res',
    combine_comparison c x y = some res' →
    Val.cmp_bool c (valu x) (valu y) = some res →
    res = res'

def combine_comparison_cmpu_soundStatement : Prop :=
  ∀ (valu : valnum → val) m c x y res res',
    combine_comparison c x y = some res' →
    Val.cmpu_bool (Mem.valid_pointer m) c (valu x) (valu y) = some res →
    res = res'

def combine_comparison_cmpl_soundStatement : Prop :=
  ∀ (valu : valnum → val) c x y res res',
    combine_comparison c x y = some res' →
    Val.cmpl_bool c (valu x) (valu y) = some res →
    res = res'

def combine_comparison_cmplu_soundStatement : Prop :=
  ∀ (valu : valnum → val) m c x y res res',
    combine_comparison c x y = some res' →
    Val.cmplu_bool (Mem.valid_pointer m) c (valu x) (valu y) = some res →
    res = res'

end CompCert4Lean.Backend.CSEdomain
