import CompCert4Lean.Backend.Kildall
import CompCert4Lean.Backend.RTL

/-!
# RTL liveness analysis

This module translates the executable definitions from CompCert's
`backend/Liveness.v`.  The two local functor applications are exposed through
source-named adapters over the integrated register-set and Kildall providers.
Their proof-valued generated members are retained as exact proposition
descriptors for later proof migration.
-/

namespace CompCert4Lean.Backend.Liveness

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps

abbrev reg_live : reg → Regset.t → Regset.t :=
  Regset.add

abbrev reg_dead : reg → Regset.t → Regset.t :=
  Regset.remove

def reg_option_live (or : Option reg) (lv : Regset.t) : Regset.t :=
  match or with
  | none => lv
  | some r => reg_live r lv

def reg_sum_live (ros : Sum reg ident) (lv : Regset.t) : Regset.t :=
  match ros with
  | .inl r => reg_live r lv
  | .inr _ => lv

def reg_list_live : List reg → Regset.t → Regset.t
  | [], lv => lv
  | r :: rs, lv => reg_list_live rs (reg_live r lv)

def reg_list_dead : List reg → Regset.t → Regset.t
  | [], lv => lv
  | r :: rs, lv => reg_list_dead rs (reg_dead r lv)

def transfer (f : function) (pc : node) (after : Regset.t) : Regset.t :=
  match PTree.get pc f.fn_code with
  | none => Regset.empty
  | some i =>
      match i with
      | Inop _ => after
      | Iop _ args res _ =>
          if Regset.mem res after then
            reg_list_live args (reg_dead res after)
          else
            after
      | Iload _ _ args dst _ =>
          if Regset.mem dst after then
            reg_list_live args (reg_dead dst after)
          else
            after
      | Istore _ _ args src _ =>
          reg_list_live args (reg_live src after)
      | Icall _ ros args res _ =>
          reg_list_live args (reg_sum_live ros (reg_dead res after))
      | Itailcall _ ros args =>
          reg_list_live args (reg_sum_live ros Regset.empty)
      | Ibuiltin _ args res _ =>
          reg_list_live (params_of_builtin_args args)
            (reg_list_dead (params_of_builtin_res res) after)
      | Icond _ args _ _ =>
          reg_list_live args after
      | Ijumptable arg _ =>
          reg_live arg after
      | Ireturn optarg =>
          reg_option_live optarg Regset.empty

/-! ## Generated surface for `LFSet(Regset)` -/

namespace RegsetLat

abbrev t : Type := Regset.t

def eq (x y : t) : Prop :=
  Regset.Equal x y

def eq_refl : Prop :=
  ∀ x : t, eq x x

def eq_sym : Prop :=
  ∀ x y : t, eq x y → eq y x

def eq_trans : Prop :=
  ∀ x y z : t, eq x y → eq y z → eq x z

def beq (x y : t) : Bool :=
  Regset.equal x y

def beq_correct : Prop :=
  ∀ x y : t, beq x y = true → eq x y

def ge (x y : t) : Prop :=
  Regset.Subset y x

def ge_refl : Prop :=
  ∀ x y : t, eq x y → ge x y

def ge_trans : Prop :=
  ∀ x y z : t, ge x y → ge y z → ge x z

def bot : t :=
  Regset.empty

def ge_bot : Prop :=
  ∀ x : t, ge x bot

def lub (x y : t) : t :=
  Regset.union x y

def ge_lub_left : Prop :=
  ∀ x y : t, ge (lub x y) x

def ge_lub_right : Prop :=
  ∀ x y : t, ge (lub x y) y

def RegsetLat : Type :=
  Unit

private def semiLattice : SemiLattice :=
  { t := t
    bot := bot
    lub := lub
    beq := beq
    eq := eq
    ge := ge }

end RegsetLat

/-!
## Generated surface for
`Backward_Dataflow_Solver(RegsetLat)(NodeSetBackward)`
-/

namespace DS

def L : SemiLattice :=
  RegsetLat.semiLattice

def DS : Type :=
  Backward_Dataflow_Solver.DS L NodeSetBackward

def fixpoint {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) : Option (PMap.t L.t) :=
  Backward_Dataflow_Solver.fixpoint L NodeSetBackward code successors transf

def fixpoint_solution : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint code successors transf = some res →
    PTree.get n code = some instr →
    s ∈ successors instr →
    (∀ (n₀ : positive) (a : L.t),
      PTree.get n₀ code = none → L.eq (transf n₀ a) L.bot) →
    L.ge (PMap.get n res) (transf s (PMap.get s res))

def fixpoint_allnodes {A : Type} (code : PTree.t A)
    (successors : A → List positive)
    (transf : positive → L.t → L.t) : Option (PMap.t L.t) :=
  Backward_Dataflow_Solver.fixpoint_allnodes L NodeSetBackward
    code successors transf

def fixpoint_allnodes_solution : Prop :=
  ∀ (A : Type) (code : PTree.t A) (successors : A → List positive)
    (transf : positive → L.t → L.t) (res : PMap.t L.t)
    (n : positive) (instr : A) (s : positive),
    fixpoint_allnodes code successors transf = some res →
    PTree.get n code = some instr →
    s ∈ successors instr →
    L.ge (PMap.get n res) (transf s (PMap.get s res))

end DS

def analyze (f : function) : Option (PMap.t Regset.t) :=
  DS.fixpoint f.fn_code successors_instr (transfer f)

def last_uses_at (live : PMap.t Regset.t) (pc : node)
    (i : instruction) : List reg :=
  let l := PMap.get pc live
  let lu := (instr_uses i).filter (fun r => !(Regset.mem r l))
  match instr_defs i with
  | none => lu
  | some r => if Regset.mem r l then lu else r :: lu

def last_uses (f : function) : PTree.t (List reg) :=
  match analyze f with
  | none => PTree.empty (List reg)
  | some live => PTree.map (last_uses_at live) f.fn_code

end CompCert4Lean.Backend.Liveness
