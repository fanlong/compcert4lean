import CompCert4Lean.Backend.RTL
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.FSetAVLplus
import CompCert4Lean.Lib.Iteration
import CompCert4Lean.Lib.Ordered

/-!
# Elimination of unreferenced static definitions

Definition-bearing translation of CompCert's `backend/Unusedglob.v`.  The
generated `FSetAVL.Make(OrderedPositive)` surface uses a local instantiation
of the invariant-bearing AVL-set provider.
-/

namespace CompCert4Lean.Backend.Unusedglob

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Iteration
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

/-! ## Generated positive finite-set application -/

namespace IS

def IS : Type := Unit

open CompCert4Lean.Lib.FSetAVLplus
open CompCert4Lean.Lib.Ordered

private abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType

def E : OrderedType where
  t := OrderedPositive.t
  eq := OrderedPositive.eq
  lt := OrderedPositive.lt
  eq_refl := fun _ => rfl
  eq_sym := by intro x y h; exact h.symm
  eq_trans := by intro x y z hxy hyz; exact hxy.trans hyz
  lt_trans := by intro x y z hxy hyz; exact Nat.lt_trans hxy hyz
  lt_not_eq := by
    intro x y hxy heq
    cases heq
    exact Nat.lt_irrefl _ hxy
  compare := CompCert4Lean.Lib.Ordered.OrderedPositive.compare
  eq_dec := CompCert4Lean.Lib.Coqlib.peq

abbrev «X'» := E

namespace X'

abbrev t : Type := E.t
def eq : t → t → Prop := E.eq
def lt : t → t → Prop := E.lt

end X'

abbrev MSet := Make.MSet E

namespace MSet

abbrev Mkt (this : Make.Raw.tree E) (is_ok : Make.Raw.Ok this) : MSet :=
  @Make.MSet.Mkt E this is_ok
abbrev this := @Make.MSet.this E
abbrev is_ok := @Make.MSet.is_ok E

end MSet

abbrev MF := Make.MF E

namespace MF
end MF

namespace E
end E

abbrev elt : Type := Make.elt E
abbrev t : Type := Make.t E

def In : elt → t → Prop := Make.In
def Equal : t → t → Prop := Make.Equal
def Subset : t → t → Prop := Make.Subset
def Empty : t → Prop := Make.Empty
def For_all : (elt → Prop) → t → Prop := Make.For_all
def Exists : (elt → Prop) → t → Prop := Make.Exists

def empty : t := Make.empty
def is_empty : t → Bool := Make.is_empty
def mem : elt → t → Bool := Make.mem
def add : elt → t → t := Make.add
def singleton : elt → t := Make.singleton
def remove : elt → t → t := Make.remove
def union : t → t → t := Make.union
def inter : t → t → t := Make.inter
def diff : t → t → t := Make.diff
def eq : t → t → Prop := Make.eq
def eq_dec (s s' : t) :
    CompCert4Lean.Foundation.Logic.Support.Sumbool (eq s s') (¬ eq s s') :=
  Make.eq_dec s s'
def equal : t → t → Bool := Make.equal
def subset : t → t → Bool := Make.subset
def fold {A : Type} : (elt → A → A) → t → A → A := Make.fold
def for_all : (elt → Bool) → t → Bool := Make.for_all
def exists_ : (elt → Bool) → t → Bool := Make.exists_
def filter : (elt → Bool) → t → t := Make.filter
def partition : (elt → Bool) → t → t × t := Make.partition
def cardinal : t → Nat := Make.cardinal
def elements : t → List elt := Make.elements
def choose : t → Option elt := Make.choose
def lt : t → t → Prop := Make.lt
def min_elt : t → Option elt := Make.min_elt
def max_elt : t → Option elt := Make.max_elt

/-! Proof-bearing generated members are exact proposition/type descriptors. -/

private abbrev CompatBool (f : elt → Bool) : Prop :=
  CompCert4Lean.Lib.FSetInterface.compat_bool X'.eq f
private abbrev InA (x : elt) (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.InA X'.eq x l
private abbrev NoDupA (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.NoDupA X'.eq l
private abbrev Sorted (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.sort X'.lt l

def In_1 : Prop :=
  ∀ (s : t) (x y : elt), X'.eq x y → In x s → In y s
def eq_refl : Prop := ∀ s : t, eq s s
def eq_sym : Prop := ∀ s s' : t, eq s s' → eq s' s
def eq_trans : Prop :=
  ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''
def mem_1 : Prop := ∀ (s : t) (x : elt), In x s → mem x s = true
def mem_2 : Prop := ∀ (s : t) (x : elt), mem x s = true → In x s
def equal_1 : Prop :=
  ∀ s s' : t, Equal s s' → equal s s' = true
def equal_2 : Prop :=
  ∀ s s' : t, equal s s' = true → Equal s s'
def subset_1 : Prop :=
  ∀ s s' : t, Subset s s' → subset s s' = true
def subset_2 : Prop :=
  ∀ s s' : t, subset s s' = true → Subset s s'
def empty_1 : Prop := Empty empty
def is_empty_1 : Prop :=
  ∀ s : t, Empty s → is_empty s = true
def is_empty_2 : Prop :=
  ∀ s : t, is_empty s = true → Empty s
def add_1 : Prop :=
  ∀ (s : t) (x y : elt), X'.eq x y → In y (add x s)
def add_2 : Prop :=
  ∀ (s : t) (x y : elt), In y s → In y (add x s)
def add_3 : Prop :=
  ∀ (s : t) (x y : elt), ¬ X'.eq x y → In y (add x s) → In y s
def remove_1 : Prop :=
  ∀ (s : t) (x y : elt), X'.eq x y → ¬ In y (remove x s)
def remove_2 : Prop :=
  ∀ (s : t) (x y : elt), ¬ X'.eq x y → In y s → In y (remove x s)
def remove_3 : Prop :=
  ∀ (s : t) (x y : elt), In y (remove x s) → In y s
def union_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (union s s') → In x s ∨ In x s'
def union_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → In x (union s s')
def union_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s' → In x (union s s')
def inter_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (inter s s') → In x s
def inter_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x (inter s s') → In x s'
def inter_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → In x s' → In x (inter s s')
def diff_1 : Prop :=
  ∀ (s s' : t) (x : elt), In x (diff s s') → In x s
def diff_2 : Prop :=
  ∀ (s s' : t) (x : elt), In x (diff s s') → ¬ In x s'
def diff_3 : Prop :=
  ∀ (s s' : t) (x : elt), In x s → ¬ In x s' → In x (diff s s')
def singleton_1 : Prop :=
  ∀ x y : elt, In y (singleton x) → X'.eq x y
def singleton_2 : Prop :=
  ∀ x y : elt, X'.eq x y → In y (singleton x)
def fold_1 : Prop :=
  ∀ (s : t) (A : Type) (i : A) (f : elt → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)
def cardinal_1 : Prop :=
  ∀ s : t, cardinal s = (elements s).length
def filter_1 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x (filter f s) → In x s
def filter_2 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x (filter f s) → f x = true
def filter_3 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool f → In x s → f x = true → In x (filter f s)
def for_all_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → For_all (fun x => f x = true) s → for_all f s = true
def for_all_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → for_all f s = true → For_all (fun x => f x = true) s
def exists_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Exists (fun x => f x = true) s → exists_ f s = true
def exists_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → exists_ f s = true → Exists (fun x => f x = true) s
def partition_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Equal (partition f s).1 (filter f s)
def partition_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool f → Equal (partition f s).2 (filter (fun x => !(f x)) s)
def choose_1 : Prop :=
  ∀ (s : t) (x : elt), choose s = some x → In x s
def choose_2 : Prop :=
  ∀ s : t, choose s = none → Empty s
def elements_1 : Prop :=
  ∀ (s : t) (x : elt), In x s → InA x (elements s)
def elements_2 : Prop :=
  ∀ (s : t) (x : elt), InA x (elements s) → In x s
def elements_3w : Prop :=
  ∀ s : t, NoDupA (elements s)
def min_elt_1 : Prop :=
  ∀ (s : t) (x : elt), min_elt s = some x → In x s
def min_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), min_elt s = some x → In y s → ¬ X'.lt y x
def min_elt_3 : Prop :=
  ∀ s : t, min_elt s = none → Empty s
def max_elt_1 : Prop :=
  ∀ (s : t) (x : elt), max_elt s = some x → In x s
def max_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), max_elt s = some x → In y s → ¬ X'.lt x y
def max_elt_3 : Prop :=
  ∀ s : t, max_elt s = none → Empty s
def elements_3 : Prop :=
  ∀ s : t, Sorted (elements s)
def choose_3 : Prop :=
  ∀ (s s' : t) (x y : elt),
    choose s = some x → choose s' = some y → Equal s s' → X'.eq x y
def lt_trans : Prop :=
  ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''
def lt_not_eq : Prop :=
  ∀ s s' : t, lt s s' → ¬ eq s s'
def compare : Type :=
  ∀ s s' : t,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq s s'

end IS

/-! ## Referenced globals -/

structure workset : Type where
  w_seen : IS.t
  w_todo : List ident

export workset (w_seen w_todo)

instance : Coe workset IS.t where
  coe := workset.w_seen

def add_workset (id : ident) (w : workset) : workset :=
  if IS.mem id w.w_seen then
    w
  else
    { w_seen := IS.add id w.w_seen
      w_todo := id :: w.w_todo }

def addlist_workset : List ident → workset → workset
  | [], w => w
  | id :: rest, w => addlist_workset rest (add_workset id w)

def ref_instruction : instruction → List ident
  | .Inop _ => []
  | .Iop op _ _ _ => globals_operation op
  | .Iload _ addr _ _ _ => globals_addressing addr
  | .Istore _ addr _ _ _ => globals_addressing addr
  | .Icall _ (.inl _) _ _ _ => []
  | .Icall _ (.inr id) _ _ _ => [id]
  | .Itailcall _ (.inl _) _ => []
  | .Itailcall _ (.inr id) _ => [id]
  | .Ibuiltin _ args _ _ => globals_of_builtin_args args
  | .Icond _ _ _ _ => []
  | .Ijumptable _ _ => []
  | .Ireturn _ => []

def add_ref_instruction (w : workset) (_pc : node) (i : instruction) : workset :=
  addlist_workset (ref_instruction i) w

def add_ref_function (f : function) (w : workset) : workset :=
  PTree.fold add_ref_instruction f.fn_code w

def add_ref_init_data (w : workset) (i : init_data) : workset :=
  match i with
  | .Init_addrof id _ => add_workset id w
  | _ => w

def add_ref_globvar (gv : globvar Unit) (w : workset) : workset :=
  gv.gvar_init.foldl add_ref_init_data w

def prog_map : Type := PTree.t (globdef fundef Unit)

def add_ref_definition (pm : prog_map) (id : ident) (w : workset) : workset :=
  match PTree.get id pm with
  | none => w
  | some (.Gfun (.Internal f)) => add_ref_function f w
  | some (.Gfun (.External _)) => w
  | some (.Gvar gv) => add_ref_globvar gv w

def initial_workset (p : program) : workset :=
  add_workset p.prog_main
    (p.prog_public.foldl
      (fun w id => add_workset id w)
      { w_seen := IS.empty, w_todo := [] })

/-! ## Dependency-graph traversal -/

def iter_step (pm : prog_map) (w : workset) : Sum IS.t workset :=
  match w.w_todo with
  | [] => .inl w.w_seen
  | id :: remaining =>
      .inr (add_ref_definition pm id
        { w_seen := w.w_seen, w_todo := remaining })

def used_globals (p : program) (pm : prog_map) : Option IS.t :=
  PrimIter.iterate workset IS.t (iter_step pm) (initial_workset p)

/-! ## Filtering global definitions -/

def filter_globdefs (used : IS.t)
    (accu defs : List (ident × globdef fundef Unit)) :
    List (ident × globdef fundef Unit) :=
  match defs with
  | [] => accu
  | (id, gd) :: rest =>
      if IS.mem id used then
        filter_globdefs (IS.remove id used) ((id, gd) :: accu) rest
      else
        filter_globdefs used accu rest

def global_defined (p : program) (pm : prog_map) (id : ident) : Bool :=
  match PTree.get id pm with
  | some _ => true
  | none =>
      match ident_eq id p.prog_main with
      | .left _ => true
      | .right _ => false

private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private def rocqStringOfBytes : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (rocqStringOfBytes rest)

private def analysisFailedText : RocqString :=
  rocqStringOfBytes
    [85, 110, 117, 115, 101, 100, 103, 108, 111, 98, 58, 32, 97, 110, 97,
      108, 121, 115, 105, 115, 32, 102, 97, 105, 108, 101, 100]

private def undefinedGlobalText : RocqString :=
  rocqStringOfBytes
    [85, 110, 117, 115, 101, 100, 103, 108, 111, 98, 58, 32, 114, 101, 102,
      101, 114, 101, 110, 99, 101, 32, 116, 111, 32, 117, 110, 100, 101, 102,
      105, 110, 101, 100, 32, 103, 108, 111, 98, 97, 108]

def transform_program (p : program) : res program :=
  let pm := prog_defmap p
  match used_globals p pm with
  | none => .Error (msg analysisFailedText)
  | some used =>
      if IS.for_all (global_defined p pm) used then
        .OK
          { prog_defs := filter_globdefs used [] p.prog_defs.reverse
            prog_public := p.prog_public
            prog_main := p.prog_main }
      else
        .Error (msg undefinedGlobalText)

end CompCert4Lean.Backend.Unusedglob

namespace CompCert4Lean.Backend.Unusedglob.IS

theorem mem_1_proof : mem_1 := by
  intro s x h
  exact CompCert4Lean.Lib.FSetAVLplus.Make.mem_1 s x h

theorem add_2_proof : add_2 := by
  intro s x y h
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2 s x y h

theorem remove_2_proof : remove_2 := by
  intro s x y hne h
  exact CompCert4Lean.Lib.FSetAVLplus.Make.remove_2 s x y hne h

theorem add_3_proof : add_3 := by
  intro s x y hne h
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_3 s x y hne h

end CompCert4Lean.Backend.Unusedglob.IS

namespace CompCert4Lean.Backend.Unusedglob.IS

theorem add_1_proof : add_1 := by
  intro s x y hxy
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_1 s x y hxy

theorem mem_2_proof : mem_2 := by
  intro s x h
  exact CompCert4Lean.Lib.FSetAVLplus.Make.mem_2 s x h

theorem empty_1_proof : empty_1 := by
  exact CompCert4Lean.Lib.FSetAVLplus.Make.empty_1

end CompCert4Lean.Backend.Unusedglob.IS
