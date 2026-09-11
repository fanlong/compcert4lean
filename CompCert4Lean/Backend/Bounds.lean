import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.Registers
import CompCert4Lean.Lib.FSetAVLplus
import CompCert4Lean.X86.Conventions1

/-! Definition translation of `backend/Bounds.v`. -/

namespace CompCert4Lean.Backend.Bounds

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Conventions1
open CompCert4Lean.Lib.Coqlib

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev z0 : Z := .Z0
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zMax := ZArith.BinInt.Z.max
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zGe := ZArith.BinInt.Z.ge
private abbrev function := CompCert4Lean.Backend.Linear.function
private abbrev instruction := CompCert4Lean.Backend.Linear.instruction

private abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType
private abbrev Compare {X : Type} (lt eq : X → X → Prop) (x y : X) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
    lt eq x y
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool

private def mregDecEq : DecidableEq mreg := by
  intro x y
  cases x <;> cases y <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

private instance : DecidableEq mreg := mregDecEq

/-! Generated surfaces owned by the local ordered-type and finite-set applications. -/

namespace RegOrd

abbrev t := mreg

def eq (x y : t) : Prop := x = y

def lt (x y : t) : Prop :=
  CompCert4Lean.Lib.Coqlib.Plt
    (CompCert4Lean.X86.Machregs.IndexedMreg.index x)
    (CompCert4Lean.X86.Machregs.IndexedMreg.index y)

private def rank : mreg → Nat
  | .AX => 1
  | .BX => 2
  | .CX => 3
  | .DX => 4
  | .SI => 5
  | .DI => 6
  | .BP => 7
  | .R8 => 8
  | .R9 => 9
  | .R10 => 10
  | .R11 => 11
  | .R12 => 12
  | .R13 => 13
  | .R14 => 14
  | .R15 => 15
  | .X0 => 16
  | .X1 => 17
  | .X2 => 18
  | .X3 => 19
  | .X4 => 20
  | .X5 => 21
  | .X6 => 22
  | .X7 => 23
  | .X8 => 24
  | .X9 => 25
  | .X10 => 26
  | .X11 => 27
  | .X12 => 28
  | .X13 => 29
  | .X14 => 30
  | .X15 => 31
  | .FP0 => 32

private theorem index_rank (r : mreg) :
    CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
        (CompCert4Lean.X86.Machregs.IndexedMreg.index r) = rank r := by
  cases r <;> decide

private theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> simp [rank] at h ⊢

private theorem index_injective :
    Function.Injective CompCert4Lean.X86.Machregs.IndexedMreg.index := by
  intro x y h
  apply rank_injective
  rw [← index_rank x, ← index_rank y, h]

theorem eq_refl : ∀ x : t, eq x x := by
  intro x
  rfl

theorem eq_sym : ∀ x y : t, eq x y → eq y x := by
  intro x y h
  exact h.symm

theorem eq_trans : ∀ x y z : t, eq x y → eq y z → eq x z := by
  intro x y z hxy hyz
  exact hxy.trans hyz

theorem lt_trans : ∀ x y z : t, lt x y → lt y z → lt x z := by
  intro x y z hxy hyz
  exact Nat.lt_trans hxy hyz

theorem lt_not_eq : ∀ x y : t, lt x y → ¬ eq x y := by
  intro x y hxy hEq
  cases hEq
  exact Nat.lt_irrefl _ hxy

def compare (x y : t) : Compare lt eq x y := by
  cases CompCert4Lean.Lib.Coqlib.plt
      (CompCert4Lean.X86.Machregs.IndexedMreg.index x)
      (CompCert4Lean.X86.Machregs.IndexedMreg.index y) with
  | left hlt =>
      exact .LT hlt
  | right hlt =>
      cases mregDecEq x y with
      | isTrue heq =>
          exact .EQ heq
      | isFalse heq =>
          refine .GT ?_
          change
            CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
                (CompCert4Lean.X86.Machregs.IndexedMreg.index y) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
                (CompCert4Lean.X86.Machregs.IndexedMreg.index x)
          change
            ¬ CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
                (CompCert4Lean.X86.Machregs.IndexedMreg.index x) <
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
                (CompCert4Lean.X86.Machregs.IndexedMreg.index y) at hlt
          have hne :
              CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
                  (CompCert4Lean.X86.Machregs.IndexedMreg.index x) ≠
                CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.to_nat
                  (CompCert4Lean.X86.Machregs.IndexedMreg.index y) := by
            intro h
            apply heq
            exact index_injective (posToNat_injective h)
          omega

def eq_dec (x y : t) : Sumbool (eq x y) (¬ eq x y) :=
  match mregDecEq x y with
  | isTrue h => .left h
  | isFalse h => .right h

def EOrder : OrderedType where
  t := t
  eq := eq
  lt := lt
  eq_refl := eq_refl
  eq_sym := eq_sym
  eq_trans := eq_trans
  lt_trans := lt_trans
  lt_not_eq := lt_not_eq
  compare := compare
  eq_dec := eq_dec

end RegOrd

namespace RegSet

open CompCert4Lean.Lib.FSetAVLplus

private abbrev EOrder : OrderedType := RegOrd.EOrder

abbrev «X'» : Type := EOrder.t

namespace X'

abbrev orderedType : OrderedType := EOrder
abbrev t : Type := EOrder.t
abbrev eq : t → t → Prop := EOrder.eq
abbrev lt : t → t → Prop := EOrder.lt

end X'

abbrev MSet : Type := Make.MSet EOrder

namespace MSet

abbrev Mkt (this : Make.Raw.tree EOrder) (is_ok : Make.Raw.Ok this) : MSet :=
  @Make.MSet.Mkt EOrder this is_ok
abbrev this : MSet → Make.Raw.tree EOrder := @Make.MSet.this EOrder
abbrev is_ok (self : MSet) : Make.Raw.Ok (@Make.MSet.this EOrder self) :=
  @Make.MSet.is_ok EOrder self

end MSet

abbrev MFType := CompCert4Lean.Lib.FSetFacts.WFacts_fun
  (CompCert4Lean.Lib.FSetInterface.OrderedType.toDecidableType EOrder)
  (Make.toSfun EOrder).toWSfun
def MFProvider : MFType := Make.MF EOrder
abbrev MF : Type := PLift (Nonempty MFType)

namespace MF

abbrev provider : MFType := MFProvider

end MF

abbrev E : Type := EOrder.t

namespace E

abbrev orderedType : OrderedType := EOrder
abbrev t : Type := EOrder.t
abbrev eq : t → t → Prop := EOrder.eq
abbrev lt : t → t → Prop := EOrder.lt
abbrev compare := EOrder.compare
abbrev eq_dec := EOrder.eq_dec

end E

abbrev elt : Type := Make.elt EOrder
abbrev t : Type := Make.t EOrder

abbrev In : elt → t → Prop := Make.In (X := EOrder)
abbrev Equal : t → t → Prop := Make.Equal (X := EOrder)
abbrev Subset : t → t → Prop := Make.Subset (X := EOrder)
abbrev Empty : t → Prop := Make.Empty (X := EOrder)
abbrev For_all : (elt → Prop) → t → Prop := Make.For_all (X := EOrder)
abbrev Exists : (elt → Prop) → t → Prop := Make.Exists (X := EOrder)

abbrev empty : t := Make.empty (X := EOrder)
abbrev is_empty : t → Bool := Make.is_empty (X := EOrder)
abbrev mem : elt → t → Bool := Make.mem (X := EOrder)
abbrev add : elt → t → t := Make.add (X := EOrder)
abbrev singleton : elt → t := Make.singleton (X := EOrder)
abbrev remove : elt → t → t := Make.remove (X := EOrder)
abbrev union : t → t → t := Make.union (X := EOrder)
abbrev inter : t → t → t := Make.inter (X := EOrder)
abbrev diff : t → t → t := Make.diff (X := EOrder)
abbrev eq : t → t → Prop := Make.eq (X := EOrder)
abbrev eq_dec := Make.eq_dec (X := EOrder)
abbrev equal : t → t → Bool := Make.equal (X := EOrder)
abbrev subset : t → t → Bool := Make.subset (X := EOrder)
abbrev fold {A : Type} (f : elt → A → A) (s : t) (i : A) : A :=
  Make.fold (X := EOrder) f s i
abbrev for_all : (elt → Bool) → t → Bool := Make.for_all (X := EOrder)
abbrev exists_ : (elt → Bool) → t → Bool := Make.exists_ (X := EOrder)
abbrev filter : (elt → Bool) → t → t := Make.filter (X := EOrder)
abbrev partition : (elt → Bool) → t → t × t := Make.partition (X := EOrder)
abbrev cardinal : t → Nat := Make.cardinal (X := EOrder)
abbrev elements : t → List elt := Make.elements (X := EOrder)
abbrev choose : t → Option elt := Make.choose (X := EOrder)
abbrev lt : t → t → Prop := Make.lt (X := EOrder)
abbrev min_elt : t → Option elt := Make.min_elt (X := EOrder)
abbrev max_elt : t → Option elt := Make.max_elt (X := EOrder)

private abbrev CompatBool (f : elt → Bool) : Prop :=
  CompCert4Lean.Lib.FSetInterface.compat_bool EOrder.eq f

def In_1 : Prop :=
  ∀ (s : t) (x y : elt), EOrder.eq x y → In x s → In y s
def eq_refl : Prop := ∀ s : t, eq s s
def eq_sym : Prop := ∀ s s' : t, eq s s' → eq s' s
def eq_trans : Prop := ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''
def mem_1 : Prop := ∀ (s : t) (x : elt), In x s → mem x s = true
def mem_2 : Prop := ∀ (s : t) (x : elt), mem x s = true → In x s
def equal_1 : Prop := ∀ s s' : t, Equal s s' → equal s s' = true
def equal_2 : Prop := ∀ s s' : t, equal s s' = true → Equal s s'
def subset_1 : Prop := ∀ s s' : t, Subset s s' → subset s s' = true
def subset_2 : Prop := ∀ s s' : t, subset s s' = true → Subset s s'
def empty_1 : Prop := Empty empty
def is_empty_1 : Prop := ∀ s : t, Empty s → is_empty s = true
def is_empty_2 : Prop := ∀ s : t, is_empty s = true → Empty s
def add_1 : Prop :=
  ∀ (s : t) (x y : elt), EOrder.eq x y → In y (add x s)
def add_2 : Prop := ∀ (s : t) (x y : elt), In y s → In y (add x s)
def add_3 : Prop :=
  ∀ (s : t) (x y : elt), ¬ EOrder.eq x y → In y (add x s) → In y s
def remove_1 : Prop :=
  ∀ (s : t) (x y : elt), EOrder.eq x y → ¬ In y (remove x s)
def remove_2 : Prop :=
  ∀ (s : t) (x y : elt), ¬ EOrder.eq x y → In y s → In y (remove x s)
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
  ∀ x y : elt, In y (singleton x) → EOrder.eq x y
def singleton_2 : Prop :=
  ∀ x y : elt, EOrder.eq x y → In y (singleton x)
def fold_1 : Prop :=
  ∀ (s : t) (A : Type) (i : A) (f : elt → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)
def cardinal_1 : Prop := ∀ s : t, cardinal s = (elements s).length
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
    CompatBool f →
      Equal (partition f s).2 (filter (fun x => !(f x)) s)
def choose_1 : Prop :=
  ∀ (s : t) (x : elt), choose s = some x → In x s
def choose_2 : Prop := ∀ s : t, choose s = none → Empty s
def elements_1 : Prop :=
  ∀ (s : t) (x : elt), In x s →
    CompCert4Lean.Lib.FSetInterface.InA EOrder.eq x (elements s)
def elements_2 : Prop :=
  ∀ (s : t) (x : elt),
    CompCert4Lean.Lib.FSetInterface.InA EOrder.eq x (elements s) → In x s
def elements_3w : Prop :=
  ∀ s : t, CompCert4Lean.Lib.FSetInterface.NoDupA EOrder.eq (elements s)
def min_elt_1 : Prop :=
  ∀ (s : t) (x : elt), min_elt s = some x → In x s
def min_elt_2 : Prop :=
  ∀ (s : t) (x y : elt),
    min_elt s = some x → In y s → ¬ EOrder.lt y x
def min_elt_3 : Prop := ∀ s : t, min_elt s = none → Empty s
def max_elt_1 : Prop :=
  ∀ (s : t) (x : elt), max_elt s = some x → In x s
def max_elt_2 : Prop :=
  ∀ (s : t) (x y : elt),
    max_elt s = some x → In y s → ¬ EOrder.lt x y
def max_elt_3 : Prop := ∀ s : t, max_elt s = none → Empty s
def elements_3 : Prop :=
  ∀ s : t, CompCert4Lean.Lib.FSetInterface.sort EOrder.lt (elements s)
def choose_3 : Prop :=
  ∀ (s s' : t) (x y : elt),
    choose s = some x → choose s' = some y → Equal s s' → EOrder.eq x y
def lt_trans : Prop :=
  ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''
def lt_not_eq : Prop := ∀ s s' : t, lt s s' → ¬ eq s s'
abbrev compare := Make.compare (X := EOrder)

end RegSet

private abbrev regset := RegSet.t

private def codeList (f : function) : List instruction := f.fn_code

/-! Resource-bound record and generated projections. -/

structure bounds (cfg : CompilerConfig) : Type where
  used_callee_save : List mreg
  bound_local : Z
  bound_outgoing : Z
  bound_stack_data : Z

export bounds (used_callee_save bound_local bound_outgoing bound_stack_data)

def bound_local_pos (cfg : CompilerConfig) (b : bounds cfg) : Prop := zGe b.bound_local z0
def bound_outgoing_pos (cfg : CompilerConfig) (b : bounds cfg) : Prop := zGe b.bound_outgoing z0
def bound_stack_data_pos (cfg : CompilerConfig) (b : bounds cfg) : Prop := zGe b.bound_stack_data z0
def used_callee_save_norepet (cfg : CompilerConfig) (b : bounds cfg) : Prop :=
  list_norepet b.used_callee_save
def used_callee_save_prop (cfg : CompilerConfig) (b : bounds cfg) : Prop :=
  ∀ r, r ∈ b.used_callee_save → is_callee_save cfg r = true

def mreg_within_bounds (cfg : CompilerConfig) (b : bounds cfg) (r : mreg) : Prop :=
  is_callee_save cfg r = true → r ∈ b.used_callee_save

def slot_within_bounds (b : bounds cfg) (sl : slot) (ofs : Z) (ty : typ) : Prop :=
  match sl with
  | .Local => zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) b.bound_local
  | .Outgoing => zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) b.bound_outgoing
  | .Incoming => True

def instr_within_bounds (cfg : CompilerConfig) (b : bounds cfg) (i : instruction) : Prop :=
  match i with
  | Linear.Lgetstack sl ofs ty r =>
      slot_within_bounds b sl ofs ty ∧ mreg_within_bounds cfg b r
  | Linear.Lsetstack _ sl ofs ty => slot_within_bounds b sl ofs ty
  | Linear.Lop _ _ res => mreg_within_bounds cfg b res
  | Linear.Lload _ _ _ dst => mreg_within_bounds cfg b dst
  | Linear.Lcall sig _ => zLe (CompCert4Lean.Backend.Conventions.size_arguments cfg sig) b.bound_outgoing
  | Linear.Lbuiltin ef args res =>
      (∀ r, r ∈ params_of_builtin_res res ∨ r ∈ destroyed_by_builtin ef →
        mreg_within_bounds cfg b r) ∧
      (∀ sl ofs ty, (S sl ofs ty) ∈ params_of_builtin_args args →
        slot_within_bounds b sl ofs ty)
  | _ => True

def function_within_bounds (cfg : CompilerConfig) (f : function) (b : bounds cfg) : Prop :=
  ∀ instr : instruction, List.Mem instr (codeList f) → instr_within_bounds cfg b instr

/-! Resource-bound inference. -/

def record_reg (cfg : CompilerConfig) (u : regset) (r : mreg) : regset :=
  if is_callee_save cfg r then RegSet.add r u else u

def record_regs (cfg : CompilerConfig) (u : regset) (rl : List mreg) : regset :=
  List.foldl (fun acc r => record_reg cfg acc r) u rl

def record_regs_of_instr (cfg : CompilerConfig) (u : regset) (i : instruction) : regset :=
  match i with
  | Linear.Lgetstack _ _ _ r => record_reg cfg u r
  | Linear.Lsetstack r _ _ _ => record_reg cfg u r
  | Linear.Lop _ _ res => record_reg cfg u res
  | Linear.Lload _ _ _ dst => record_reg cfg u dst
  | Linear.Lstore _ _ _ _ => u
  | Linear.Lcall _ _ => u
  | Linear.Ltailcall _ _ => u
  | Linear.Lbuiltin ef _ res =>
      record_regs cfg (record_regs cfg u (params_of_builtin_res res)) (destroyed_by_builtin ef)
  | Linear.Llabel _ => u
  | Linear.Lgoto _ => u
  | Linear.Lcond _ _ _ => u
  | Linear.Ljumptable _ _ => u
  | Linear.Lreturn => u

def record_regs_of_function (cfg : CompilerConfig) (f : function) : regset :=
  List.foldl (fun acc i => record_regs_of_instr cfg acc i) RegSet.empty f.fn_code

def slots_of_locs : List loc → List (slot × Z × typ)
  | [] => []
  | S sl ofs ty :: l' => (sl, ofs, ty) :: slots_of_locs l'
  | R _ :: l' => slots_of_locs l'

def slots_of_instr (i : instruction) : List (slot × Z × typ) :=
  match i with
  | Linear.Lgetstack sl ofs ty _ => [(sl, ofs, ty)]
  | Linear.Lsetstack _ sl ofs ty => [(sl, ofs, ty)]
  | Linear.Lbuiltin _ args _ => slots_of_locs (params_of_builtin_args args)
  | _ => []

def max_over_list {A : Type} (valu : A → Z) (l : List A) : Z :=
  List.foldl (fun m x => zMax m (valu x)) z0 l

def max_over_instrs (f : function) (valu : instruction → Z) : Z :=
  max_over_list valu f.fn_code

def max_over_slots_of_instr (valu : (slot × Z × typ) → Z) (i : instruction) : Z :=
  max_over_list valu (slots_of_instr i)

def max_over_slots_of_funct (f : function) (valu : (slot × Z × typ) → Z) : Z :=
  max_over_instrs f (max_over_slots_of_instr valu)

def local_slot (s : slot × Z × typ) : Z :=
  match s with
  | (.Local, ofs, ty) => zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)
  | _ => z0

def outgoing_slot (s : slot × Z × typ) : Z :=
  match s with
  | (.Outgoing, ofs, ty) => zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)
  | _ => z0

def outgoing_space (cfg : CompilerConfig) (i : instruction) : Z :=
  match i with
  | Linear.Lcall sig _ => CompCert4Lean.Backend.Conventions.size_arguments cfg sig
  | _ => z0

def only_callee_saves (cfg : CompilerConfig) (u : regset) : Prop :=
  ∀ r, RegSet.In r u → is_callee_save cfg r = true

def function_bounds (cfg : CompilerConfig) (f : function) : bounds cfg :=
  { used_callee_save := RegSet.elements (record_regs_of_function cfg f)
    bound_local := max_over_slots_of_funct f local_slot
    bound_outgoing := zMax (max_over_instrs f (outgoing_space cfg))
      (max_over_slots_of_funct f outgoing_slot)
    bound_stack_data := zMax f.fn_stacksize z0 }

def defined_by_instr (r' : mreg) (i : instruction) : Prop :=
  match i with
  | Linear.Lgetstack _ _ _ r => r' = r
  | Linear.Lop _ _ res => r' = res
  | Linear.Lload _ _ _ dst => r' = dst
  | Linear.Lbuiltin ef _ res =>
      r' ∈ params_of_builtin_res res ∨ r' ∈ destroyed_by_builtin ef
  | _ => False

def size_callee_save_area_rec : List mreg → Z → Z
  | [], ofs => ofs
  | r :: l, ofs =>
      let sz := CompCert4Lean.Common.AST.typesize (mreg_type r)
      size_callee_save_area_rec l (zAdd (align ofs sz) sz)

def size_callee_save_area (cfg : CompilerConfig) (b : bounds cfg) (ofs : Z) : Z :=
  size_callee_save_area_rec b.used_callee_save ofs

structure frame_env : Type where
  fe_size : Z
  fe_ofs_link : Z
  fe_ofs_retaddr : Z
  fe_ofs_local : Z
  fe_ofs_callee_save : Z
  fe_stack_data : Z
  fe_used_callee_save : List mreg

export frame_env (fe_size fe_ofs_link fe_ofs_retaddr fe_ofs_local fe_ofs_callee_save
  fe_stack_data fe_used_callee_save)

/-! Statement descriptors for later proof migration. -/

def max_over_list_posStatement : Prop :=
  ∀ (A : Type) (valu : A → Z) (l : List A), zGe (max_over_list valu l) z0
def max_over_slots_of_funct_posStatement : Prop :=
  ∀ (f : function) (valu : (slot × Z × typ) → Z), zGe (max_over_slots_of_funct f valu) z0
def fold_left_preservesStatement : Prop :=
  ∀ (A B : Type) (f : A → B → A) (P : A → Prop),
    (∀ a b, P a → P (f a b)) → ∀ (l : List B) (a : A), P a → P (List.foldl f a l)
def fold_left_ensuresStatement : Prop :=
  ∀ (A B : Type) (f : A → B → A) (P : A → Prop) (b0 : B),
    (∀ a b, P a → P (f a b)) → (∀ a, P (f a b0)) →
    ∀ (l : List B) (a : A), b0 ∈ l → P (List.foldl f a l)
def record_reg_onlyStatement : Prop :=
  ∀ (cfg : CompilerConfig) (u : regset) (r : mreg), only_callee_saves cfg u → only_callee_saves cfg (record_reg cfg u r)
def record_regs_onlyStatement : Prop :=
  ∀ (cfg : CompilerConfig) (rl : List mreg) (u : regset), only_callee_saves cfg u → only_callee_saves cfg (record_regs cfg u rl)
def record_regs_of_instr_onlyStatement : Prop :=
  ∀ (cfg : CompilerConfig) (u : regset) (i : instruction), only_callee_saves cfg u → only_callee_saves cfg (record_regs_of_instr cfg u i)
def record_regs_of_function_onlyStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function), only_callee_saves cfg (record_regs_of_function cfg f)
def record_reg_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (u : regset) (r r' : mreg),
    RegSet.In r' u → RegSet.In r' (record_reg cfg u r)
def record_reg_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (u : regset) (r : mreg),
    is_callee_save cfg r = true → RegSet.In r (record_reg cfg u r)
def record_regs_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r' : mreg) (rl : List mreg) (u : regset),
    RegSet.In r' u → RegSet.In r' (record_regs cfg u rl)
def record_regs_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r : mreg) (rl : List mreg) (u : regset),
    r ∈ rl → is_callee_save cfg r = true → RegSet.In r (record_regs cfg u rl)
def record_regs_of_instr_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r' : mreg) (u : regset) (i : instruction),
    RegSet.In r' u → RegSet.In r' (record_regs_of_instr cfg u i)
def record_regs_of_instr_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r' : mreg) (u : regset) (i : instruction),
    defined_by_instr r' i → is_callee_save cfg r' = true →
      RegSet.In r' (record_regs_of_instr cfg u i)
def record_regs_of_function_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (r : mreg) (i : instruction),
    List.Mem i (codeList f) → defined_by_instr r i →
      is_callee_save cfg r = true → RegSet.In r (record_regs_of_function cfg f)
def max_over_list_boundStatement : Prop :=
  ∀ (A : Type) (valu : A → Z) (l : List A) (x : A), x ∈ l → zLe (valu x) (max_over_list valu l)
def max_over_instrs_boundStatement : Prop :=
  ∀ (f : function) (valu : instruction → Z) (i : instruction), List.Mem i (codeList f) → zLe (valu i) (max_over_instrs f valu)
def max_over_slots_of_funct_boundStatement : Prop :=
  ∀ (f : function) (valu : (slot × Z × typ) → Z) (i : instruction) (s : slot × Z × typ), List.Mem i (codeList f) → s ∈ slots_of_instr i → zLe (valu s) (max_over_slots_of_funct f valu)
def local_slot_boundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (i : instruction) (ofs : Z) (ty : typ), List.Mem i (codeList f) → (Local, ofs, ty) ∈ slots_of_instr i → zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) (bound_local (function_bounds cfg f))
def outgoing_slot_boundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (i : instruction) (ofs : Z) (ty : typ), List.Mem i (codeList f) → (Outgoing, ofs, ty) ∈ slots_of_instr i → zLe (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty)) (bound_outgoing (function_bounds cfg f))
def size_arguments_boundStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (sig : signature) (ros : Sum mreg ident), List.Mem (Linear.Lcall sig ros) (codeList f) → zLe (CompCert4Lean.Backend.Conventions.size_arguments cfg sig) (bound_outgoing (function_bounds cfg f))
def mreg_is_within_boundsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (i : instruction), List.Mem i (codeList f) → ∀ r, defined_by_instr r i → mreg_within_bounds cfg (function_bounds cfg f) r
def slot_is_within_boundsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (i : instruction), List.Mem i (codeList f) → ∀ sl ty ofs, (sl, ofs, ty) ∈ slots_of_instr i → slot_within_bounds (function_bounds cfg f) sl ofs ty
def slots_of_locs_charactStatement : Prop :=
  ∀ (sl : slot) (ofs : Z) (ty : typ) (l : List loc), (sl, ofs, ty) ∈ slots_of_locs l ↔ (S sl ofs ty) ∈ l
def instr_is_within_boundsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (i : instruction), List.Mem i (codeList f) → instr_within_bounds cfg (function_bounds cfg f) i
def function_is_within_boundsStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function), function_within_bounds cfg f (function_bounds cfg f)
def size_callee_save_area_rec_incrStatement : Prop :=
  ∀ (l : List mreg) (ofs : Z), zLe ofs (size_callee_save_area_rec l ofs)
def size_callee_save_area_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (b : bounds cfg) (ofs : Z), zLe ofs (size_callee_save_area cfg b ofs)

end CompCert4Lean.Backend.Bounds

namespace CompCert4Lean.Backend.Bounds

theorem fold_left_preserves : fold_left_preservesStatement := by
  intro A B f P h l a ha
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
      simp only [List.foldl]
      apply ih
      exact h a b ha

end CompCert4Lean.Backend.Bounds

namespace CompCert4Lean.Backend.Bounds

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace RegSet

theorem add_1_proof : add_1 := by
  intro s x y hxy
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_1 s x y hxy

theorem add_2_proof : add_2 := by
  intro s x y hy
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_2 s x y hy

end RegSet

private theorem zLe_refl (x : Z) : zLe x x := by
  change intOfZ x ≤ intOfZ x
  exact Int.le_refl _

private theorem zLe_trans (x y z : Z) : zLe x y → zLe y z → zLe x z := by
  intro hxy hyz
  change intOfZ x ≤ intOfZ y at hxy
  change intOfZ y ≤ intOfZ z at hyz
  change intOfZ x ≤ intOfZ z
  exact Int.le_trans hxy hyz

private theorem zLe_max_left (x y : Z) : zLe x (zMax x y) := by
  change intOfZ x ≤ intOfZ (zMax x y)
  unfold zMax ZArith.BinInt.Z.max
  by_cases h : intOfZ x ≤ intOfZ y
  · simp [h]
  · simp [h]

private theorem zLe_max_right (x y : Z) : zLe y (zMax x y) := by
  change intOfZ y ≤ intOfZ (zMax x y)
  unfold zMax ZArith.BinInt.Z.max
  by_cases h : intOfZ x ≤ intOfZ y
  · simp [h]
  · have hyx : intOfZ y ≤ intOfZ x := by omega
    simp [h, hyx]

private theorem max_over_list_aux {A : Type} (valu : A → Z) (x : A) :
    ∀ (l : List A) (z : Z),
      zLe z (List.foldl (fun m y => zMax m (valu y)) z l) ∧
        (x ∈ l → zLe (valu x)
          (List.foldl (fun m y => zMax m (valu y)) z l)) := by
  intro l
  induction l with
  | nil =>
      intro z
      constructor
      · exact zLe_refl z
      · intro hx
        exact (_root_.List.not_mem_nil hx).elim
  | cons a l ih =>
      intro z
      simp only [List.foldl]
      have hi := ih (zMax z (valu a))
      constructor
      · exact zLe_trans z (zMax z (valu a)) _ (zLe_max_left z (valu a)) hi.1
      · intro hx
        rcases (_root_.List.mem_cons.mp hx) with hxa | hxl
        · subst a
          exact zLe_trans (valu x) (zMax z (valu x)) _
            (zLe_max_right z (valu x)) hi.1
        · exact hi.2 hxl

theorem max_over_list_bound : max_over_list_boundStatement := by
  intro A valu l x hx
  have h := max_over_list_aux valu x l z0
  exact h.2 hx

theorem fold_left_ensures : fold_left_ensuresStatement := by
  intro A B f P b0 hpres hbase l a hmem
  induction l generalizing a with
  | nil =>
      exact (_root_.List.not_mem_nil hmem).elim
  | cons b l ih =>
      simp only [List.foldl]
      rcases (_root_.List.mem_cons.mp hmem) with hhead | htail
      · subst b
        have hp : ∀ (ll : List B) (aa : A), P aa → P (List.foldl f aa ll) := by
          intro ll
          induction ll with
          | nil =>
              intro aa haa
              exact haa
          | cons bb ll ih =>
              intro aa haa
              apply ih
              exact hpres aa bb haa
        exact hp l (f a b0) (hbase a)
      · exact ih (f a b) htail

end CompCert4Lean.Backend.Bounds

namespace CompCert4Lean.Backend.Bounds

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

namespace RegSet

theorem add_3_proof : add_3 := by
  intro s x y hne hy
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_3 s x y hne hy

end RegSet

theorem record_reg_incr : record_reg_incrStatement := by
  intro cfg u r r' hr'
  unfold record_reg
  split
  · exact RegSet.add_2_proof u r r' hr'
  · exact hr'

theorem record_reg_ok : record_reg_okStatement := by
  intro cfg u r hr
  unfold record_reg
  rw [hr]
  exact RegSet.add_1_proof u r r rfl

theorem max_over_instrs_bound : max_over_instrs_boundStatement := by
  intro f valu i hi
  exact max_over_list_bound instruction valu (codeList f) i hi

end CompCert4Lean.Backend.Bounds

namespace CompCert4Lean.Backend.Bounds

open CompCert4Lean.Foundation.Numbers.Rocq.Coq

theorem record_reg_only : record_reg_onlyStatement := by
  intro cfg u r hu
  unfold only_callee_saves at hu ⊢
  intro r' hr'
  unfold record_reg at hr'
  split at hr'
  · by_cases hEq : r' = r
    · subst r'
      assumption
    · apply hu r'
      apply RegSet.add_3_proof u r r'
      · intro h
        exact hEq h.symm
      · exact hr'
  · exact hu r' hr'

theorem record_regs_incr : record_regs_incrStatement := by
  intro cfg r' rl u hr'
  unfold record_regs
  apply fold_left_preserves
  · intro acc r hacc
    exact record_reg_incr cfg acc r r' hacc
  · exact hr'

theorem record_regs_ok : record_regs_okStatement := by
  intro cfg r rl u hmem hsave
  unfold record_regs
  apply fold_left_ensures
    (A := regset)
    (f := fun acc r' => record_reg cfg acc r')
    (P := fun acc => RegSet.In r acc) (b0 := r)
  · intro acc r' hacc
    exact record_reg_incr cfg acc r' r hacc
  · intro acc
    exact record_reg_ok cfg acc r hsave
  · exact hmem

theorem max_over_slots_of_funct_bound : max_over_slots_of_funct_boundStatement := by
  intro f valu i s hi hs
  unfold max_over_slots_of_funct
  apply zLe_trans (valu s) (max_over_slots_of_instr valu i) _
  · unfold max_over_slots_of_instr
    exact max_over_list_bound _ valu (slots_of_instr i) s hs
  · exact max_over_instrs_bound f (max_over_slots_of_instr valu) i hi

end CompCert4Lean.Backend.Bounds
