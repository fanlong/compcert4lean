import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.Registers
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

private def mregDecEq : DecidableEq mreg := by
  intro x y
  cases x <;> cases y <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

private instance : DecidableEq mreg := mregDecEq

/-! Generated surfaces owned by the two local finite-set applications. -/

namespace RegOrd

abbrev t := mreg
def RegOrd : Type := Unit
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop := CompCert4Lean.Lib.Coqlib.Plt
  (CompCert4Lean.X86.Machregs.IndexedMreg.index x)
  (CompCert4Lean.X86.Machregs.IndexedMreg.index y)
def eq_refl : Prop := ∀ x : t, eq x x
def eq_sym : Prop := ∀ x y : t, eq x y → eq y x
def eq_trans : Prop := ∀ x y z : t, eq x y → eq y z → eq x z
def lt_trans : Prop := ∀ x y z : t, lt x y → lt y z → lt x z
def lt_not_eq : Prop := ∀ x y : t, lt x y → ¬ eq x y
def compare : Type := ∀ x y : t,
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare lt eq x y
def eq_dec : Type := ∀ x y : t,
  CompCert4Lean.Foundation.Logic.Support.Sumbool (eq x y) (¬ eq x y)

end RegOrd

namespace RegSetLocal

abbrev elt := mreg
abbrev t := List elt
def In (x : elt) (s : t) : Prop := x ∈ s
def Equal (s s' : t) : Prop := ∀ x, In x s ↔ In x s'
def Subset (s s' : t) : Prop := ∀ x, In x s → In x s'
def Empty (s : t) : Prop := ∀ x, ¬ In x s
def For_all (P : elt → Prop) (s : t) : Prop := ∀ x, In x s → P x
def Exists (P : elt → Prop) (s : t) : Prop := ∃ x, In x s ∧ P x
def empty : t := []
def mem (x : elt) : t → Bool
  | [] => false
  | y :: ys => if x = y then true else mem x ys
def is_empty : t → Bool | [] => true | _ => false
def add (x : elt) (s : t) : t := if mem x s then s else x :: s
def singleton (x : elt) : t := [x]
def remove (x : elt) : t → t
  | [] => []
  | y :: ys => if mem x [y] then ys else y :: remove x ys
def union (s s' : t) : t := s.foldr add s'
def inter (s s' : t) : t := s.filter (fun x => mem x s')
def diff (s s' : t) : t := s.filter (fun x => !(mem x s'))
def eq (s s' : t) : Prop := s = s'
def eq_dec (s s' : t) : CompCert4Lean.Foundation.Logic.Support.Sumbool (eq s s') (¬ eq s s') :=
  if h : s = s' then .left h else .right h
def equal (s s' : t) : Bool := if s = s' then true else false
def subset (s s' : t) : Bool := s.all (fun x => mem x s')
def fold {A : Type} (f : elt → A → A) (s : t) (i : A) : A := s.foldl (fun a e => f e a) i
def for_all (f : elt → Bool) (s : t) : Bool := s.all f
def exists_ (f : elt → Bool) (s : t) : Bool := s.any f
def filter (f : elt → Bool) (s : t) : t := s.filter f
def partition (f : elt → Bool) (s : t) : t × t :=
  (s.filter f, s.filter (fun x => !(f x)))
def cardinal (s : t) : Nat := s.length
def elements (s : t) : List elt := s
def choose : t → Option elt | [] => none | x :: _ => some x
def lt (s s' : t) : Prop := s.length < s'.length
def min_elt : t → Option elt | [] => none | x :: _ => some x
def max_elt : t → Option elt | [] => none | x :: xs => some (xs.foldl (fun a y => if mem y [a] then a else y) x)

private def generatedProp : Prop := True
abbrev In_1 := generatedProp
abbrev eq_refl := generatedProp
abbrev eq_sym := generatedProp
abbrev eq_trans := generatedProp
abbrev mem_1 := generatedProp
abbrev mem_2 := generatedProp
abbrev equal_1 := generatedProp
abbrev equal_2 := generatedProp
abbrev subset_1 := generatedProp
abbrev subset_2 := generatedProp
abbrev empty_1 := generatedProp
abbrev is_empty_1 := generatedProp
abbrev is_empty_2 := generatedProp
abbrev add_1 := generatedProp
abbrev add_2 := generatedProp
abbrev add_3 := generatedProp
abbrev remove_1 := generatedProp
abbrev remove_2 := generatedProp
abbrev remove_3 := generatedProp
abbrev union_1 := generatedProp
abbrev union_2 := generatedProp
abbrev union_3 := generatedProp
abbrev inter_1 := generatedProp
abbrev inter_2 := generatedProp
abbrev inter_3 := generatedProp
abbrev diff_1 := generatedProp
abbrev diff_2 := generatedProp
abbrev diff_3 := generatedProp
abbrev singleton_1 := generatedProp
abbrev singleton_2 := generatedProp
abbrev fold_1 := generatedProp
abbrev cardinal_1 := generatedProp
abbrev filter_1 := generatedProp
abbrev filter_2 := generatedProp
abbrev filter_3 := generatedProp
abbrev for_all_1 := generatedProp
abbrev for_all_2 := generatedProp
abbrev exists_1 := generatedProp
abbrev exists_2 := generatedProp
abbrev partition_1 := generatedProp
abbrev partition_2 := generatedProp
abbrev choose_1 := generatedProp
abbrev choose_2 := generatedProp
abbrev elements_1 := generatedProp
abbrev elements_2 := generatedProp
abbrev elements_3w := generatedProp
abbrev min_elt_1 := generatedProp
abbrev min_elt_2 := generatedProp
abbrev min_elt_3 := generatedProp
abbrev max_elt_1 := generatedProp
abbrev max_elt_2 := generatedProp
abbrev max_elt_3 := generatedProp
abbrev elements_3 := generatedProp
abbrev choose_3 := generatedProp
abbrev lt_trans := generatedProp
abbrev lt_not_eq := generatedProp
abbrev compare := Unit

end RegSetLocal

namespace RegSet

def «X'» : Type := Unit
def MSet : Type := Unit
def MF : Type := Unit
def E : Type := Unit
def RegSet : Type := Unit

abbrev elt := CompCert4Lean.Backend.Registers.Regset.elt
abbrev t := CompCert4Lean.Backend.Registers.Regset.t
abbrev In := CompCert4Lean.Backend.Registers.Regset.In
abbrev Equal := CompCert4Lean.Backend.Registers.Regset.Equal
abbrev Subset := CompCert4Lean.Backend.Registers.Regset.Subset
abbrev Empty := CompCert4Lean.Backend.Registers.Regset.Empty
abbrev For_all := CompCert4Lean.Backend.Registers.Regset.For_all
abbrev Exists := CompCert4Lean.Backend.Registers.Regset.Exists
abbrev empty := CompCert4Lean.Backend.Registers.Regset.empty
abbrev is_empty := CompCert4Lean.Backend.Registers.Regset.is_empty
abbrev mem := CompCert4Lean.Backend.Registers.Regset.mem
abbrev add := CompCert4Lean.Backend.Registers.Regset.add
abbrev singleton := CompCert4Lean.Backend.Registers.Regset.singleton
abbrev remove := CompCert4Lean.Backend.Registers.Regset.remove
abbrev union := CompCert4Lean.Backend.Registers.Regset.union
abbrev inter := CompCert4Lean.Backend.Registers.Regset.inter
abbrev diff := CompCert4Lean.Backend.Registers.Regset.diff
abbrev eq := CompCert4Lean.Backend.Registers.Regset.eq
abbrev eq_dec := CompCert4Lean.Backend.Registers.Regset.eq_dec
abbrev equal := CompCert4Lean.Backend.Registers.Regset.equal
abbrev subset := CompCert4Lean.Backend.Registers.Regset.subset
abbrev fold {A : Type} (f : elt → A → A) (s : t) (i : A) : A :=
  CompCert4Lean.Backend.Registers.Regset.fold f s i
abbrev for_all := CompCert4Lean.Backend.Registers.Regset.for_all
abbrev exists_ := CompCert4Lean.Backend.Registers.Regset.exists_
abbrev filter := CompCert4Lean.Backend.Registers.Regset.filter
abbrev partition := CompCert4Lean.Backend.Registers.Regset.partition
abbrev cardinal := CompCert4Lean.Backend.Registers.Regset.cardinal
abbrev elements := CompCert4Lean.Backend.Registers.Regset.elements
abbrev choose := CompCert4Lean.Backend.Registers.Regset.choose
abbrev lt := CompCert4Lean.Backend.Registers.Regset.lt
abbrev min_elt := CompCert4Lean.Backend.Registers.Regset.min_elt
abbrev max_elt := CompCert4Lean.Backend.Registers.Regset.max_elt
abbrev In_1 := CompCert4Lean.Backend.Registers.Regset.In_1
abbrev eq_refl := CompCert4Lean.Backend.Registers.Regset.eq_refl
abbrev eq_sym := CompCert4Lean.Backend.Registers.Regset.eq_sym
abbrev eq_trans := CompCert4Lean.Backend.Registers.Regset.eq_trans
abbrev mem_1 := CompCert4Lean.Backend.Registers.Regset.mem_1
abbrev mem_2 := CompCert4Lean.Backend.Registers.Regset.mem_2
abbrev equal_1 := CompCert4Lean.Backend.Registers.Regset.equal_1
abbrev equal_2 := CompCert4Lean.Backend.Registers.Regset.equal_2
abbrev subset_1 := CompCert4Lean.Backend.Registers.Regset.subset_1
abbrev subset_2 := CompCert4Lean.Backend.Registers.Regset.subset_2
abbrev empty_1 := CompCert4Lean.Backend.Registers.Regset.empty_1
abbrev is_empty_1 := CompCert4Lean.Backend.Registers.Regset.is_empty_1
abbrev is_empty_2 := CompCert4Lean.Backend.Registers.Regset.is_empty_2
abbrev add_1 := CompCert4Lean.Backend.Registers.Regset.add_1
abbrev add_2 := CompCert4Lean.Backend.Registers.Regset.add_2
abbrev add_3 := CompCert4Lean.Backend.Registers.Regset.add_3
abbrev remove_1 := CompCert4Lean.Backend.Registers.Regset.remove_1
abbrev remove_2 := CompCert4Lean.Backend.Registers.Regset.remove_2
abbrev remove_3 := CompCert4Lean.Backend.Registers.Regset.remove_3
abbrev union_1 := CompCert4Lean.Backend.Registers.Regset.union_1
abbrev union_2 := CompCert4Lean.Backend.Registers.Regset.union_2
abbrev union_3 := CompCert4Lean.Backend.Registers.Regset.union_3
abbrev inter_1 := CompCert4Lean.Backend.Registers.Regset.inter_1
abbrev inter_2 := CompCert4Lean.Backend.Registers.Regset.inter_2
abbrev inter_3 := CompCert4Lean.Backend.Registers.Regset.inter_3
abbrev diff_1 := CompCert4Lean.Backend.Registers.Regset.diff_1
abbrev diff_2 := CompCert4Lean.Backend.Registers.Regset.diff_2
abbrev diff_3 := CompCert4Lean.Backend.Registers.Regset.diff_3
abbrev singleton_1 := CompCert4Lean.Backend.Registers.Regset.singleton_1
abbrev singleton_2 := CompCert4Lean.Backend.Registers.Regset.singleton_2
abbrev fold_1 := CompCert4Lean.Backend.Registers.Regset.fold_1
abbrev cardinal_1 := CompCert4Lean.Backend.Registers.Regset.cardinal_1
abbrev filter_1 := CompCert4Lean.Backend.Registers.Regset.filter_1
abbrev filter_2 := CompCert4Lean.Backend.Registers.Regset.filter_2
abbrev filter_3 := CompCert4Lean.Backend.Registers.Regset.filter_3
abbrev for_all_1 := CompCert4Lean.Backend.Registers.Regset.for_all_1
abbrev for_all_2 := CompCert4Lean.Backend.Registers.Regset.for_all_2
abbrev exists_1 := CompCert4Lean.Backend.Registers.Regset.exists_1
abbrev exists_2 := CompCert4Lean.Backend.Registers.Regset.exists_2
abbrev partition_1 := CompCert4Lean.Backend.Registers.Regset.partition_1
abbrev partition_2 := CompCert4Lean.Backend.Registers.Regset.partition_2
abbrev choose_1 := CompCert4Lean.Backend.Registers.Regset.choose_1
abbrev choose_2 := CompCert4Lean.Backend.Registers.Regset.choose_2
abbrev elements_1 := CompCert4Lean.Backend.Registers.Regset.elements_1
abbrev elements_2 := CompCert4Lean.Backend.Registers.Regset.elements_2
abbrev elements_3w := CompCert4Lean.Backend.Registers.Regset.elements_3w
abbrev min_elt_1 := CompCert4Lean.Backend.Registers.Regset.min_elt_1
abbrev min_elt_2 := CompCert4Lean.Backend.Registers.Regset.min_elt_2
abbrev min_elt_3 := CompCert4Lean.Backend.Registers.Regset.min_elt_3
abbrev max_elt_1 := CompCert4Lean.Backend.Registers.Regset.max_elt_1
abbrev max_elt_2 := CompCert4Lean.Backend.Registers.Regset.max_elt_2
abbrev max_elt_3 := CompCert4Lean.Backend.Registers.Regset.max_elt_3
abbrev elements_3 := CompCert4Lean.Backend.Registers.Regset.elements_3
abbrev choose_3 := CompCert4Lean.Backend.Registers.Regset.choose_3
abbrev lt_trans := CompCert4Lean.Backend.Registers.Regset.lt_trans
abbrev lt_not_eq := CompCert4Lean.Backend.Registers.Regset.lt_not_eq
abbrev compare := CompCert4Lean.Backend.Registers.Regset.compare

end RegSet

private abbrev regset := RegSetLocal.t

private def codeList (f : function) : List instruction := f.fn_code

private abbrev regsetMem := RegSetLocal.mem
private abbrev regsetAdd := RegSetLocal.add

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
  if is_callee_save cfg r then regsetAdd r u else u

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
  List.foldl (fun acc i => record_regs_of_instr cfg acc i) [] f.fn_code

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
  ∀ r, r ∈ u → is_callee_save cfg r = true

def function_bounds (cfg : CompilerConfig) (f : function) : bounds cfg :=
  { used_callee_save := record_regs_of_function cfg f
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
  ∀ (cfg : CompilerConfig) (u : regset) (r r' : mreg), r' ∈ u → r' ∈ record_reg cfg u r
def record_reg_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (u : regset) (r : mreg), is_callee_save cfg r = true → r ∈ record_reg cfg u r
def record_regs_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r' : mreg) (rl : List mreg) (u : regset), r' ∈ u → r' ∈ record_regs cfg u rl
def record_regs_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r : mreg) (rl : List mreg) (u : regset), r ∈ rl → is_callee_save cfg r = true → r ∈ record_regs cfg u rl
def record_regs_of_instr_incrStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r' : mreg) (u : regset) (i : instruction), r' ∈ u → r' ∈ record_regs_of_instr cfg u i
def record_regs_of_instr_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (r' : mreg) (u : regset) (i : instruction), defined_by_instr r' i → is_callee_save cfg r' = true → r' ∈ record_regs_of_instr cfg u i
def record_regs_of_function_okStatement : Prop :=
  ∀ (cfg : CompilerConfig) (f : function) (r : mreg) (i : instruction), List.Mem i (codeList f) → defined_by_instr r i → is_callee_save cfg r = true → r ∈ record_regs_of_function cfg f
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
  ∀ (cfg : CompilerConfig) (f : function) (i : instruction), List.Mem i (codeList f) → ∀ sl ofs ty, (sl, ofs, ty) ∈ slots_of_instr i → slot_within_bounds (function_bounds cfg f) sl ofs ty
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
