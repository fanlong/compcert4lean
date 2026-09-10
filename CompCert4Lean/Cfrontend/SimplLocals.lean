import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Foundation.RocqString
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.Linking
import CompCert4Lean.Cfrontend.Clight
import CompCert4Lean.Cfrontend.Cop
import CompCert4Lean.Cfrontend.Ctypes
import CompCert4Lean.Driver.Compopts
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.FSetAVLplus
import CompCert4Lean.Lib.Ordered
import CompCert4Lean.X86.Conventions1

/-!
# Pulling local scalar variables into temporaries

Definition-bearing translation of CompCert's `cfrontend/SimplLocals.v`.
The source's generated `FSetAVL.Make(OrderedPositive)` application is exposed
as the local `VSet` namespace.  Proof-bearing members of that generated
surface are retained as exact proposition or type descriptors for the later
proof-migration phase.
-/

namespace CompCert4Lean.Cfrontend.SimplLocals

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Cfrontend.Clight
open CompCert4Lean.Cfrontend.Cop
open CompCert4Lean.Cfrontend.Ctypes
open CompCert4Lean.Lib.Coqlib

private abbrev ident := CompCert4Lean.Common.AST.ident
private abbrev type := CompCert4Lean.Cfrontend.Ctypes.type
private abbrev expr := CompCert4Lean.Cfrontend.Clight.expr
private abbrev statement := CompCert4Lean.Cfrontend.Clight.statement
private abbrev labeled_statements :=
  CompCert4Lean.Cfrontend.Clight.labeled_statements
private abbrev function := CompCert4Lean.Cfrontend.Clight.function
private abbrev fundef := CompCert4Lean.Cfrontend.Clight.fundef
private abbrev program := CompCert4Lean.Cfrontend.Clight.program
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/-! ## Generated ordered finite-set surface -/

namespace VSet

def VSet : Type := Unit

open CompCert4Lean.Lib.FSetAVLplus
open CompCert4Lean.Lib.Ordered

private abbrev OrderedType :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType
private abbrev Compare {X : Type} (lt eq : X → X → Prop) (x y : X) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
    lt eq x y

def EOrder : OrderedType where
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
  compare := OrderedPositive.compare
  eq_dec := CompCert4Lean.Lib.Coqlib.peq

abbrev E : Type := EOrder.t
abbrev «X'» : Type := E

namespace X'

abbrev orderedType : OrderedType := EOrder
abbrev t : Type := E
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

namespace E

abbrev orderedType : OrderedType := EOrder
abbrev t : Type := E
abbrev eq : t → t → Prop := EOrder.eq
abbrev lt : t → t → Prop := EOrder.lt
abbrev compare := EOrder.compare
abbrev eq_dec := EOrder.eq_dec

end E

abbrev elt : Type := Make.elt EOrder
abbrev t : Type := Make.t EOrder

def In : elt → t → Prop := Make.In (X := EOrder)
def Equal : t → t → Prop := Make.Equal (X := EOrder)
def Subset : t → t → Prop := Make.Subset (X := EOrder)
def Empty : t → Prop := Make.Empty (X := EOrder)
def For_all : (elt → Prop) → t → Prop := Make.For_all (X := EOrder)
def Exists : (elt → Prop) → t → Prop := Make.Exists (X := EOrder)

def empty : t := Make.empty (X := EOrder)
def is_empty : t → Bool := Make.is_empty (X := EOrder)
def mem : elt → t → Bool := Make.mem (X := EOrder)
def add : elt → t → t := Make.add (X := EOrder)
def singleton : elt → t := Make.singleton (X := EOrder)
def remove : elt → t → t := Make.remove (X := EOrder)
def union : t → t → t := Make.union (X := EOrder)
def inter : t → t → t := Make.inter (X := EOrder)
def diff : t → t → t := Make.diff (X := EOrder)
def eq : t → t → Prop := Make.eq (X := EOrder)
def eq_dec (s s' : t) : Sumbool (eq s s') (¬ eq s s') :=
  Make.eq_dec s s'
def equal : t → t → Bool := Make.equal (X := EOrder)
def subset : t → t → Bool := Make.subset (X := EOrder)
def fold {A : Type} (f : elt → A → A) (s : t) (initial : A) : A :=
  Make.fold (X := EOrder) f s initial
def for_all : (elt → Bool) → t → Bool := Make.for_all (X := EOrder)
def exists_ : (elt → Bool) → t → Bool := Make.exists_ (X := EOrder)
def filter : (elt → Bool) → t → t := Make.filter (X := EOrder)
def partition : (elt → Bool) → t → t × t := Make.partition (X := EOrder)
def cardinal : t → Nat := Make.cardinal (X := EOrder)
def elements : t → List elt := Make.elements (X := EOrder)
def choose : t → Option elt := Make.choose (X := EOrder)
def lt : t → t → Prop := Make.lt (X := EOrder)
def min_elt : t → Option elt := Make.min_elt (X := EOrder)
def max_elt : t → Option elt := Make.max_elt (X := EOrder)

private abbrev CompatBool (R : elt → elt → Prop) (f : elt → Bool) : Prop :=
  CompCert4Lean.Lib.FSetInterface.compat_bool R f
private abbrev NoDupA (R : elt → elt → Prop) (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.NoDupA R l
private abbrev Sorted (R : elt → elt → Prop) (l : List elt) : Prop :=
  CompCert4Lean.Lib.FSetInterface.sort R l

def In_1 : Prop :=
  ∀ (s : t) (x y : elt), x = y → In x s → In y s

def eq_refl : Prop :=
  ∀ s : t, eq s s

def eq_sym : Prop :=
  ∀ s s' : t, eq s s' → eq s' s

def eq_trans : Prop :=
  ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''

def mem_1 : Prop :=
  ∀ (s : t) (x : elt), In x s → mem x s = true

def mem_2 : Prop :=
  ∀ (s : t) (x : elt), mem x s = true → In x s

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
  ∀ (s : t) (x y : elt), x = y → In y (add x s)

def add_2 : Prop :=
  ∀ (s : t) (x y : elt), In y s → In y (add x s)

def add_3 : Prop :=
  ∀ (s : t) (x y : elt), x ≠ y → In y (add x s) → In y s

def remove_1 : Prop :=
  ∀ (s : t) (x y : elt), x = y → ¬ In y (remove x s)

def remove_2 : Prop :=
  ∀ (s : t) (x y : elt), x ≠ y → In y s → In y (remove x s)

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
  ∀ x y : elt, In y (singleton x) → x = y

def singleton_2 : Prop :=
  ∀ x y : elt, x = y → In y (singleton x)

def fold_1 : Prop :=
  ∀ (s : t) (A : Type) (i : A) (f : elt → A → A),
    fold f s i = List.foldl (fun a e => f e a) i (elements s)

def cardinal_1 : Prop :=
  ∀ s : t, cardinal s = (elements s).length

def filter_1 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → In x (filter f s) → In x s

def filter_2 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → In x (filter f s) → f x = true

def filter_3 : Prop :=
  ∀ (s : t) (x : elt) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → In x s → f x = true →
      In x (filter f s)

def for_all_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool (fun x y => x = y) f →
      For_all (fun x => f x = true) s → for_all f s = true

def for_all_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → for_all f s = true →
      For_all (fun x => f x = true) s

def exists_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool (fun x y => x = y) f →
      Exists (fun x => f x = true) s → exists_ f s = true

def exists_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool (fun x y => x = y) f → exists_ f s = true →
      Exists (fun x => f x = true) s

def partition_1 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool (fun x y => x = y) f →
      Equal (partition f s).1 (filter f s)

def partition_2 : Prop :=
  ∀ (s : t) (f : elt → Bool),
    CompatBool (fun x y => x = y) f →
      Equal (partition f s).2 (filter (fun x => !(f x)) s)

def choose_1 : Prop :=
  ∀ (s : t) (x : elt), choose s = some x → In x s

def choose_2 : Prop :=
  ∀ s : t, choose s = none → Empty s

def elements_1 : Prop :=
  ∀ (s : t) (x : elt), In x s →
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
      (fun x y : elt => x = y) x (elements s)

def elements_2 : Prop :=
  ∀ (s : t) (x : elt),
    CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.SetoidList.InA
      (fun x y : elt => x = y) x (elements s) → In x s

def elements_3w : Prop :=
  ∀ s : t, NoDupA (fun x y : elt => x = y) (elements s)

def min_elt_1 : Prop :=
  ∀ (s : t) (x : elt), min_elt s = some x → In x s

def min_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), min_elt s = some x → In y s →
    ¬ CompCert4Lean.Lib.Coqlib.Plt y x

def min_elt_3 : Prop :=
  ∀ s : t, min_elt s = none → Empty s

def max_elt_1 : Prop :=
  ∀ (s : t) (x : elt), max_elt s = some x → In x s

def max_elt_2 : Prop :=
  ∀ (s : t) (x y : elt), max_elt s = some x → In y s →
    ¬ CompCert4Lean.Lib.Coqlib.Plt x y

def max_elt_3 : Prop :=
  ∀ s : t, max_elt s = none → Empty s

def elements_3 : Prop :=
  ∀ s : t, Sorted CompCert4Lean.Lib.Coqlib.Plt (elements s)

def choose_3 : Prop :=
  ∀ (s s' : t) (x y : elt),
    choose s = some x → choose s' = some y → Equal s s' → x = y

def lt_trans : Prop :=
  ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''

def lt_not_eq : Prop :=
  ∀ s s' : t, lt s s' → ¬ eq s s'

def compare : Type :=
  ∀ s s' : t,
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq s s'

end VSet

/-! ## Liftable-variable environments and smart casts -/

def compilenv : Type := VSet.t

def is_liftable_var (cenv : compilenv) (a : expr) : Option ident :=
  match a with
  | .Evar id _ => if VSet.mem id cenv then some id else none
  | _ => none

def make_cast (a : expr) (tto : type) : expr :=
  match classify_cast (typeof a) tto with
  | .cast_case_pointer => a
  | .cast_case_i2i .I32 _ => a
  | .cast_case_f2f => a
  | .cast_case_s2s => a
  | .cast_case_l2l => a
  | .cast_case_struct _ _ => a
  | .cast_case_union _ _ => a
  | .cast_case_void => a
  | _ => .Ecast a tto

/-! ## Debug annotations -/

private abbrev debugTempKind : positive := .xO .xH
private abbrev debugVarKind : positive := .xI (.xO .xH)

def Sdebug_temp (id : ident) (ty : type) : statement :=
  .Sbuiltin none (.EF_debug debugTempKind id [typ_of_type ty])
    [typeconv ty] [.Etempvar id ty]

def Sdebug_var (id : ident) (ty : type) : statement :=
  let pointerType := Tpointer ty noattr
  .Sbuiltin none (.EF_debug debugVarKind id [CompCert4Lean.Common.AST.Tptr])
    [pointerType] [.Eaddrof (.Evar id ty) pointerType]

def Sset_debug (cfg : CompilerConfig) (id : ident) (ty : type)
    (a : expr) : statement :=
  if CompCert4Lean.Driver.Compopts.debug cfg then
    .Ssequence (.Sset id (make_cast a ty)) (Sdebug_temp id ty)
  else
    .Sset id (make_cast a ty)

/-! ## Rewriting expressions and statements -/

def simpl_expr (cenv : compilenv) : expr → expr
  | a@(.Econst_int _ _) => a
  | a@(.Econst_float _ _) => a
  | a@(.Econst_single _ _) => a
  | a@(.Econst_long _ _) => a
  | .Evar id ty => if VSet.mem id cenv then .Etempvar id ty else .Evar id ty
  | .Etempvar id ty => .Etempvar id ty
  | .Ederef a ty => .Ederef (simpl_expr cenv a) ty
  | .Eaddrof a ty => .Eaddrof (simpl_expr cenv a) ty
  | .Eunop op a ty => .Eunop op (simpl_expr cenv a) ty
  | .Ebinop op a₁ a₂ ty =>
      .Ebinop op (simpl_expr cenv a₁) (simpl_expr cenv a₂) ty
  | .Ecast a ty => .Ecast (simpl_expr cenv a) ty
  | .Efield a field ty => .Efield (simpl_expr cenv a) field ty
  | a@(.Esizeof _ _) => a
  | a@(.Ealignof _ _) => a

def simpl_exprlist (cenv : compilenv) (expressions : List expr) : List expr :=
  expressions.map (simpl_expr cenv)

private def badTemporaryText :
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string :=
  [98, 97, 100, 32, 116, 101, 109, 112, 111, 114, 97, 114, 121, 32].foldr
    (fun byte tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String byte tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

def check_temp (cenv : compilenv) (id : ident) : Res Unit :=
  if VSet.mem id cenv then
    .Error [.MSG badTemporaryText, .CTX id]
  else
    .OK ()

def check_opttemp (cenv : compilenv) (id : Option ident) : Res Unit :=
  match id with
  | some id => check_temp cenv id
  | none => .OK ()

mutual
  def simpl_stmt (cfg : CompilerConfig) (cenv : compilenv) : statement → Res statement
    | .Sskip => .OK .Sskip
    | .Sassign a₁ a₂ =>
        match is_liftable_var cenv a₁ with
        | some id => .OK (Sset_debug cfg id (typeof a₁) (simpl_expr cenv a₂))
        | none => .OK (.Sassign (simpl_expr cenv a₁) (simpl_expr cenv a₂))
    | .Sset id a =>
        match check_temp cenv id with
        | .Error message => .Error message
        | .OK _ => .OK (.Sset id (simpl_expr cenv a))
    | .Scall result fn args =>
        match check_opttemp cenv result with
        | .Error message => .Error message
        | .OK _ => .OK (.Scall result (simpl_expr cenv fn) (simpl_exprlist cenv args))
    | .Sbuiltin result ef argTypes args =>
        match check_opttemp cenv result with
        | .Error message => .Error message
        | .OK _ => .OK (.Sbuiltin result ef argTypes (simpl_exprlist cenv args))
    | .Ssequence s₁ s₂ =>
        match simpl_stmt cfg cenv s₁ with
        | .Error message => .Error message
        | .OK s₁' =>
            match simpl_stmt cfg cenv s₂ with
            | .Error message => .Error message
            | .OK s₂' => .OK (.Ssequence s₁' s₂')
    | .Sifthenelse a s₁ s₂ =>
        match simpl_stmt cfg cenv s₁ with
        | .Error message => .Error message
        | .OK s₁' =>
            match simpl_stmt cfg cenv s₂ with
            | .Error message => .Error message
            | .OK s₂' => .OK (.Sifthenelse (simpl_expr cenv a) s₁' s₂')
    | .Sloop s₁ s₂ =>
        match simpl_stmt cfg cenv s₁ with
        | .Error message => .Error message
        | .OK s₁' =>
            match simpl_stmt cfg cenv s₂ with
            | .Error message => .Error message
            | .OK s₂' => .OK (.Sloop s₁' s₂')
    | .Sbreak => .OK .Sbreak
    | .Scontinue => .OK .Scontinue
    | .Sreturn result => .OK (.Sreturn (result.map (simpl_expr cenv)))
    | .Sswitch a cases =>
        match simpl_lblstmt cfg cenv cases with
        | .Error message => .Error message
        | .OK cases' => .OK (.Sswitch (simpl_expr cenv a) cases')
    | .Slabel label s =>
        match simpl_stmt cfg cenv s with
        | .Error message => .Error message
        | .OK s' => .OK (.Slabel label s')
    | .Sgoto label => .OK (.Sgoto label)

  def simpl_lblstmt (cfg : CompilerConfig) (cenv : compilenv) :
      labeled_statements → Res labeled_statements
    | .LSnil => .OK .LSnil
    | .LScons case s rest =>
        match simpl_stmt cfg cenv s with
        | .Error message => .Error message
        | .OK s' =>
            match simpl_lblstmt cfg cenv rest with
            | .Error message => .Error message
            | .OK rest' => .OK (.LScons case s' rest')
end

/-! ## Function parameters and address-taken analysis -/

def store_params (cenv : compilenv) :
    List (ident × type) → statement → statement
  | [], s => s
  | (id, ty) :: params, s =>
      if VSet.mem id cenv then
        if CompCert4Lean.X86.Conventions1.parameter_needs_normalization
            (argtype_of_type ty) then
          .Ssequence (.Sset id (make_cast (.Etempvar id ty) ty))
            (store_params cenv params s)
        else
          store_params cenv params s
      else
        .Ssequence (.Sassign (.Evar id ty) (.Etempvar id ty))
          (store_params cenv params s)

mutual
  def addr_taken_expr : expr → VSet.t
    | .Econst_int _ _ => VSet.empty
    | .Econst_float _ _ => VSet.empty
    | .Econst_single _ _ => VSet.empty
    | .Econst_long _ _ => VSet.empty
    | .Evar _ _ => VSet.empty
    | .Etempvar _ _ => VSet.empty
    | .Ederef a _ => addr_taken_expr a
    | .Eaddrof (.Evar id _) _ => VSet.singleton id
    | .Eaddrof a _ => addr_taken_expr a
    | .Eunop _ a _ => addr_taken_expr a
    | .Ebinop _ a₁ a₂ _ => VSet.union (addr_taken_expr a₁) (addr_taken_expr a₂)
    | .Ecast a _ => addr_taken_expr a
    | .Efield a _ _ => addr_taken_expr a
    | .Esizeof _ _ => VSet.empty
    | .Ealignof _ _ => VSet.empty

  def addr_taken_exprlist : List expr → VSet.t
    | [] => VSet.empty
    | a :: rest => VSet.union (addr_taken_expr a) (addr_taken_exprlist rest)

  def addr_taken_stmt : statement → VSet.t
    | .Sskip => VSet.empty
    | .Sassign a b => VSet.union (addr_taken_expr a) (addr_taken_expr b)
    | .Sset _ a => addr_taken_expr a
    | .Scall _ a args => VSet.union (addr_taken_expr a) (addr_taken_exprlist args)
    | .Sbuiltin _ _ _ args => addr_taken_exprlist args
    | .Ssequence s₁ s₂ => VSet.union (addr_taken_stmt s₁) (addr_taken_stmt s₂)
    | .Sifthenelse a s₁ s₂ =>
        VSet.union (addr_taken_expr a)
          (VSet.union (addr_taken_stmt s₁) (addr_taken_stmt s₂))
    | .Sloop s₁ s₂ => VSet.union (addr_taken_stmt s₁) (addr_taken_stmt s₂)
    | .Sbreak => VSet.empty
    | .Scontinue => VSet.empty
    | .Sreturn none => VSet.empty
    | .Sreturn (some a) => addr_taken_expr a
    | .Sswitch a cases => VSet.union (addr_taken_expr a) (addr_taken_lblstmt cases)
    | .Slabel _ s => addr_taken_stmt s
    | .Sgoto _ => VSet.empty

  def addr_taken_lblstmt : labeled_statements → VSet.t
    | .LSnil => VSet.empty
    | .LScons _ s rest => VSet.union (addr_taken_stmt s) (addr_taken_lblstmt rest)
end

def add_local_variable (addressTaken : VSet.t) (idType : ident × type)
    (cenv : compilenv) : compilenv :=
  let (id, ty) := idType
  match access_mode ty with
  | .By_value _ => if VSet.mem id addressTaken then cenv else VSet.add id cenv
  | _ => cenv

def cenv_for (f : function) : compilenv :=
  let addressTaken := addr_taken_stmt f.fn_body
  (f.fn_params ++ f.fn_vars).foldr (add_local_variable addressTaken) VSet.empty

/-! ## Function and whole-program transformation -/

def add_debug_var (idType : ident × type) (s : statement) : statement :=
  let (id, ty) := idType
  .Ssequence (Sdebug_var id ty) s

def add_debug_vars (cfg : CompilerConfig) (vars : List (ident × type))
    (s : statement) : statement :=
  if CompCert4Lean.Driver.Compopts.debug cfg then
    vars.foldr add_debug_var s
  else
    s

def add_debug_param (idType : ident × type) (s : statement) : statement :=
  let (id, ty) := idType
  .Ssequence (Sdebug_temp id ty) s

def add_debug_params (cfg : CompilerConfig) (params : List (ident × type))
    (s : statement) : statement :=
  if CompCert4Lean.Driver.Compopts.debug cfg then
    params.foldr add_debug_param s
  else
    s

def remove_lifted (cenv : compilenv) (vars : List (ident × type)) :
    List (ident × type) :=
  vars.filter fun idType => !(VSet.mem idType.1 cenv)

def add_lifted (cenv : compilenv) (vars₁ vars₂ : List (ident × type)) :
    List (ident × type) :=
  vars₁.filter (fun idType => VSet.mem idType.1 cenv) ++ vars₂

private def listDisjoint (left right : List ident) : Bool :=
  CompCert4Lean.Lib.Coqlib.proj_sumbool
    (CompCert4Lean.Lib.Coqlib.list_disjoint_dec
      CompCert4Lean.Common.AST.ident_eq left right)

def transf_function (cfg : CompilerConfig) (f : function) : Res function :=
  let cenv := cenv_for f
  if listDisjoint (var_names f.fn_params) (var_names f.fn_temps) then
    match simpl_stmt cfg cenv f.fn_body with
    | .Error message => .Error message
    | .OK body' =>
        let vars' := remove_lifted cenv (f.fn_params ++ f.fn_vars)
        let temps' := add_lifted cenv f.fn_vars f.fn_temps
        .OK
          { fn_return := f.fn_return
            fn_callconv := f.fn_callconv
            fn_params := f.fn_params
            fn_vars := vars'
            fn_temps := temps'
            fn_body :=
              add_debug_params cfg f.fn_params
                (store_params cenv f.fn_params
                  (add_debug_vars cfg vars' body')) }
  else
    assertion_failed

def transf_fundef (cfg : CompilerConfig) : fundef → Res fundef
  | .Internal f =>
      match transf_function cfg f with
      | .Error message => .Error message
      | .OK transformed => .OK (.Internal transformed)
  | .External ef args result cc => .OK (.External ef args result cc)

def transf_program (cfg : CompilerConfig) (p : program) : Res program :=
  match CompCert4Lean.Common.AST.transform_partial_program
      (transf_fundef cfg) (program_of_program p) with
  | .Error message => .Error message
  | .OK p' =>
      .OK
        { prog_defs := p'.prog_defs
          prog_public := p'.prog_public
          prog_main := p'.prog_main
          prog_types := p.prog_types
          prog_comp_env := p.prog_comp_env
          prog_comp_env_eq := p.prog_comp_env_eq }

end CompCert4Lean.Cfrontend.SimplLocals

namespace CompCert4Lean.Cfrontend.SimplLocals

namespace VSet

theorem mem_2_proof : mem_2 := by
  intro s x h
  exact CompCert4Lean.Lib.FSetAVLplus.Make.mem_2 s x h

theorem singleton_2_proof : singleton_2 := by
  intro x y hxy
  exact CompCert4Lean.Lib.FSetAVLplus.Make.singleton_2 x y hxy

theorem add_1_proof : add_1 := by
  intro s x y hxy
  exact CompCert4Lean.Lib.FSetAVLplus.Make.add_1 s x y hxy

end VSet

end CompCert4Lean.Cfrontend.SimplLocals
