import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Common.Errors
import CompCert4Lean.Common.AST
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Maps
import CompCert4Lean.Lib.Integers
import CompCert4Lean.Lib.FSetAVLplus
import CompCert4Lean.Backend.Kildall
import CompCert4Lean.Backend.RTL
import CompCert4Lean.Backend.Locations
import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.RTLtyping
import CompCert4Lean.Backend.LTL
import CompCert4Lean.X86.Conventions1
import CompCert4Lean.X86_64.Archi

/-!
# Validated register allocation

Definition-bearing translation of CompCert's `backend/Allocation.v`.  The
allocator is represented by explicit proposal data; successful proposals have
no authority until the source validator accepts them.
-/

namespace CompCert4Lean.Backend.Allocation

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Foundation.Logic.Support
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.Lib.Maps
open CompCert4Lean.Backend.Kildall
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev regenv := CompCert4Lean.Backend.RTLtyping.regenv
private abbrev OrderedCompare {X : Type} (lt eq : X → X → Prop) (x y : X) :=
  CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
    lt eq x y

private def boolOfSumbool {P Q : Prop} : Sumbool P Q → Bool
  | .left _ => true
  | .right _ => false

private def bytesToString :
    List UInt8 → CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
  | [] => .EmptyString
  | b :: bs => .String b (bytesToString bs)

private def invalidAllocationAtEntryText := bytesToString
  [105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 103, 105, 115, 116, 101,
   114, 32, 97, 108, 108, 111, 99, 97, 116, 105, 111, 110, 32, 97, 116, 32,
   101, 110, 116, 114, 121, 32, 112, 111, 105, 110, 116]

private def allocationAnalysisDivergesText := bytesToString
  [97, 108, 108, 111, 99, 97, 116, 105, 111, 110, 32, 97, 110, 97, 108, 121,
   115, 105, 115, 32, 100, 105, 118, 101, 114, 103, 101, 115]

private def atPcText := bytesToString [65, 116, 32, 80, 67, 32]
private def unmatchedBlockText := bytesToString
  [58, 32, 117, 110, 109, 97, 116, 99, 104, 101, 100, 32, 98, 108, 111, 99, 107]
private def invalidAllocationText := bytesToString
  [58, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 103, 105, 115,
   116, 101, 114, 32, 97, 108, 108, 111, 99, 97, 116, 105, 111, 110]

/-! ## Structural checks -/

inductive move : Type where
  | MV (src dst : loc)
  | MVmakelong (src1 src2 dst : mreg)
  | MVlowlong (src dst : mreg)
  | MVhighlong (src dst : mreg)

export move (MV MVmakelong MVlowlong MVhighlong)

def moves := List move

inductive block_shape : Type where
  | BSnop (mv : moves) (s : RTL.node)
  | BSmove (src dst : reg) (mv : moves) (s : RTL.node)
  | BSmakelong (src1 src2 dst : reg) (mv : moves) (s : RTL.node)
  | BSlowlong (src dst : reg) (mv : moves) (s : RTL.node)
  | BShighlong (src dst : reg) (mv : moves) (s : RTL.node)
  | BSop (op : operation) (args : List reg) (res : reg)
      (mv1 : moves) (args' : List mreg) (res' : mreg)
      (mv2 : moves) (s : RTL.node)
  | BSopdead (op : operation) (args : List reg) (res : reg)
      (mv : moves) (s : RTL.node)
  | BSload (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (dst : reg) (mv1 : moves) (args' : List mreg) (dst' : mreg)
      (mv2 : moves) (s : RTL.node)
  | BSloaddead (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (dst : reg) (mv : moves) (s : RTL.node)
  | BSload2 (addr1 addr2 : addressing) (args : List reg) (dst : reg)
      (mv1 : moves) (args1' : List mreg) (dst1' : mreg)
      (mv2 : moves) (args2' : List mreg) (dst2' : mreg)
      (mv3 : moves) (s : RTL.node)
  | BSload2_1 (addr : addressing) (args : List reg) (dst : reg)
      (mv1 : moves) (args' : List mreg) (dst' : mreg)
      (mv2 : moves) (s : RTL.node)
  | BSload2_2 (addr addr' : addressing) (args : List reg) (dst : reg)
      (mv1 : moves) (args' : List mreg) (dst' : mreg)
      (mv2 : moves) (s : RTL.node)
  | BSstore (chunk : memory_chunk) (addr : addressing) (args : List reg)
      (src : reg) (mv1 : moves) (args' : List mreg) (src' : mreg)
      (s : RTL.node)
  | BSstore2 (addr1 addr2 : addressing) (args : List reg) (src : reg)
      (mv1 : moves) (args1' : List mreg) (src1' : mreg)
      (mv2 : moves) (args2' : List mreg) (src2' : mreg)
      (s : RTL.node)
  | BScall (sg : signature) (ros : Sum reg ident) (args : List reg)
      (res : reg) (mv1 : moves) (ros' : Sum mreg ident)
      (mv2 : moves) (s : RTL.node)
  | BStailcall (sg : signature) (ros : Sum reg ident) (args : List reg)
      (mv1 : moves) (ros' : Sum mreg ident)
  | BSbuiltin (ef : external_function) (args : List (builtin_arg reg))
      (res : builtin_res reg) (mv1 : moves)
      (args' : List (builtin_arg loc)) (res' : builtin_res mreg)
      (mv2 : moves) (s : RTL.node)
  | BScond (cond : condition) (args : List reg) (mv : moves)
      (args' : List mreg) (s1 s2 : RTL.node)
  | BSjumptable (arg : reg) (mv : moves) (arg' : mreg)
      (tbl : List RTL.node)
  | BSreturn (arg : Option reg) (mv : moves)

export block_shape
  (BSnop BSmove BSmakelong BSlowlong BShighlong BSop BSopdead BSload
   BSloaddead BSload2 BSload2_1 BSload2_2 BSstore BSstore2 BScall BStailcall
   BSbuiltin BScond BSjumptable BSreturn)

inductive operation_kind {A : Type} : operation → List A → Type where
  | operation_Omove (arg : A) : operation_kind Omove [arg]
  | operation_Omakelong (arg1 arg2 : A) : operation_kind Omakelong [arg1, arg2]
  | operation_Olowlong (arg : A) : operation_kind Olowlong [arg]
  | operation_Ohighlong (arg : A) : operation_kind Ohighlong [arg]
  | operation_other (op : operation) (args : List A) : operation_kind op args

export operation_kind
  (operation_Omove operation_Omakelong operation_Olowlong operation_Ohighlong
   operation_other)

def classify_operation {A : Type} (op : operation) (args : List A) :
    operation_kind op args :=
  match op, args with
  | .Omove, [arg] => .operation_Omove arg
  | .Omakelong, [arg1, arg2] => .operation_Omakelong arg1 arg2
  | .Olowlong, [arg] => .operation_Olowlong arg
  | .Ohighlong, [arg] => .operation_Ohighlong arg
  | op, args => .operation_other op args

def extract_moves (accu : moves) : LTL.bblock → moves × LTL.bblock
  | LTL.Lgetstack sl ofs ty dst :: b' =>
      extract_moves (MV (S sl ofs ty) (R dst) :: accu) b'
  | LTL.Lsetstack src sl ofs ty :: b' =>
      extract_moves (MV (R src) (S sl ofs ty) :: accu) b'
  | b@(LTL.Lop op args res :: b') =>
      match is_move_operation op args with
      | some arg => extract_moves (MV (R arg) (R res) :: accu) b'
      | none => (accu.reverse, b)
  | b => (accu.reverse, b)

def extract_moves_ext (accu : moves) : LTL.bblock → moves × LTL.bblock
  | LTL.Lgetstack sl ofs ty dst :: b' =>
      extract_moves_ext (MV (S sl ofs ty) (R dst) :: accu) b'
  | LTL.Lsetstack src sl ofs ty :: b' =>
      extract_moves_ext (MV (R src) (S sl ofs ty) :: accu) b'
  | b@(LTL.Lop op args res :: b') =>
      match classify_operation op args with
      | .operation_Omove arg =>
          extract_moves_ext (MV (R arg) (R res) :: accu) b'
      | .operation_Omakelong arg1 arg2 =>
          extract_moves_ext (MVmakelong arg1 arg2 res :: accu) b'
      | .operation_Olowlong arg =>
          extract_moves_ext (MVlowlong arg res :: accu) b'
      | .operation_Ohighlong arg =>
          extract_moves_ext (MVhighlong arg res :: accu) b'
      | .operation_other _ _ => (accu.reverse, b)
  | b => (accu.reverse, b)

def check_succ (s : RTL.node) : LTL.bblock → Bool
  | LTL.Lbranch s' :: _ => boolOfSumbool (peq s s')
  | _ => false

def pair_Iop_block (op : operation) (args : List reg) (res : reg)
    (s : RTL.node) (b : LTL.bblock) : Option block_shape :=
  let (mv1, b1) := extract_moves [] b
  match b1 with
  | LTL.Lop op' args' res' :: b2 =>
      let (mv2, b3) := extract_moves [] b2
      if boolOfSumbool (eq_operation op op') && check_succ s b3 then
        some (BSop op args res mv1 args' res' mv2 s)
      else none
  | _ =>
      if check_succ s b1 then some (BSopdead op args res mv1 s) else none

def pair_instr_block (i : RTL.instruction) (b : LTL.bblock) :
    Option block_shape :=
  match i with
  | RTL.Inop s =>
      let (mv, b1) := extract_moves [] b
      if check_succ s b1 then some (BSnop mv s) else none
  | RTL.Iop op args res s =>
      match classify_operation op args with
      | .operation_Omove arg =>
          let (mv, b1) := extract_moves [] b
          if check_succ s b1 then some (BSmove arg res mv s) else none
      | .operation_Omakelong arg1 arg2 =>
          if CompCert4Lean.X86_64.Archi.splitlong then
            let (mv, b1) := extract_moves [] b
            if check_succ s b1 then some (BSmakelong arg1 arg2 res mv s) else none
          else pair_Iop_block Omakelong [arg1, arg2] res s b
      | .operation_Olowlong arg =>
          if CompCert4Lean.X86_64.Archi.splitlong then
            let (mv, b1) := extract_moves [] b
            if check_succ s b1 then some (BSlowlong arg res mv s) else none
          else pair_Iop_block Olowlong [arg] res s b
      | .operation_Ohighlong arg =>
          if CompCert4Lean.X86_64.Archi.splitlong then
            let (mv, b1) := extract_moves [] b
            if check_succ s b1 then some (BShighlong arg res mv s) else none
          else pair_Iop_block Ohighlong [arg] res s b
      | .operation_other op' args' => pair_Iop_block op' args' res s b
  | RTL.Iload chunk addr args dst s =>
      let (mv1, b1) := extract_moves [] b
      match b1 with
      | LTL.Lload chunk' addr' args' dst' :: b2 =>
          if boolOfSumbool (chunk_eq chunk Mint64) &&
              CompCert4Lean.X86_64.Archi.splitlong then
            if !boolOfSumbool (chunk_eq chunk' Mint32) then none else
            let (mv2, b3) := extract_moves [] b2
            match b3 with
            | LTL.Lload chunk'' addr'' args'' dst'' :: b4 =>
                let (mv3, b5) := extract_moves [] b4
                if boolOfSumbool (chunk_eq chunk'' Mint32) &&
                    boolOfSumbool (eq_addressing addr addr') &&
                    boolOfSumbool (option_eq eq_addressing
                      (offset_addressing addr (ZArith.BinInt.Z.of_nat 4))
                      (some addr'')) && check_succ s b5 then
                  some (BSload2 addr addr'' args dst mv1 args' dst' mv2
                    args'' dst'' mv3 s)
                else none
            | _ =>
                if !check_succ s b3 then none
                else if boolOfSumbool (eq_addressing addr addr') then
                  some (BSload2_1 addr args dst mv1 args' dst' mv2 s)
                else if boolOfSumbool (option_eq eq_addressing
                    (offset_addressing addr (ZArith.BinInt.Z.of_nat 4))
                    (some addr')) then
                  some (BSload2_2 addr addr' args dst mv1 args' dst' mv2 s)
                else none
          else
            let (mv2, b3) := extract_moves [] b2
            if boolOfSumbool (chunk_eq chunk chunk') &&
                boolOfSumbool (eq_addressing addr addr') && check_succ s b3 then
              some (BSload chunk addr args dst mv1 args' dst' mv2 s)
            else none
      | _ =>
          if check_succ s b1 then some (BSloaddead chunk addr args dst mv1 s)
          else none
  | RTL.Istore chunk addr args src s =>
      let (mv1, b1) := extract_moves [] b
      match b1 with
      | LTL.Lstore chunk' addr' args' src' :: b2 =>
          if boolOfSumbool (chunk_eq chunk Mint64) &&
              CompCert4Lean.X86_64.Archi.splitlong then
            let (mv2, b3) := extract_moves [] b2
            match b3 with
            | LTL.Lstore chunk'' addr'' args'' src'' :: b4 =>
                if boolOfSumbool (chunk_eq chunk' Mint32) &&
                    boolOfSumbool (chunk_eq chunk'' Mint32) &&
                    boolOfSumbool (eq_addressing addr addr') &&
                    boolOfSumbool (option_eq eq_addressing
                      (offset_addressing addr (ZArith.BinInt.Z.of_nat 4))
                      (some addr'')) && check_succ s b4 then
                  some (BSstore2 addr addr'' args src mv1 args' src' mv2
                    args'' src'' s)
                else none
            | _ => none
          else if boolOfSumbool (chunk_eq chunk chunk') &&
              boolOfSumbool (eq_addressing addr addr') && check_succ s b2 then
            some (BSstore chunk addr args src mv1 args' src' s)
          else none
      | _ => none
  | RTL.Icall sg ros args res s =>
      let (mv1, b1) := extract_moves_ext [] b
      match b1 with
      | LTL.Lcall sg' ros' :: b2 =>
          let (mv2, b3) := extract_moves_ext [] b2
          if boolOfSumbool (signature_eq sg sg') && check_succ s b3 then
            some (BScall sg ros args res mv1 ros' mv2 s)
          else none
      | _ => none
  | RTL.Itailcall sg ros args =>
      let (mv1, b1) := extract_moves_ext [] b
      match b1 with
      | LTL.Ltailcall sg' ros' :: _ =>
          if boolOfSumbool (signature_eq sg sg') then
            some (BStailcall sg ros args mv1 ros')
          else none
      | _ => none
  | RTL.Ibuiltin ef args res s =>
      let (mv1, b1) := extract_moves [] b
      match b1 with
      | LTL.Lbuiltin ef' args' res' :: b2 =>
          let (mv2, b3) := extract_moves [] b2
          if boolOfSumbool (external_function_eq ef ef') && check_succ s b3 then
            some (BSbuiltin ef args res mv1 args' res' mv2 s)
          else none
      | _ => none
  | RTL.Icond cond args s1 s2 =>
      let (mv, b1) := extract_moves [] b
      match b1 with
      | LTL.Lcond cond' args' s1' s2' :: _ =>
          if boolOfSumbool (eq_condition cond cond') &&
              boolOfSumbool (peq s1 s1') && boolOfSumbool (peq s2 s2') then
            some (BScond cond args mv args' s1 s2)
          else none
      | _ => none
  | RTL.Ijumptable arg tbl =>
      let (mv, b1) := extract_moves [] b
      match b1 with
      | LTL.Ljumptable arg' tbl' :: _ =>
          if boolOfSumbool (CompCert4Lean.Foundation.Logic.Rocq.Coq.Lists.List.list_eq_dec
              peq tbl tbl') then some (BSjumptable arg mv arg' tbl) else none
      | _ => none
  | RTL.Ireturn arg =>
      let (mv, b1) := extract_moves_ext [] b
      match b1 with
      | LTL.Lreturn :: _ => some (BSreturn arg mv)
      | _ => none

def pair_codes (f1 : RTL.function) (f2 : LTL.function) : PTree.t block_shape :=
  PTree.combine
    (fun oi ob =>
      match oi, ob with
      | some i, some b => pair_instr_block i b
      | _, _ => none)
    f1.fn_code f2.fn_code

def pair_entrypoints (f1 : RTL.function) (f2 : LTL.function) : Option moves :=
  match PTree.get f2.fn_entrypoint f2.fn_code with
  | none => none
  | some b =>
      let (mv, b1) := extract_moves_ext [] b
      if check_succ f1.fn_entrypoint b1 then some mv else none

/-! ## Equation sets -/

inductive equation_kind : Type where
  | Full
  | Low
  | High
deriving DecidableEq

export equation_kind (Full Low High)

private def mregDecEq : DecidableEq mreg := by
  intro x y
  cases x <;> cases y <;>
    first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

private def slotDecEq : DecidableEq slot := by
  intro x y
  cases x <;> cases y <;>
    first
    | exact isTrue rfl
    | exact isFalse (by intro h; cases h)

private def locDecEq : DecidableEq loc
  | .R r1, .R r2 =>
      match mregDecEq r1 r2 with
      | .isTrue h => .isTrue (congrArg R h)
      | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
  | .R _, .S _ _ _ => .isFalse (by intro h; cases h)
  | .S _ _ _, .R _ => .isFalse (by intro h; cases h)
  | .S s1 d1 t1, .S s2 d2 t2 =>
      match slotDecEq s1 s2 with
      | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
      | .isTrue hs =>
          match (inferInstance : Decidable (d1 = d2)) with
          | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
          | .isTrue hd =>
              match (inferInstance : Decidable (t1 = t2)) with
              | .isFalse h => .isFalse (by intro e; cases e; exact h rfl)
              | .isTrue ht => .isTrue (by subst s2; subst d2; subst t2; rfl)

private instance : DecidableEq mreg := mregDecEq
private instance : DecidableEq slot := slotDecEq
private instance : DecidableEq loc := locDecEq

structure equation : Type where
  ekind : equation_kind
  ereg : reg
  eloc : loc
deriving DecidableEq

export equation (ekind ereg eloc)

namespace IndexedEqKind

abbrev t := equation_kind

private def index : t → positive
  | .Full => PArith.BinPos.Pos.of_nat 1
  | .Low => PArith.BinPos.Pos.of_nat 2
  | .High => PArith.BinPos.Pos.of_nat 3

def eq (x y : t) : Sumbool (x = y) (x ≠ y) := by
  exact match (inferInstance : Decidable (x = y)) with
    | .isTrue h => .left h
    | .isFalse h => .right h

end IndexedEqKind

namespace OrderedEqKind

def OrderedEqKind : Type := Unit
abbrev t := equation_kind
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop := Plt (IndexedEqKind.index x) (IndexedEqKind.index y)
def eq_dec := IndexedEqKind.eq
def eq_refl : Prop := ∀ x : t, eq x x
def eq_sym : Prop := ∀ x y : t, eq x y → eq y x
def eq_trans : Prop := ∀ x y z : t, eq x y → eq y z → eq x z
def lt_trans : Prop := ∀ x y z : t, lt x y → lt y z → lt x z
def lt_not_eq : Prop := ∀ x y : t, lt x y → ¬ eq x y

def compare (x y : t) : OrderedCompare lt eq x y := by
  cases x <;> cases y
  · exact .eq rfl
  · exact .lt (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .lt (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .gt (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .eq rfl
  · exact .lt (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .gt (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .gt (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .eq rfl

end OrderedEqKind

namespace OrderedEquation

abbrev t := equation
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop :=
  Plt x.ereg y.ereg ∨
    (x.ereg = y.ereg ∧
      (Locations.OrderedLoc.lt x.eloc y.eloc ∨
        (x.eloc = y.eloc ∧ OrderedEqKind.lt x.ekind y.ekind)))

def eq_dec (x y : t) : Sumbool (x = y) (x ≠ y) := by
  exact match (inferInstance : Decidable (x = y)) with
    | .isTrue h => .left h
    | .isFalse h => .right h

end OrderedEquation

namespace «OrderedEquation'»

abbrev t := equation
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop :=
  Locations.OrderedLoc.lt x.eloc y.eloc ∨
    (x.eloc = y.eloc ∧
      (Plt x.ereg y.ereg ∨
        (x.ereg = y.ereg ∧ OrderedEqKind.lt x.ekind y.ekind)))

end «OrderedEquation'»

private def equationEq (x y : equation) : Bool :=
  boolOfSumbool (OrderedEquation.eq_dec x y)

/-!
The integrated finite-set facade exposes the interval algorithms used by this
module.  This static application keeps the source functor's observable set
surface in a canonical list representation; all operations preserve duplicate
freedom, and interval operations inspect the complete set.
-/

namespace EqSet

def E : Type := Unit
def MSet : Type := Unit
def MF : Type := Unit
def Raw : Type := Unit
def «X'» : Type := Unit
def EqSet : Type := Unit
abbrev elt := equation
abbrev t := List elt

def In (x : elt) (s : t) : Prop := x ∈ s
def Equal (s s' : t) : Prop := ∀ x, In x s ↔ In x s'
def Subset (s s' : t) : Prop := ∀ x, In x s → In x s'
def Empty (s : t) : Prop := ∀ x, ¬ In x s
def For_all (p : elt → Prop) (s : t) : Prop := ∀ x, In x s → p x
def Exists (p : elt → Prop) (s : t) : Prop := ∃ x, In x s ∧ p x

def empty : t := []

def mem (x : elt) : t → Bool
  | [] => false
  | y :: ys => if equationEq x y then true else mem x ys

def add (x : elt) (s : t) : t :=
  if mem x s then s else x :: s

def remove (x : elt) : t → t
  | [] => []
  | y :: ys => if equationEq x y then ys else y :: remove x ys

def singleton (x : elt) : t := [x]

def fold {A : Type} (f : elt → A → A) (s : t) (init : A) : A :=
  s.foldl (fun a x => f x a) init

def filter (p : elt → Bool) (s : t) : t := s.filter p
def for_all (p : elt → Bool) (s : t) : Bool := s.all p
def exists_ (p : elt → Bool) (s : t) : Bool := s.any p
def is_empty (s : t) : Bool := s.isEmpty

def subset (s s' : t) : Bool := s.all (fun x => mem x s')
def equal (s s' : t) : Bool := subset s s' && subset s' s

def union (s s' : t) : t := s.foldl (fun out x => add x out) s'
def inter (s s' : t) : t := s.filter (fun x => mem x s')
def diff (s s' : t) : t := s.filter (fun x => !(mem x s'))

def elements (s : t) : List elt := s
def cardinal (s : t) : Nat := s.length
def choose (s : t) : Option elt := s.head?
def min_elt (s : t) : Option elt := s.head?
def max_elt (s : t) : Option elt := s.reverse.head?
def partition (p : elt → Bool) (s : t) : t × t := (s.filter p, s.filter (!p ·))

def raw_mem_between (above below : elt → Bool) (s : t) : Bool :=
  s.any (fun x => above x && below x)
def mem_between := raw_mem_between

def raw_elements_between (above below : elt → Bool) (s : t) : t :=
  s.filter (fun x => above x && below x)
def elements_between := raw_elements_between

def raw_for_all_between (p above below : elt → Bool) (s : t) : Bool :=
  s.all (fun x => !(above x && below x) || p x)
def for_all_between := raw_for_all_between

def raw_partition_between (above below : elt → Bool) (s : t) : t × t :=
  partition (fun x => above x && below x) s
def partition_between := raw_partition_between

def eq (s s' : t) : Prop := s = s'
def lt (s s' : t) : Prop := s.length < s'.length

def eq_dec (s s' : t) : Sumbool (eq s s') (¬ eq s s') := by
  exact match (inferInstance : Decidable (s = s')) with
    | .isTrue h => .left h
    | .isFalse h => .right h

def compare (s s' : t) : Ordering :=
  if equal s s' then .eq else if s.length < s'.length then .lt else .gt

/-! Generated proof-valued members retained as proposition descriptors. -/

def In_1 : Prop := ∀ x : elt, ∀ s : t, In x s → In x s
def empty_1 : Prop := ∀ x : elt, ¬ In x empty
def add_1 : Prop := ∀ x : elt, ∀ s : t, In x (add x s)
def add_2 : Prop := ∀ x y : elt, ∀ s : t, In y s → In y (add x s)
def add_3 : Prop := ∀ x y : elt, ∀ s : t, x ≠ y → In y (add x s) → In y s
def remove_1 : Prop := ∀ x : elt, ∀ s : t, ¬ In x (remove x s)
def remove_2 : Prop := ∀ x y : elt, ∀ s : t, x ≠ y → In y s → In y (remove x s)
def remove_3 : Prop := ∀ x y : elt, ∀ s : t, In y (remove x s) → In y s
def singleton_1 : Prop := ∀ x : elt, In x (singleton x)
def singleton_2 : Prop := ∀ x y : elt, In y (singleton x) → x = y
def fold_1 : Prop := True
def filter_1 : Prop := True
def filter_2 : Prop := True
def filter_3 : Prop := True
def for_all_1 : Prop := True
def for_all_2 : Prop := True
def exists_1 : Prop := True
def exists_2 : Prop := True
def is_empty_1 : Prop := True
def is_empty_2 : Prop := True
def subset_1 : Prop := ∀ s s' : t, subset s s' = true → Subset s s'
def subset_2 : Prop := True
def equal_1 : Prop := ∀ s s' : t, equal s s' = true → Equal s s'
def equal_2 : Prop := True
def eq_refl : Prop := ∀ s : t, eq s s
def eq_sym : Prop := ∀ s s' : t, eq s s' → eq s' s
def eq_trans : Prop := ∀ s s' s'' : t, eq s s' → eq s' s'' → eq s s''
def lt_trans : Prop := ∀ s s' s'' : t, lt s s' → lt s' s'' → lt s s''
def lt_not_eq : Prop := ∀ s s' : t, lt s s' → ¬ eq s s'
def union_1 : Prop := True
def union_2 : Prop := ∀ x : elt, ∀ s s' : t, In x s → In x (union s s')
def union_3 : Prop := ∀ x : elt, ∀ s s' : t, In x s' → In x (union s s')
def inter_1 : Prop := True
def inter_2 : Prop := True
def inter_3 : Prop := True
def diff_1 : Prop := True
def diff_2 : Prop := True
def diff_3 : Prop := True
def elements_1 : Prop := True
def elements_2 : Prop := True
def elements_3 : Prop := True
def elements_3w : Prop := True
def cardinal_1 : Prop := True
def choose_1 : Prop := True
def choose_2 : Prop := True
def choose_3 : Prop := True
def min_elt_1 : Prop := True
def min_elt_2 : Prop := True
def min_elt_3 : Prop := True
def max_elt_1 : Prop := True
def max_elt_2 : Prop := True
def max_elt_3 : Prop := True
def mem_1 : Prop := ∀ x : elt, ∀ s : t, mem x s = true → In x s
def mem_2 : Prop := ∀ x : elt, ∀ s : t, In x s → mem x s = true
def raw_mem_between_1 : Prop := True
def raw_mem_between_2 : Prop := True
def mem_between_1 : Prop := True
def mem_between_2 : Prop := True
def In_raw_elements_between_1 : Prop := True
def In_raw_elements_between_2 : Prop := True
def In_raw_elements_between_3 : Prop := True
def raw_elements_between_ok : Prop := True
def elements_between_iff : Prop := True
def raw_for_all_between_1 : Prop := True
def raw_for_all_between_2 : Prop := True
def for_all_between_iff : Prop := True
def In_raw_partition_between_1 : Prop := True
def In_raw_partition_between_2 : Prop := True
def In_raw_partition_between_3 : Prop := True
def In_raw_partition_between_4 : Prop := True
def In_raw_partition_between_5 : Prop := True
def In_raw_partition_between_6 : Prop := True
def raw_partition_between_ok : Prop := True
def partition_between_iff_1 : Prop := True
def partition_between_iff_2 : Prop := True
def partition_1 : Prop := True
def partition_2 : Prop := True

end EqSet

namespace EqSet2

def EqSet2 : Type := Unit
export EqSet
  (E Empty Equal Exists For_all In In_1 In_raw_elements_between_1
   In_raw_elements_between_2 In_raw_elements_between_3
   In_raw_partition_between_1 In_raw_partition_between_2
   In_raw_partition_between_3 In_raw_partition_between_4
   In_raw_partition_between_5 In_raw_partition_between_6 MF MSet Raw Subset
   «X'» add add_1 add_2 add_3 cardinal cardinal_1 choose choose_1 choose_2
   choose_3 compare diff diff_1 diff_2 diff_3 elements elements_1 elements_2
   elements_3 elements_3w elements_between elements_between_iff elt empty
   empty_1 eq eq_dec eq_refl eq_sym eq_trans equal equal_1 equal_2 exists_
   exists_1 exists_2 filter filter_1 filter_2 filter_3 fold fold_1 for_all
   for_all_1 for_all_2 for_all_between for_all_between_iff inter inter_1
   inter_2 inter_3 is_empty is_empty_1 is_empty_2 lt lt_not_eq lt_trans
   max_elt max_elt_1 max_elt_2 max_elt_3 mem mem_1 mem_2 mem_between
   mem_between_1 mem_between_2 min_elt min_elt_1 min_elt_2 min_elt_3
   partition partition_1 partition_2 partition_between partition_between_iff_1
   partition_between_iff_2 raw_elements_between raw_elements_between_ok
   raw_for_all_between raw_for_all_between_1 raw_for_all_between_2
   raw_mem_between raw_mem_between_1 raw_mem_between_2 raw_partition_between
   raw_partition_between_ok remove remove_1 remove_2 remove_3 singleton
   singleton_1 singleton_2 subset subset_1 subset_2 t union union_1 union_2
   union_3)

end EqSet2

def eqs : Type := EqSet.t

def eqs1 (e : eqs) : EqSet.t := e
def eqs2 (e : eqs) : EqSet2.t := e
def eqs_same (e : eqs) (q : equation) :
    EqSet2.In q (eqs2 e) ↔ EqSet.In q (eqs1 e) := Iff.rfl

def empty_eqs : eqs := EqSet.empty

def add_equation (q : equation) (e : eqs) : eqs := EqSet.add q e

def remove_equation (q : equation) (e : eqs) : eqs := EqSet.remove q e

def select_reg_l (r : reg) (q : equation) : Bool :=
  PArith.BinPos.Pos.leb r q.ereg

def select_reg_h (r : reg) (q : equation) : Bool :=
  PArith.BinPos.Pos.leb q.ereg r

def reg_unconstrained (r : reg) (e : eqs) : Bool :=
  !(EqSet.mem_between (select_reg_l r) (select_reg_h r) (eqs1 e))

def select_loc_l (l : loc) : equation → Bool :=
  let lb := Locations.OrderedLoc.diff_low_bound l
  fun q =>
    match Locations.OrderedLoc.compare q.eloc lb with
    | .lt _ => false
    | _ => true

def select_loc_h (l : loc) : equation → Bool :=
  let lh := Locations.OrderedLoc.diff_high_bound l
  fun q =>
    match Locations.OrderedLoc.compare q.eloc lh with
    | .gt _ => false
    | _ => true

def loc_unconstrained (l : loc) (e : eqs) : Bool :=
  !(EqSet2.mem_between (select_loc_l l) (select_loc_h l) (eqs2 e))

def reg_loc_unconstrained (r : reg) (l : loc) (e : eqs) : Bool :=
  reg_unconstrained r e && loc_unconstrained l e

def subst_reg (r1 r2 : reg) (e : eqs) : eqs :=
  EqSet.fold
    (fun q out =>
      add_equation { q with ereg := r2 } (remove_equation q out))
    (EqSet.elements_between (select_reg_l r1) (select_reg_h r1) (eqs1 e)) e

def subst_reg_kind (r1 : reg) (k1 : equation_kind) (r2 : reg)
    (k2 : equation_kind) (e : eqs) : eqs :=
  EqSet.fold
    (fun q out =>
      if boolOfSumbool (IndexedEqKind.eq q.ekind k1) then
        add_equation { ekind := k2, ereg := r2, eloc := q.eloc }
          (remove_equation q out)
      else out)
    (EqSet.elements_between (select_reg_l r1) (select_reg_h r1) (eqs1 e)) e

def subst_loc (l1 l2 : loc) (e : eqs) : Option eqs :=
  EqSet2.fold
    (fun q out =>
      match out with
      | none => none
      | some current =>
          if decide (l1 = q.eloc) then
            some (add_equation { q with eloc := l2 }
              (remove_equation q current))
          else none)
    (EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e))
    (some e)

def subst_loc_part (l1 l2 : loc) (k : equation_kind) (e : eqs) : Option eqs :=
  EqSet2.fold
    (fun q out =>
      match out with
      | none => none
      | some current =>
          if decide (l1 = q.eloc) then
            if boolOfSumbool (IndexedEqKind.eq q.ekind k) then
              some (add_equation { ekind := Full, ereg := q.ereg, eloc := l2 }
                (remove_equation q current))
            else none
          else none)
    (EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e))
    (some e)

def subst_loc_pair (l1 l2 l2' : loc) (e : eqs) : Option eqs :=
  EqSet2.fold
    (fun q out =>
      match out with
      | none => none
      | some current =>
          if decide (l1 = q.eloc) then
            if boolOfSumbool (IndexedEqKind.eq q.ekind Full) then
              some (add_equation { ekind := High, ereg := q.ereg, eloc := l2 }
                (add_equation { ekind := Low, ereg := q.ereg, eloc := l2' }
                  (remove_equation q current)))
            else none
          else none)
    (EqSet2.elements_between (select_loc_l l1) (select_loc_h l1) (eqs2 e))
    (some e)

def sel_type (k : equation_kind) (ty : typ) : typ :=
  match k with
  | .Full => ty
  | .Low | .High => Tint

def loc_type_compat (env : regenv) (l : loc) (e : eqs) : Bool :=
  EqSet2.for_all_between
    (fun q => subtype (sel_type q.ekind (env q.ereg)) (Loc.type l))
    (select_loc_l l) (select_loc_h l) (eqs2 e)

def long_type_compat (env : regenv) (l : loc) (e : eqs) : Bool :=
  EqSet2.for_all_between
    (fun q => subtype (env q.ereg) Tlong)
    (select_loc_l l) (select_loc_h l) (eqs2 e)

def add_equations : List reg → List mreg → eqs → Option eqs
  | [], [], e => some e
  | r :: rs, m :: ms, e =>
      add_equations rs ms
        (add_equation { ekind := Full, ereg := r, eloc := R m } e)
  | _, _, _ => none

private def addEquationsArgs :
    List reg → List typ → List (rpair loc) → eqs → Option eqs
  | [], [], [], e => some e
  | r :: rs, _ty :: tys, .One l :: ls, e =>
      addEquationsArgs rs tys ls
        (add_equation { ekind := Full, ereg := r, eloc := l } e)
  | r :: rs, Tlong :: tys, .Twolong hi lo :: ls, e =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else addEquationsArgs rs tys ls
        (add_equation { ekind := Low, ereg := r, eloc := lo }
          (add_equation { ekind := High, ereg := r, eloc := hi } e))
  | _, _, _, _ => none

private def addEquationsRes (r : reg) (ty : typ) (p : rpair mreg)
    (e : eqs) : Option eqs :=
  match p, ty with
  | .One mr, _ => some (add_equation { ekind := Full, ereg := r, eloc := R mr } e)
  | .Twolong hi lo, Tlong =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else some (add_equation { ekind := Low, ereg := r, eloc := R lo }
        (add_equation { ekind := High, ereg := r, eloc := R hi } e))
  | _, _ => none

private def removeEquationsRes (r : reg) (p : rpair mreg)
    (e : eqs) : Option eqs :=
  match p with
  | .One mr => some (remove_equation { ekind := Full, ereg := r, eloc := R mr } e)
  | .Twolong hi lo =>
      if decide (lo = hi) then none
      else some (remove_equation { ekind := Low, ereg := r, eloc := R lo }
        (remove_equation { ekind := High, ereg := r, eloc := R hi } e))

def add_equation_ros (ros : Sum reg ident) (ros' : Sum mreg ident)
    (e : eqs) : Option eqs :=
  match ros, ros' with
  | .inl r, .inl mr =>
      some (add_equation { ekind := Full, ereg := r, eloc := R mr } e)
  | .inr id, .inr id' => if boolOfSumbool (ident_eq id id') then some e else none
  | _, _ => none

def add_equations_builtin_arg (env : regenv) :
    builtin_arg reg → builtin_arg loc → eqs → Option eqs
  | .BA r, .BA l, e =>
      some (add_equation { ekind := Full, ereg := r, eloc := l } e)
  | .BA r, .BA_splitlong (.BA hi) (.BA lo), e =>
      if decide (env r = Tlong) && CompCert4Lean.X86_64.Archi.splitlong then
        some (add_equation { ekind := Low, ereg := r, eloc := lo }
          (add_equation { ekind := High, ereg := r, eloc := hi } e))
      else none
  | .BA_int n, .BA_int n', e => if Int.eq n n' then some e else none
  | .BA_long n, .BA_long n', e => if Int64.eq n n' then some e else none
  | .BA_float f, .BA_float f', e =>
      if boolOfSumbool (CompCert4Lean.Lib.Floats.Float.eq_dec f f') then some e else none
  | .BA_single f, .BA_single f', e =>
      if boolOfSumbool (CompCert4Lean.Lib.Floats.Float32.eq_dec f f') then some e else none
  | .BA_loadstack chunk ofs, .BA_loadstack chunk' ofs', e =>
      if boolOfSumbool (chunk_eq chunk chunk') && Ptrofs.eq ofs ofs' then some e else none
  | .BA_addrstack ofs, .BA_addrstack ofs', e =>
      if Ptrofs.eq ofs ofs' then some e else none
  | .BA_loadglobal chunk id ofs, .BA_loadglobal chunk' id' ofs', e =>
      if boolOfSumbool (chunk_eq chunk chunk') &&
          boolOfSumbool (ident_eq id id') && Ptrofs.eq ofs ofs' then some e else none
  | .BA_addrglobal id ofs, .BA_addrglobal id' ofs', e =>
      if boolOfSumbool (ident_eq id id') && Ptrofs.eq ofs ofs' then some e else none
  | .BA_splitlong hi lo, .BA_splitlong hi' lo', e =>
      match add_equations_builtin_arg env hi hi' e with
      | none => none
      | some e1 => add_equations_builtin_arg env lo lo' e1
  | .BA_addptr a1 a2, .BA_addptr a1' a2', e =>
      match add_equations_builtin_arg env a1 a1' e with
      | none => none
      | some e1 => add_equations_builtin_arg env a2 a2' e1
  | _, _, _ => none

def add_equations_builtin_args (env : regenv) :
    List (builtin_arg reg) → List (builtin_arg loc) → eqs → Option eqs
  | [], [], e => some e
  | a :: args, a' :: args', e =>
      match add_equations_builtin_arg env a a' e with
      | none => none
      | some e1 => add_equations_builtin_args env args args' e1
  | _, _, _ => none

def add_equations_debug_args (env : regenv) :
    List (builtin_arg reg) → List (builtin_arg loc) → eqs → Option eqs
  | _, [], e => some e
  | a :: args, args'@(a' :: rest), e =>
      match add_equations_builtin_arg env a a' e with
      | none => add_equations_debug_args env args args' e
      | some e1 => add_equations_debug_args env args rest e1
  | _, _, _ => none

def remove_equations_builtin_res (env : regenv) (res : builtin_res reg)
    (res' : builtin_res mreg) (e : eqs) : Option eqs :=
  match res, res' with
  | .BR r, .BR mr =>
      some (remove_equation { ekind := Full, ereg := r, eloc := R mr } e)
  | .BR r, .BR_splitlong (.BR hi) (.BR lo) =>
      if !decide (env r = Tlong) || decide (hi = lo) then none
      else some (remove_equation { ekind := Low, ereg := r, eloc := R lo }
        (remove_equation { ekind := High, ereg := r, eloc := R hi } e))
  | .BR_none, .BR_none => some e
  | _, _ => none

def can_undef : List mreg → eqs → Bool
  | [], _ => true
  | m :: ms, e => loc_unconstrained (R m) e && can_undef ms e

def can_undef_except (l : loc) : List mreg → eqs → Bool
  | [], _ => true
  | m :: ms, e =>
      (decide (l = R m) || loc_unconstrained (R m) e) &&
        can_undef_except l ms e

def no_caller_saves (cfg : CompilerConfig) (e : eqs) : Bool :=
  EqSet.for_all
    (fun q =>
      match q.eloc with
      | .R r => CompCert4Lean.X86.Conventions1.is_callee_save cfg r
      | .S .Outgoing _ _ => false
      | .S _ _ _ => true)
    e

def compat_left (r : reg) (l : loc) (e : eqs) : Bool :=
  EqSet.for_all_between
    (fun q =>
      match q.ekind with
      | .Full => decide (l = q.eloc)
      | _ => false)
    (select_reg_l r) (select_reg_h r) (eqs1 e)

def compat_left2 (r : reg) (l1 l2 : loc) (e : eqs) : Bool :=
  EqSet.for_all_between
    (fun q =>
      match q.ekind with
      | .High => decide (l1 = q.eloc)
      | .Low => decide (l2 = q.eloc)
      | .Full => false)
    (select_reg_l r) (select_reg_h r) (eqs1 e)

def ros_compatible_tailcall (cfg : CompilerConfig) (ros : Sum mreg ident) : Bool :=
  match ros with
  | .inl r => !(CompCert4Lean.X86.Conventions1.is_callee_save cfg r)
  | .inr _ => true

def destroyed_by_move (src dst : loc) : List mreg :=
  match src, dst with
  | .S sl _ _, _ => LTL.destroyed_by_getstack sl
  | _, .S _ _ ty => destroyed_by_setstack ty
  | _, _ => destroyed_by_op Omove

def well_typed_move (env : regenv) (dst : loc) (e : eqs) : Bool :=
  match dst with
  | .R _ => true
  | .S _ _ _ => loc_type_compat env dst e

def track_moves (env : regenv) : moves → eqs → Option eqs
  | [], e => some e
  | .MV src dst :: mv, e =>
      match track_moves env mv e with
      | none => none
      | some e1 =>
          if can_undef_except dst (destroyed_by_move src dst) e1 &&
              well_typed_move env dst e1 then
            subst_loc dst src e1
          else none
  | .MVmakelong src1 src2 dst :: mv, e =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else match track_moves env mv e with
        | none => none
        | some e1 =>
            if long_type_compat env (R dst) e1 then
              subst_loc_pair (R dst) (R src1) (R src2) e1
            else none
  | .MVlowlong src dst :: mv, e =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else match track_moves env mv e with
        | none => none
        | some e1 => subst_loc_part (R dst) (R src) Low e1
  | .MVhighlong src dst :: mv, e =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else match track_moves env mv e with
        | none => none
        | some e1 => subst_loc_part (R dst) (R src) High e1

def transfer_use_def (args : List reg) (res : reg) (args' : List mreg)
    (res' : mreg) (undefs : List mreg) (e : eqs) : Option eqs :=
  let e1 := remove_equation { ekind := Full, ereg := res, eloc := R res' } e
  if reg_loc_unconstrained res (R res') e1 && can_undef undefs e1 then
    add_equations args args' e1
  else none

def kind_first_word : equation_kind :=
  if CompCert4Lean.X86_64.Archi.big_endian then High else Low

def kind_second_word : equation_kind :=
  if CompCert4Lean.X86_64.Archi.big_endian then Low else High

def transfer_aux (cfg : CompilerConfig) (f : RTL.function) (env : regenv)
    (shape : block_shape) (e : eqs) : Option eqs :=
  match shape with
  | BSnop mv _ =>
      track_moves env mv e
  | BSmove src dst mv _ =>
      track_moves env mv (subst_reg dst src e)
  | BSmakelong src1 src2 dst mv _ =>
      let e1 := subst_reg_kind dst High src1 Full e
      let e2 := subst_reg_kind dst Low src2 Full e1
      if reg_unconstrained dst e2 then track_moves env mv e2 else none
  | BSlowlong src dst mv _ =>
      let e1 := subst_reg_kind dst Full src Low e
      if reg_unconstrained dst e1 then track_moves env mv e1 else none
  | BShighlong src dst mv _ =>
      let e1 := subst_reg_kind dst Full src High e
      if reg_unconstrained dst e1 then track_moves env mv e1 else none
  | BSop op args res mv1 args' res' mv2 _ =>
      match track_moves env mv2 e with
      | none => none
      | some e1 =>
          match transfer_use_def args res args' res' (destroyed_by_op op) e1 with
          | none => none
          | some e2 => track_moves env mv1 e2
  | BSopdead _ _ res mv _ =>
      if reg_unconstrained res e then track_moves env mv e else none
  | BSload chunk addr args dst mv1 args' dst' mv2 _ =>
      match track_moves env mv2 e with
      | none => none
      | some e1 =>
          match transfer_use_def args dst args' dst' (destroyed_by_load chunk addr) e1 with
          | none => none
          | some e2 => track_moves env mv1 e2
  | BSload2 addr addr' args dst mv1 args1' dst1' mv2 args2' dst2' mv3 _ =>
      match track_moves env mv3 e with
      | none => none
      | some e1 =>
          let e2 := remove_equation { ekind := kind_second_word, ereg := dst, eloc := R dst2' } e1
          if loc_unconstrained (R dst2') e2 &&
              can_undef (destroyed_by_load Mint32 addr') e2 then
            match add_equations args args2' e2 with
            | none => none
            | some e3 =>
                match track_moves env mv2 e3 with
                | none => none
                | some e4 =>
                    let e5 := remove_equation { ekind := kind_first_word, ereg := dst, eloc := R dst1' } e4
                    if loc_unconstrained (R dst1') e5 &&
                        can_undef (destroyed_by_load Mint32 addr) e5 &&
                        reg_unconstrained dst e5 then
                      match add_equations args args1' e5 with
                      | none => none
                      | some e6 => track_moves env mv1 e6
                    else none
          else none
  | BSload2_1 addr args dst mv1 args' dst' mv2 _ =>
      match track_moves env mv2 e with
      | none => none
      | some e1 =>
          let e2 := remove_equation { ekind := kind_first_word, ereg := dst, eloc := R dst' } e1
          if reg_loc_unconstrained dst (R dst') e2 &&
              can_undef (destroyed_by_load Mint32 addr) e2 then
            match add_equations args args' e2 with
            | none => none
            | some e3 => track_moves env mv1 e3
          else none
  | BSload2_2 addr addr' args dst mv1 args' dst' mv2 _ =>
      match track_moves env mv2 e with
      | none => none
      | some e1 =>
          let e2 := remove_equation { ekind := kind_second_word, ereg := dst, eloc := R dst' } e1
          if reg_loc_unconstrained dst (R dst') e2 &&
              can_undef (destroyed_by_load Mint32 addr') e2 then
            match add_equations args args' e2 with
            | none => none
            | some e3 => track_moves env mv1 e3
          else none
  | BSloaddead _ _ _ dst mv _ =>
      if reg_unconstrained dst e then track_moves env mv e else none
  | BSstore chunk addr args src mv args' src' _ =>
      if can_undef (destroyed_by_store chunk addr) e then
        match add_equations (src :: args) (src' :: args') e with
        | none => none
        | some e1 => track_moves env mv e1
      else none
  | BSstore2 addr addr' args src mv1 args1' src1' mv2 args2' src2' _ =>
      if can_undef (destroyed_by_store Mint32 addr') e then
        match add_equations args args2'
            (add_equation { ekind := kind_second_word, ereg := src, eloc := R src2' } e) with
        | none => none
        | some e1 =>
            match track_moves env mv2 e1 with
            | none => none
            | some e2 =>
                if can_undef (destroyed_by_store Mint32 addr) e2 then
                  match add_equations args args1'
                      (add_equation { ekind := kind_first_word, ereg := src, eloc := R src1' } e2) with
                  | none => none
                  | some e3 => track_moves env mv1 e3
                else none
      else none
  | BScall sg ros args res mv1 ros' mv2 _ =>
      let args' := CompCert4Lean.X86.Conventions1.loc_arguments cfg sg
      let res' := CompCert4Lean.X86.Conventions1.loc_result sg
      match track_moves env mv2 e with
      | none => none
      | some e1 =>
          match removeEquationsRes res res' e1 with
          | none => none
          | some e2 =>
              let resultRegs := regs_of_rpair res'
              let resultOk := resultRegs.all (fun l => reg_loc_unconstrained res (R l) e2)
              if resultOk && no_caller_saves cfg e2 then
                match add_equation_ros ros ros' e2 with
                | none => none
                | some e3 =>
                    match addEquationsArgs args (proj_sig_args sg) args' e3 with
                    | none => none
                    | some e4 => track_moves env mv1 e4
              else none
  | BStailcall sg ros args mv1 ros' =>
      let args' := CompCert4Lean.X86.Conventions1.loc_arguments cfg sg
      if CompCert4Lean.Backend.Conventions.tailcall_is_possible cfg sg &&
          decide (sg.sig_res = f.fn_sig.sig_res) &&
          ros_compatible_tailcall cfg ros' then
        match add_equation_ros ros ros' empty_eqs with
        | none => none
        | some e1 =>
            match addEquationsArgs args (proj_sig_args sg) args' e1 with
            | none => none
            | some e2 => track_moves env mv1 e2
      else none
  | BSbuiltin ef args res mv1 args' res' mv2 _ =>
      match track_moves env mv2 e with
      | none => none
      | some e1 =>
          match remove_equations_builtin_res env res res' e1 with
          | none => none
          | some e2 =>
              let regsOk := (params_of_builtin_res res).all (fun r => reg_unconstrained r e2)
              let locsOk := (params_of_builtin_res res').all
                (fun mr => loc_unconstrained (R mr) e2)
              if regsOk && locsOk && can_undef (destroyed_by_builtin ef) e2 then
                match ef with
                | EF_debug _ _ _ =>
                    match add_equations_debug_args env args args' e2 with
                    | none => none
                    | some e3 => track_moves env mv1 e3
                | _ =>
                    match add_equations_builtin_args env args args' e2 with
                    | none => none
                    | some e3 => track_moves env mv1 e3
              else none
  | BScond cond args mv args' _ _ =>
      if can_undef (destroyed_by_cond cond) e then
        match add_equations args args' e with
        | none => none
        | some e1 => track_moves env mv e1
      else none
  | BSjumptable arg mv arg' _ =>
      if can_undef destroyed_by_jumptable e then
        track_moves env mv (add_equation { ekind := Full, ereg := arg, eloc := R arg' } e)
      else none
  | BSreturn none mv => track_moves env mv empty_eqs
  | BSreturn (some arg) mv =>
      match addEquationsRes arg (proj_sig_res f.fn_sig)
          (CompCert4Lean.X86.Conventions1.loc_result f.fn_sig) empty_eqs with
      | none => none
      | some e1 => track_moves env mv e1

def transfer (cfg : CompilerConfig) (f : RTL.function) (env : regenv)
    (shapes : PTree.t block_shape) (pc : RTL.node) (after : res eqs) : res eqs :=
  match after with
  | Error _ => after
  | OK e =>
      match PTree.get pc shapes with
      | none => Error (MSG atPcText :: POS pc :: MSG unmatchedBlockText :: [])
      | some shape =>
          match transfer_aux cfg f env shape e with
          | none => Error (MSG atPcText :: POS pc :: MSG invalidAllocationText :: [])
          | some e' => OK e'

private def analysisEq (x y : res eqs) : Prop :=
  match x, y with
  | OK a, OK b => EqSet.Equal a b
  | Error _, Error _ => True
  | _, _ => False

private def analysisGe (x y : res eqs) : Prop :=
  match x, y with
  | OK a, OK b => EqSet.Subset b a
  | Error _, _ => True
  | _, Error _ => False

private def analysisBeq (x y : res eqs) : Bool :=
  match x, y with
  | OK a, OK b => EqSet.equal a b
  | Error _, Error _ => true
  | _, _ => false

private def analysisLub (x y : res eqs) : res eqs :=
  match x, y with
  | OK a, OK b => OK (EqSet.union a b)
  | OK _, Error m => Error m
  | Error m, _ => Error m

private def analysisLattice : SemiLattice where
  t := res eqs
  bot := OK empty_eqs
  lub := analysisLub
  beq := analysisBeq
  eq := analysisEq
  ge := analysisGe

/-! Generated surface for `Backward_Dataflow_Solver(LEq)(NodeSetBackward)`. -/
namespace DS

def L : SemiLattice := analysisLattice

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

def successors_block_shape (bsh : block_shape) : List RTL.node :=
  match bsh with
  | BSnop _ s | BSmove _ _ _ s | BSmakelong _ _ _ _ s
  | BSlowlong _ _ _ s | BShighlong _ _ _ s | BSop _ _ _ _ _ _ _ s
  | BSopdead _ _ _ _ s | BSload _ _ _ _ _ _ _ _ s
  | BSload2 _ _ _ _ _ _ _ _ _ _ _ s | BSload2_1 _ _ _ _ _ _ _ s
  | BSload2_2 _ _ _ _ _ _ _ _ s | BSloaddead _ _ _ _ _ s
  | BSstore _ _ _ _ _ _ _ s | BSstore2 _ _ _ _ _ _ _ _ _ _ s
  | BScall _ _ _ _ _ _ _ s | BSbuiltin _ _ _ _ _ _ _ s => [s]
  | BStailcall _ _ _ _ _ => []
  | BScond _ _ _ _ s1 s2 => [s1, s2]
  | BSjumptable _ _ _ tbl => tbl
  | BSreturn _ _ => []

def analyze (cfg : CompilerConfig) (f : RTL.function) (env : regenv)
    (bsh : PTree.t block_shape) : Option (PMap.t (res eqs)) :=
  Backward_Dataflow_Solver.fixpoint_allnodes analysisLattice NodeSetBackward
    bsh successors_block_shape (transfer cfg f env bsh)

private def compatEntry : List reg → List (rpair loc) → eqs → Bool
  | [], [], _ => true
  | r :: rs, .One l :: ls, e => compat_left r l e && compatEntry rs ls e
  | r :: rs, .Twolong hi lo :: ls, e =>
      compat_left2 r hi lo e && compatEntry rs ls e
  | _, _, _ => false

def check_entrypoints_aux (cfg : CompilerConfig) (rtl : RTL.function)
    (ltl : LTL.function) (env : regenv) (e1 : eqs) : Option Unit :=
  match pair_entrypoints rtl ltl with
  | none => none
  | some mv =>
      match track_moves env mv e1 with
      | none => none
      | some e2 =>
          if compatEntry rtl.fn_params
                (CompCert4Lean.Backend.Conventions.loc_parameters cfg rtl.fn_sig) e2 &&
              can_undef destroyed_at_function_entry e2 &&
              boolOfSumbool (zeq rtl.fn_stacksize ltl.fn_stacksize) &&
              boolOfSumbool (signature_eq rtl.fn_sig ltl.fn_sig) then
            some ()
          else none

def check_entrypoints (cfg : CompilerConfig) (rtl : RTL.function)
    (ltl : LTL.function) (env : regenv) (bsh : PTree.t block_shape)
    (a : PMap.t (res eqs)) : res Unit :=
  match transfer cfg rtl env bsh rtl.fn_entrypoint (PMap.get rtl.fn_entrypoint a) with
  | Error m => Error m
  | OK e1 =>
      match check_entrypoints_aux cfg rtl ltl env e1 with
      | none => Error (msg invalidAllocationAtEntryText)
      | some _ => OK ()

def check_function (cfg : CompilerConfig) (rtl : RTL.function)
    (ltl : LTL.function) (env : regenv) : res Unit :=
  let bsh := pair_codes rtl ltl
  match analyze cfg rtl env bsh with
  | none => Error (msg allocationAnalysisDivergesText)
  | some a => check_entrypoints cfg rtl ltl env bsh a

abbrev RegallocOracle := RTL.function → res LTL.function

def regalloc (oracle : RegallocOracle) (f : RTL.function) : res LTL.function :=
  oracle f

def transf_function (cfg : CompilerConfig) (oracle : RegallocOracle)
    (f : RTL.function) : res LTL.function :=
  match CompCert4Lean.Backend.RTLtyping.type_function cfg f with
  | Error m => Error m
  | OK env =>
      match regalloc oracle f with
      | Error m => Error m
      | OK tf =>
          match check_function cfg f tf env with
          | Error m => Error m
          | OK _ => OK tf

def transf_fundef (cfg : CompilerConfig) (oracle : RegallocOracle)
    (fd : RTL.fundef) : res LTL.fundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef (transf_function cfg oracle) fd

def transf_program (cfg : CompilerConfig) (oracle : RegallocOracle)
    (p : RTL.program) : res LTL.program :=
  CompCert4Lean.Common.AST.transform_partial_program
    (transf_fundef cfg oracle) p
