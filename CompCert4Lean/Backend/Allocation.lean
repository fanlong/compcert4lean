import CompCert4Lean.Foundation.Logic
import CompCert4Lean.Foundation.Numbers
import CompCert4Lean.Foundation.Ordered
import CompCert4Lean.Foundation.RocqString
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

def index : t → positive
  | .Full => PArith.BinPos.Pos.of_nat 1
  | .Low => PArith.BinPos.Pos.of_nat 2
  | .High => PArith.BinPos.Pos.of_nat 3

theorem index_inj (x y : t) : index x = index y → x = y := by
  cases x <;> cases y <;> decide

def eq (x y : t) : Sumbool (x = y) (x ≠ y) := by
  exact match (inferInstance : Decidable (x = y)) with
    | .isTrue h => .left h
    | .isFalse h => .right h

end IndexedEqKind

namespace OrderedEqKind

abbrev t := equation_kind
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop := Plt (IndexedEqKind.index x) (IndexedEqKind.index y)

theorem eq_refl (x : t) : eq x x := rfl

theorem eq_sym (x y : t) : eq x y → eq y x := Eq.symm

theorem eq_trans (x y z : t) : eq x y → eq y z → eq x z := Eq.trans

theorem lt_trans (x y z : t) : lt x y → lt y z → lt x z := Nat.lt_trans

theorem lt_not_eq (x y : t) (hlt : lt x y) : ¬ eq x y := by
  intro hxy
  subst y
  exact Nat.lt_irrefl _ hlt

def compare (x y : t) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y := by
  cases x <;> cases y
  · exact .EQ rfl
  · exact .LT (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .LT (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .GT (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .EQ rfl
  · exact .LT (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .GT (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .GT (by
      unfold lt IndexedEqKind.index CompCert4Lean.Lib.Coqlib.Plt
        PArith.BinPos.Pos.lt
      decide)
  · exact .EQ rfl

def eq_dec := IndexedEqKind.eq

def OrderedEqKind :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType where
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

end OrderedEqKind

private theorem positiveLtTrans {x y z : positive} :
    Plt x y → Plt y z → Plt x z :=
  Nat.lt_trans

private theorem positiveLtIrrefl (x : positive) : ¬ Plt x x :=
  Nat.lt_irrefl _

private def comparePositive (x y : positive) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      Plt (fun a b => a = b) x y := by
  cases plt x y with
  | left hlt => exact .LT hlt
  | right hlt =>
      cases peq x y with
      | left heq => exact .EQ heq
      | right heq =>
          refine .GT ?_
          change PArith.BinPos.Pos.to_nat y < PArith.BinPos.Pos.to_nat x
          change ¬ PArith.BinPos.Pos.to_nat x < PArith.BinPos.Pos.to_nat y at hlt
          have hnatne :
              PArith.BinPos.Pos.to_nat x ≠ PArith.BinPos.Pos.to_nat y := by
            intro h
            exact heq (posToNat_injective h)
          omega

private theorem orderedSlotLtTrans (x y z : slot) :
    Locations.OrderedSlot.lt x y → Locations.OrderedSlot.lt y z →
      Locations.OrderedSlot.lt x z := by
  cases x <;> cases y <;> cases z <;>
    simp_all [Locations.OrderedSlot.lt, Plt, PArith.BinPos.Pos.lt] <;> omega

private theorem orderedSlotLtIrrefl (x : slot) :
    ¬ Locations.OrderedSlot.lt x x := by
  cases x <;> simp [Locations.OrderedSlot.lt, Plt, PArith.BinPos.Pos.lt]

private theorem orderedTypLtTrans (x y z : typ) :
    Locations.OrderedTyp.lt x y → Locations.OrderedTyp.lt y z →
      Locations.OrderedTyp.lt x z := by
  cases x <;> cases y <;> cases z <;>
    simp_all [Locations.OrderedTyp.lt, Plt, PArith.BinPos.Pos.lt] <;> omega

private theorem orderedTypLtIrrefl (x : typ) :
    ¬ Locations.OrderedTyp.lt x x := by
  cases x <;> simp [Locations.OrderedTyp.lt, Plt, PArith.BinPos.Pos.lt]

private theorem orderedLocLtTrans (x y z : loc) :
    Locations.OrderedLoc.lt x y → Locations.OrderedLoc.lt y z →
      Locations.OrderedLoc.lt x z := by
  intro hxy hyz
  cases x with
  | R rx =>
      cases y with
      | R ry =>
          cases z with
          | R rz => exact positiveLtTrans hxy hyz
          | S _ _ _ => trivial
      | S _ _ _ =>
          cases z with
          | R _ => contradiction
          | S _ _ _ => trivial
  | S sx ox tx =>
      cases y with
      | R _ => contradiction
      | S sy oy ty =>
          cases z with
          | R _ => contradiction
          | S sz oz tz =>
              rcases hxy with hsxy | ⟨hesxy, hoxy | ⟨heoxy, htxy⟩⟩
              · rcases hyz with hsyz | ⟨hesyz, _⟩
                · exact Or.inl (orderedSlotLtTrans _ _ _ hsxy hsyz)
                · exact Or.inl (by simpa [hesyz] using hsxy)
              · rcases hyz with hsyz | ⟨hesyz, hosyz | ⟨heoyz, _⟩⟩
                · exact Or.inl (by simpa [hesxy] using hsyz)
                · exact Or.inr ⟨hesxy.trans hesyz, Or.inl (Int.lt_trans hoxy hosyz)⟩
                · exact Or.inr ⟨hesxy.trans hesyz, Or.inl (by
                    simpa [heoyz] using hoxy)⟩
              · rcases hyz with hsyz | ⟨hesyz, hosyz | ⟨heoyz, htyz⟩⟩
                · exact Or.inl (by simpa [hesxy] using hsyz)
                · exact Or.inr ⟨hesxy.trans hesyz, Or.inl (by
                    simpa [heoxy] using hosyz)⟩
                · exact Or.inr ⟨hesxy.trans hesyz, Or.inr
                    ⟨heoxy.trans heoyz, orderedTypLtTrans _ _ _ htxy htyz⟩⟩

private theorem orderedLocLtIrrefl (x : loc) :
    ¬ Locations.OrderedLoc.lt x x := by
  intro h
  cases x with
  | R r =>
      exact positiveLtIrrefl
        (CompCert4Lean.X86.Machregs.IndexedMreg.index r) h
  | S s o t =>
      rcases h with hs | ⟨_, ho | ⟨_, ht⟩⟩
      · exact orderedSlotLtIrrefl s hs
      · exact Int.lt_irrefl _ ho
      · exact orderedTypLtIrrefl t ht

namespace OrderedEquation

abbrev t := equation
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop :=
  Plt x.ereg y.ereg ∨
    (x.ereg = y.ereg ∧
      (Locations.OrderedLoc.lt x.eloc y.eloc ∨
        (x.eloc = y.eloc ∧ OrderedEqKind.lt x.ekind y.ekind)))

theorem eq_refl (x : t) : eq x x := rfl

theorem eq_sym (x y : t) : eq x y → eq y x := Eq.symm

theorem eq_trans (x y z : t) : eq x y → eq y z → eq x z := Eq.trans

theorem lt_trans (x y z : t) (hxy : lt x y) (hyz : lt y z) : lt x z := by
  rcases hxy with hrxy | ⟨herxy, hlxy | ⟨helxy, hkxy⟩⟩
  · rcases hyz with hryz | ⟨heryz, _⟩
    · exact Or.inl (positiveLtTrans hrxy hryz)
    · exact Or.inl (by simpa [heryz] using hrxy)
  · rcases hyz with hryz | ⟨heryz, hlryz | ⟨helryz, _⟩⟩
    · exact Or.inl (by simpa [herxy] using hryz)
    · exact Or.inr ⟨herxy.trans heryz,
        Or.inl (orderedLocLtTrans _ _ _ hlxy hlryz)⟩
    · exact Or.inr ⟨herxy.trans heryz, Or.inl (by
        simpa [helryz] using hlxy)⟩
  · rcases hyz with hryz | ⟨heryz, hlryz | ⟨helryz, hkryz⟩⟩
    · exact Or.inl (by simpa [herxy] using hryz)
    · exact Or.inr ⟨herxy.trans heryz, Or.inl (by
        simpa [helxy] using hlryz)⟩
    · exact Or.inr ⟨herxy.trans heryz, Or.inr
        ⟨helxy.trans helryz, OrderedEqKind.lt_trans _ _ _ hkxy hkryz⟩⟩

theorem lt_not_eq (x y : t) (hlt : lt x y) : ¬ eq x y := by
  intro hxy
  subst y
  rcases hlt with hr | ⟨_, hl | ⟨_, hk⟩⟩
  · exact positiveLtIrrefl x.ereg hr
  · exact orderedLocLtIrrefl x.eloc hl
  · exact OrderedEqKind.lt_not_eq _ _ hk rfl

def compare (x y : t) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y := by
  cases comparePositive x.ereg y.ereg with
  | LT hr => exact .LT (Or.inl hr)
  | GT hr => exact .GT (Or.inl hr)
  | EQ her =>
      cases Locations.OrderedLoc.compare x.eloc y.eloc with
      | LT hl => exact .LT (Or.inr ⟨her, Or.inl hl⟩)
      | GT hl => exact .GT (Or.inr ⟨her.symm, Or.inl hl⟩)
      | EQ hel =>
          cases OrderedEqKind.compare x.ekind y.ekind with
          | LT hk => exact .LT (Or.inr ⟨her, Or.inr ⟨hel, hk⟩⟩)
          | GT hk => exact .GT (Or.inr ⟨her.symm, Or.inr ⟨hel.symm, hk⟩⟩)
          | EQ hek =>
              cases x
              cases y
              subst_vars
              exact .EQ rfl

def eq_dec (x y : t) : Sumbool (x = y) (x ≠ y) := by
  exact match (inferInstance : Decidable (x = y)) with
    | .isTrue h => .left h
    | .isFalse h => .right h

def OrderedEquation :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType where
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

end OrderedEquation

namespace «OrderedEquation'»

abbrev t := equation
def eq (x y : t) : Prop := x = y
def lt (x y : t) : Prop :=
  Locations.OrderedLoc.lt x.eloc y.eloc ∨
    (x.eloc = y.eloc ∧
      (Plt x.ereg y.ereg ∨
        (x.ereg = y.ereg ∧ OrderedEqKind.lt x.ekind y.ekind)))

theorem eq_refl (x : t) : eq x x := rfl

theorem eq_sym (x y : t) : eq x y → eq y x := Eq.symm

theorem eq_trans (x y z : t) : eq x y → eq y z → eq x z := Eq.trans

theorem lt_trans (x y z : t) (hxy : lt x y) (hyz : lt y z) : lt x z := by
  rcases hxy with hlxy | ⟨helxy, hrxy | ⟨herxy, hkxy⟩⟩
  · rcases hyz with hlryz | ⟨helryz, _⟩
    · exact Or.inl (orderedLocLtTrans _ _ _ hlxy hlryz)
    · exact Or.inl (by simpa [helryz] using hlxy)
  · rcases hyz with hlryz | ⟨helryz, hryz | ⟨heryz, _⟩⟩
    · exact Or.inl (by simpa [helxy] using hlryz)
    · exact Or.inr ⟨helxy.trans helryz,
        Or.inl (positiveLtTrans hrxy hryz)⟩
    · exact Or.inr ⟨helxy.trans helryz, Or.inl (by
        simpa [heryz] using hrxy)⟩
  · rcases hyz with hlryz | ⟨helryz, hryz | ⟨heryz, hkryz⟩⟩
    · exact Or.inl (by simpa [helxy] using hlryz)
    · exact Or.inr ⟨helxy.trans helryz, Or.inl (by
        simpa [herxy] using hryz)⟩
    · exact Or.inr ⟨helxy.trans helryz, Or.inr
        ⟨herxy.trans heryz, OrderedEqKind.lt_trans _ _ _ hkxy hkryz⟩⟩

theorem lt_not_eq (x y : t) (hlt : lt x y) : ¬ eq x y := by
  intro hxy
  subst y
  rcases hlt with hl | ⟨_, hr | ⟨_, hk⟩⟩
  · exact orderedLocLtIrrefl x.eloc hl
  · exact positiveLtIrrefl x.ereg hr
  · exact OrderedEqKind.lt_not_eq _ _ hk rfl

def compare (x y : t) :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.Compare
      lt eq x y := by
  cases Locations.OrderedLoc.compare x.eloc y.eloc with
  | LT hl => exact .LT (Or.inl hl)
  | GT hl => exact .GT (Or.inl hl)
  | EQ hel =>
      cases comparePositive x.ereg y.ereg with
      | LT hr => exact .LT (Or.inr ⟨hel, Or.inl hr⟩)
      | GT hr => exact .GT (Or.inr ⟨hel.symm, Or.inl hr⟩)
      | EQ her =>
          cases OrderedEqKind.compare x.ekind y.ekind with
          | LT hk => exact .LT (Or.inr ⟨hel, Or.inr ⟨her, hk⟩⟩)
          | GT hk => exact .GT (Or.inr ⟨hel.symm, Or.inr ⟨her.symm, hk⟩⟩)
          | EQ hek =>
              cases x
              cases y
              subst_vars
              exact .EQ rfl

def eq_dec := OrderedEquation.eq_dec

def OrderedEquation' :
    CompCert4Lean.Foundation.Ordered.Rocq.Coq.Structures.OrderedType.OrderedType where
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

end «OrderedEquation'»

/-! ## The two source `FSetAVLplus.Make` applications -/

open CompCert4Lean.Lib.FSetAVLplus

namespace EqSet

abbrev E := OrderedEquation.OrderedEquation
abbrev «X'» := E
abbrev MSet := Make.MSet E
abbrev Raw : Type := Make.Raw.tree E
abbrev EqSet : Type := Make.t E
abbrev t := Make.t E
abbrev elt := Make.elt E

namespace MSet

abbrev Mkt := @Make.MSet.Mkt E
abbrev this := @Make.MSet.this E
abbrev is_ok := @Make.MSet.is_ok E

end MSet

namespace Raw

abbrev tree := Make.Raw.tree E
abbrev t := tree
abbrev IsOk (s : tree) : Prop := Make.Raw.IsOk s
abbrev Ok (s : tree) : Prop := Make.Raw.Ok s
abbrev Leaf : tree := Make.Raw.Leaf
abbrev Node := @Make.Raw.Node E
abbrev empty : tree := Make.Raw.empty
abbrev singleton := @Make.Raw.singleton E
export CompCert4Lean.Lib.FSetAVLplus.Make.Raw
  (is_empty mem min_elt max_elt choose fold elements_aux elements
   rev_elements_aux rev_elements cardinal maxdepth mindepth for_all exists_
   compare equal subset subsetl subsetr ltb_tree gtb_tree isok In InT IsRoot
   InLeft InRight Equal Subset Empty For_all Exists lt_tree gt_tree bst InA
   NoDupA Sorted RespectsEq enumeration End More cons compare_more compare_cont
   compare_end flatten_e eq lt CompSpec CompareSpec CompEq CompLt CompGt Cmp
   height create assert_false bal add join remove_min merge remove concat triple
   split inter diff union filter partition singleton_spec create_spec create_bst
   singleton_bst bal_spec bal_bst add_spec add_bst join_spec join_bst
   remove_min_spec remove_min_bst_gt remove_min_bst remove_min_ok
   remove_min_gt_tree merge_spec merge_bst concat_spec concat_bst remove_spec
   remove_bst split_left_spec split_right_spec split_in_spec split_bst
   split_membership_spec union_spec union_bst inter_spec_bst inter_spec inter_bst
   diff_spec_bst diff_spec diff_bst filter_weak_spec filter_spec filter_bst
   partition_fst partition_snd partition_bst ltb_tree_iff gtb_tree_iff isok_iff
   In_1 In_node_iff In_leaf_iff lt_leaf gt_leaf lt_tree_node gt_tree_node
   lt_tree_not_in gt_tree_not_in lt_tree_trans gt_tree_trans empty_spec empty_ok
   is_empty_spec mem_spec min_elt_spec1 min_elt_spec2 min_elt_spec3
   max_elt_spec1 max_elt_spec2 max_elt_spec3 choose_spec1 choose_spec2
   choose_spec3 elements_spec1' elements_spec1 elements_spec2' elements_spec2
   elements_spec2w elements_aux_cardinal elements_cardinal cardinal_spec
   elements_app elements_node rev_elements_app rev_elements_node rev_elements_rev
   sorted_app_inv elements_sort_ok for_all_spec exists_spec fold_spec' fold_spec
   subsetl_spec subsetr_spec subset_spec eq_Leq eq_equiv lt_strorder lt_compat
   flatten_e_elements cons_1 compare_end_Cmp compare_more_Cmp compare_cont_Cmp
   compare_Cmp compare_spec equal_spec mindepth_maxdepth maxdepth_cardinal
   mindepth_cardinal maxdepth_log_cardinal mindepth_log_cardinal join_ok
   concat_ok)

end Raw

abbrev In := @Make.In E
abbrev Equal := @Make.Equal E
abbrev Subset := @Make.Subset E
abbrev Empty := @Make.Empty E
abbrev For_all := @Make.For_all E
abbrev Exists := @Make.Exists E
abbrev eq := @Make.eq E
abbrev lt := @Make.lt E
abbrev empty : t := Make.empty
abbrev is_empty := @Make.is_empty E
abbrev mem := @Make.mem E
abbrev add := @Make.add E
abbrev singleton := @Make.singleton E
abbrev remove := @Make.remove E
abbrev union := @Make.union E
abbrev inter := @Make.inter E
abbrev diff := @Make.diff E
abbrev equal := @Make.equal E
abbrev subset := @Make.subset E
abbrev fold := @Make.fold E
abbrev for_all := @Make.for_all E
abbrev exists_ := @Make.exists_ E
abbrev filter := @Make.filter E
abbrev partition := @Make.partition E
abbrev cardinal := @Make.cardinal E
abbrev elements := @Make.elements E
abbrev choose := @Make.choose E
abbrev min_elt := @Make.min_elt E
abbrev max_elt := @Make.max_elt E
abbrev eq_dec := @Make.eq_dec E
abbrev compare := @Make.compare E
abbrev In_1 := @Make.In_1 E
abbrev eq_refl := @Make.eq_refl E
abbrev eq_sym := @Make.eq_sym E
abbrev eq_trans := @Make.eq_trans E
abbrev mem_1 := @Make.mem_1 E
abbrev mem_2 := @Make.mem_2 E
abbrev equal_1 := @Make.equal_1 E
abbrev equal_2 := @Make.equal_2 E
abbrev subset_1 := @Make.subset_1 E
abbrev subset_2 := @Make.subset_2 E
abbrev empty_1 := @Make.empty_1 E
abbrev is_empty_1 := @Make.is_empty_1 E
abbrev is_empty_2 := @Make.is_empty_2 E
abbrev add_1 := @Make.add_1 E
abbrev add_2 := @Make.add_2 E
abbrev add_3 := @Make.add_3 E
abbrev remove_1 := @Make.remove_1 E
abbrev remove_2 := @Make.remove_2 E
abbrev remove_3 := @Make.remove_3 E
abbrev singleton_1 := @Make.singleton_1 E
abbrev singleton_2 := @Make.singleton_2 E
abbrev union_1 := @Make.union_1 E
abbrev union_2 := @Make.union_2 E
abbrev union_3 := @Make.union_3 E
abbrev inter_1 := @Make.inter_1 E
abbrev inter_2 := @Make.inter_2 E
abbrev inter_3 := @Make.inter_3 E
abbrev diff_1 := @Make.diff_1 E
abbrev diff_2 := @Make.diff_2 E
abbrev diff_3 := @Make.diff_3 E
abbrev fold_1 := @Make.fold_1 E
abbrev cardinal_1 := @Make.cardinal_1 E
abbrev filter_1 := @Make.filter_1 E
abbrev filter_2 := @Make.filter_2 E
abbrev filter_3 := @Make.filter_3 E
abbrev for_all_1 := @Make.for_all_1 E
abbrev for_all_2 := @Make.for_all_2 E
abbrev exists_1 := @Make.exists_1 E
abbrev exists_2 := @Make.exists_2 E
abbrev partition_1 := @Make.partition_1 E
abbrev partition_2 := @Make.partition_2 E
abbrev elements_1 := @Make.elements_1 E
abbrev elements_2 := @Make.elements_2 E
abbrev elements_3w := @Make.elements_3w E
abbrev choose_1 := @Make.choose_1 E
abbrev choose_2 := @Make.choose_2 E
abbrev lt_trans := @Make.lt_trans E
abbrev lt_not_eq := @Make.lt_not_eq E
abbrev elements_3 := @Make.elements_3 E
abbrev min_elt_1 := @Make.min_elt_1 E
abbrev min_elt_2 := @Make.min_elt_2 E
abbrev min_elt_3 := @Make.min_elt_3 E
abbrev max_elt_1 := @Make.max_elt_1 E
abbrev max_elt_2 := @Make.max_elt_2 E
abbrev max_elt_3 := @Make.max_elt_3 E
abbrev choose_3 := @Make.choose_3 E
abbrev MF := Make.MF E
private abbrev AboveMonotone := @Make.AboveMonotone E
private abbrev BelowMonotone := @Make.BelowMonotone E
private abbrev PredCompat := @Make.PredCompat E
abbrev raw_mem_between := @Make.raw_mem_between E
abbrev mem_between := @Make.mem_between E
abbrev raw_elements_between := @Make.raw_elements_between E
abbrev elements_between := @Make.elements_between E
abbrev raw_for_all_between := @Make.raw_for_all_between E
abbrev for_all_between := @Make.for_all_between E
abbrev raw_partition_between := @Make.raw_partition_between E
abbrev partition_between := @Make.partition_between E

def raw_mem_between_1 : Prop :=
  ∀ (above below : elt → Bool) (m : Raw.tree),
    raw_mem_between above below m = true →
      ∃ x, Raw.InT x m ∧ above x = true ∧ below x = true

def raw_mem_between_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      above x = true → below x = true → raw_mem_between above below m = true

def mem_between_1 : Prop :=
  ∀ (above below : elt → Bool) (s : t),
    mem_between above below s = true →
      ∃ x, In x s ∧ above x = true ∧ below x = true

def mem_between_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t), In x s → above x = true → below x = true →
      mem_between above below s = true

def In_raw_elements_between_1 : Prop :=
  ∀ (above below : elt → Bool) (x : elt) (m : Raw.tree),
    Raw.InT x (raw_elements_between above below m) → Raw.InT x m

def raw_elements_between_ok : Prop :=
  ∀ (above below : elt → Bool) (m : Raw.tree),
    Raw.bst m → Raw.bst (raw_elements_between above below m)

def In_raw_elements_between_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree),
      Raw.InT x (raw_elements_between above below m) →
        above x = true ∧ below x = true

def In_raw_elements_between_3 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      above x = true → below x = true →
        Raw.InT x (raw_elements_between above below m)

def elements_between_iff : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t),
      In x (elements_between above below s) ↔
        In x s ∧ above x = true ∧ below x = true

def raw_for_all_between_1 : Prop :=
  ∀ (pred above below : elt → Bool),
    PredCompat pred → AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m →
      raw_for_all_between pred above below m = true → Raw.InT x m →
      above x = true → below x = true → pred x = true

def raw_for_all_between_2 : Prop :=
  ∀ (pred above below : elt → Bool) (m : Raw.tree), Raw.bst m →
    (∀ x, Raw.InT x m → above x = true → below x = true → pred x = true) →
      raw_for_all_between pred above below m = true

def for_all_between_iff : Prop :=
  ∀ (pred above below : elt → Bool),
    PredCompat pred → AboveMonotone above → BelowMonotone below →
    ∀ s : t, for_all_between pred above below s = true ↔
      ∀ x, In x s → above x = true → below x = true → pred x = true

def In_raw_partition_between_1 : Prop :=
  ∀ (above below : elt → Bool) (x : elt) (m : Raw.tree),
    Raw.InT x (raw_partition_between above below m).1 → Raw.InT x m

def In_raw_partition_between_2 : Prop :=
  ∀ (above below : elt → Bool) (x : elt) (m : Raw.tree),
    Raw.InT x (raw_partition_between above below m).2 → Raw.InT x m

def raw_partition_between_ok : Prop :=
  ∀ (above below : elt → Bool) (m : Raw.tree), Raw.bst m →
    Raw.bst (raw_partition_between above below m).1 ∧
      Raw.bst (raw_partition_between above below m).2

def In_raw_partition_between_3 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree),
      Raw.InT x (raw_partition_between above below m).1 →
        above x = true ∧ below x = true

def In_raw_partition_between_4 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m →
      Raw.InT x (raw_partition_between above below m).2 →
        above x = false ∨ below x = false

def In_raw_partition_between_5 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      above x = true → below x = true →
        Raw.InT x (raw_partition_between above below m).1

def In_raw_partition_between_6 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      (above x = false ∨ below x = false) →
        Raw.InT x (raw_partition_between above below m).2

def partition_between_iff_1 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t),
      In x (partition_between above below s).1 ↔
        In x s ∧ above x = true ∧ below x = true

def partition_between_iff_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t),
      In x (partition_between above below s).2 ↔
        In x s ∧ (above x = false ∨ below x = false)

end EqSet

namespace EqSet2

abbrev E := OrderedEquation'.OrderedEquation'
abbrev «X'» := E
abbrev MSet := Make.MSet E
abbrev Raw : Type := Make.Raw.tree E
abbrev EqSet2 : Type := Make.t E
abbrev t := Make.t E
abbrev elt := Make.elt E

namespace MSet

abbrev Mkt := @Make.MSet.Mkt E
abbrev this := @Make.MSet.this E
abbrev is_ok := @Make.MSet.is_ok E

end MSet

namespace Raw

abbrev tree := Make.Raw.tree E
abbrev t := tree
abbrev IsOk (s : tree) : Prop := Make.Raw.IsOk s
abbrev Ok (s : tree) : Prop := Make.Raw.Ok s
abbrev Leaf : tree := Make.Raw.Leaf
abbrev Node := @Make.Raw.Node E
abbrev empty : tree := Make.Raw.empty
abbrev singleton := @Make.Raw.singleton E
export CompCert4Lean.Lib.FSetAVLplus.Make.Raw
  (is_empty mem min_elt max_elt choose fold elements_aux elements
   rev_elements_aux rev_elements cardinal maxdepth mindepth for_all exists_
   compare equal subset subsetl subsetr ltb_tree gtb_tree isok In InT IsRoot
   InLeft InRight Equal Subset Empty For_all Exists lt_tree gt_tree bst InA
   NoDupA Sorted RespectsEq enumeration End More cons compare_more compare_cont
   compare_end flatten_e eq lt CompSpec CompareSpec CompEq CompLt CompGt Cmp
   height create assert_false bal add join remove_min merge remove concat triple
   split inter diff union filter partition singleton_spec create_spec create_bst
   singleton_bst bal_spec bal_bst add_spec add_bst join_spec join_bst
   remove_min_spec remove_min_bst_gt remove_min_bst remove_min_ok
   remove_min_gt_tree merge_spec merge_bst concat_spec concat_bst remove_spec
   remove_bst split_left_spec split_right_spec split_in_spec split_bst
   split_membership_spec union_spec union_bst inter_spec_bst inter_spec inter_bst
   diff_spec_bst diff_spec diff_bst filter_weak_spec filter_spec filter_bst
   partition_fst partition_snd partition_bst ltb_tree_iff gtb_tree_iff isok_iff
   In_1 In_node_iff In_leaf_iff lt_leaf gt_leaf lt_tree_node gt_tree_node
   lt_tree_not_in gt_tree_not_in lt_tree_trans gt_tree_trans empty_spec empty_ok
   is_empty_spec mem_spec min_elt_spec1 min_elt_spec2 min_elt_spec3
   max_elt_spec1 max_elt_spec2 max_elt_spec3 choose_spec1 choose_spec2
   choose_spec3 elements_spec1' elements_spec1 elements_spec2' elements_spec2
   elements_spec2w elements_aux_cardinal elements_cardinal cardinal_spec
   elements_app elements_node rev_elements_app rev_elements_node rev_elements_rev
   sorted_app_inv elements_sort_ok for_all_spec exists_spec fold_spec' fold_spec
   subsetl_spec subsetr_spec subset_spec eq_Leq eq_equiv lt_strorder lt_compat
   flatten_e_elements cons_1 compare_end_Cmp compare_more_Cmp compare_cont_Cmp
   compare_Cmp compare_spec equal_spec mindepth_maxdepth maxdepth_cardinal
   mindepth_cardinal maxdepth_log_cardinal mindepth_log_cardinal join_ok
   concat_ok)

end Raw

abbrev In := @Make.In E
abbrev Equal := @Make.Equal E
abbrev Subset := @Make.Subset E
abbrev Empty := @Make.Empty E
abbrev For_all := @Make.For_all E
abbrev Exists := @Make.Exists E
abbrev eq := @Make.eq E
abbrev lt := @Make.lt E
abbrev empty : t := Make.empty
abbrev is_empty := @Make.is_empty E
abbrev mem := @Make.mem E
abbrev add := @Make.add E
abbrev singleton := @Make.singleton E
abbrev remove := @Make.remove E
abbrev union := @Make.union E
abbrev inter := @Make.inter E
abbrev diff := @Make.diff E
abbrev equal := @Make.equal E
abbrev subset := @Make.subset E
abbrev fold := @Make.fold E
abbrev for_all := @Make.for_all E
abbrev exists_ := @Make.exists_ E
abbrev filter := @Make.filter E
abbrev partition := @Make.partition E
abbrev cardinal := @Make.cardinal E
abbrev elements := @Make.elements E
abbrev choose := @Make.choose E
abbrev min_elt := @Make.min_elt E
abbrev max_elt := @Make.max_elt E
abbrev eq_dec := @Make.eq_dec E
abbrev compare := @Make.compare E
abbrev In_1 := @Make.In_1 E
abbrev eq_refl := @Make.eq_refl E
abbrev eq_sym := @Make.eq_sym E
abbrev eq_trans := @Make.eq_trans E
abbrev mem_1 := @Make.mem_1 E
abbrev mem_2 := @Make.mem_2 E
abbrev equal_1 := @Make.equal_1 E
abbrev equal_2 := @Make.equal_2 E
abbrev subset_1 := @Make.subset_1 E
abbrev subset_2 := @Make.subset_2 E
abbrev empty_1 := @Make.empty_1 E
abbrev is_empty_1 := @Make.is_empty_1 E
abbrev is_empty_2 := @Make.is_empty_2 E
abbrev add_1 := @Make.add_1 E
abbrev add_2 := @Make.add_2 E
abbrev add_3 := @Make.add_3 E
abbrev remove_1 := @Make.remove_1 E
abbrev remove_2 := @Make.remove_2 E
abbrev remove_3 := @Make.remove_3 E
abbrev singleton_1 := @Make.singleton_1 E
abbrev singleton_2 := @Make.singleton_2 E
abbrev union_1 := @Make.union_1 E
abbrev union_2 := @Make.union_2 E
abbrev union_3 := @Make.union_3 E
abbrev inter_1 := @Make.inter_1 E
abbrev inter_2 := @Make.inter_2 E
abbrev inter_3 := @Make.inter_3 E
abbrev diff_1 := @Make.diff_1 E
abbrev diff_2 := @Make.diff_2 E
abbrev diff_3 := @Make.diff_3 E
abbrev fold_1 := @Make.fold_1 E
abbrev cardinal_1 := @Make.cardinal_1 E
abbrev filter_1 := @Make.filter_1 E
abbrev filter_2 := @Make.filter_2 E
abbrev filter_3 := @Make.filter_3 E
abbrev for_all_1 := @Make.for_all_1 E
abbrev for_all_2 := @Make.for_all_2 E
abbrev exists_1 := @Make.exists_1 E
abbrev exists_2 := @Make.exists_2 E
abbrev partition_1 := @Make.partition_1 E
abbrev partition_2 := @Make.partition_2 E
abbrev elements_1 := @Make.elements_1 E
abbrev elements_2 := @Make.elements_2 E
abbrev elements_3w := @Make.elements_3w E
abbrev choose_1 := @Make.choose_1 E
abbrev choose_2 := @Make.choose_2 E
abbrev lt_trans := @Make.lt_trans E
abbrev lt_not_eq := @Make.lt_not_eq E
abbrev elements_3 := @Make.elements_3 E
abbrev min_elt_1 := @Make.min_elt_1 E
abbrev min_elt_2 := @Make.min_elt_2 E
abbrev min_elt_3 := @Make.min_elt_3 E
abbrev max_elt_1 := @Make.max_elt_1 E
abbrev max_elt_2 := @Make.max_elt_2 E
abbrev max_elt_3 := @Make.max_elt_3 E
abbrev choose_3 := @Make.choose_3 E
abbrev MF := Make.MF E
private abbrev AboveMonotone := @Make.AboveMonotone E
private abbrev BelowMonotone := @Make.BelowMonotone E
private abbrev PredCompat := @Make.PredCompat E
abbrev raw_mem_between := @Make.raw_mem_between E
abbrev mem_between := @Make.mem_between E
abbrev raw_elements_between := @Make.raw_elements_between E
abbrev elements_between := @Make.elements_between E
abbrev raw_for_all_between := @Make.raw_for_all_between E
abbrev for_all_between := @Make.for_all_between E
abbrev raw_partition_between := @Make.raw_partition_between E
abbrev partition_between := @Make.partition_between E

def raw_mem_between_1 : Prop :=
  ∀ (above below : elt → Bool) (m : Raw.tree),
    raw_mem_between above below m = true →
      ∃ x, Raw.InT x m ∧ above x = true ∧ below x = true

def raw_mem_between_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      above x = true → below x = true → raw_mem_between above below m = true

def mem_between_1 : Prop :=
  ∀ (above below : elt → Bool) (s : t),
    mem_between above below s = true →
      ∃ x, In x s ∧ above x = true ∧ below x = true

def mem_between_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t), In x s → above x = true → below x = true →
      mem_between above below s = true

def In_raw_elements_between_1 : Prop :=
  ∀ (above below : elt → Bool) (x : elt) (m : Raw.tree),
    Raw.InT x (raw_elements_between above below m) → Raw.InT x m

def raw_elements_between_ok : Prop :=
  ∀ (above below : elt → Bool) (m : Raw.tree),
    Raw.bst m → Raw.bst (raw_elements_between above below m)

def In_raw_elements_between_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree),
      Raw.InT x (raw_elements_between above below m) →
        above x = true ∧ below x = true

def In_raw_elements_between_3 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      above x = true → below x = true →
        Raw.InT x (raw_elements_between above below m)

def elements_between_iff : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t),
      In x (elements_between above below s) ↔
        In x s ∧ above x = true ∧ below x = true

def raw_for_all_between_1 : Prop :=
  ∀ (pred above below : elt → Bool),
    PredCompat pred → AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m →
      raw_for_all_between pred above below m = true → Raw.InT x m →
      above x = true → below x = true → pred x = true

def raw_for_all_between_2 : Prop :=
  ∀ (pred above below : elt → Bool) (m : Raw.tree), Raw.bst m →
    (∀ x, Raw.InT x m → above x = true → below x = true → pred x = true) →
      raw_for_all_between pred above below m = true

def for_all_between_iff : Prop :=
  ∀ (pred above below : elt → Bool),
    PredCompat pred → AboveMonotone above → BelowMonotone below →
    ∀ s : t, for_all_between pred above below s = true ↔
      ∀ x, In x s → above x = true → below x = true → pred x = true

def In_raw_partition_between_1 : Prop :=
  ∀ (above below : elt → Bool) (x : elt) (m : Raw.tree),
    Raw.InT x (raw_partition_between above below m).1 → Raw.InT x m

def In_raw_partition_between_2 : Prop :=
  ∀ (above below : elt → Bool) (x : elt) (m : Raw.tree),
    Raw.InT x (raw_partition_between above below m).2 → Raw.InT x m

def raw_partition_between_ok : Prop :=
  ∀ (above below : elt → Bool) (m : Raw.tree), Raw.bst m →
    Raw.bst (raw_partition_between above below m).1 ∧
      Raw.bst (raw_partition_between above below m).2

def In_raw_partition_between_3 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree),
      Raw.InT x (raw_partition_between above below m).1 →
        above x = true ∧ below x = true

def In_raw_partition_between_4 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m →
      Raw.InT x (raw_partition_between above below m).2 →
        above x = false ∨ below x = false

def In_raw_partition_between_5 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      above x = true → below x = true →
        Raw.InT x (raw_partition_between above below m).1

def In_raw_partition_between_6 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (m : Raw.tree), Raw.bst m → Raw.InT x m →
      (above x = false ∨ below x = false) →
        Raw.InT x (raw_partition_between above below m).2

def partition_between_iff_1 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t),
      In x (partition_between above below s).1 ↔
        In x s ∧ above x = true ∧ below x = true

def partition_between_iff_2 : Prop :=
  ∀ (above below : elt → Bool),
    AboveMonotone above → BelowMonotone below →
    ∀ (x : elt) (s : t),
      In x (partition_between above below s).2 ↔
        In x s ∧ (above x = false ∨ below x = false)

end EqSet2

structure eqs : Type where
  eqs1 : EqSet.t
  eqs2 : EqSet2.t
  eqs_same : ∀ q, EqSet2.In q eqs2 ↔ EqSet.In q eqs1

abbrev mkeqs := eqs.mk
export eqs (eqs1 eqs2 eqs_same)

instance : Coe eqs EqSet.t := ⟨eqs.eqs1⟩

def empty_eqs : eqs :=
  mkeqs EqSet.empty EqSet2.empty (fun q => by
    constructor
    · exact fun h => False.elim (EqSet2.empty_1 q h)
    · exact fun h => False.elim (EqSet.empty_1 q h))

def add_equation (q : equation) (e : eqs) : eqs :=
  mkeqs (EqSet.add q e.eqs1) (EqSet2.add q e.eqs2) (fun q' => by
    constructor
    · intro h
      cases OrderedEquation'.eq_dec q q' with
      | left heq => exact EqSet.add_1 e.eqs1 q q' heq
      | right hne =>
          exact EqSet.add_2 e.eqs1 q q'
            ((e.eqs_same q').mp (EqSet2.add_3 e.eqs2 q q' hne h))
    · intro h
      cases OrderedEquation.eq_dec q q' with
      | left heq => exact EqSet2.add_1 e.eqs2 q q' heq
      | right hne =>
          exact EqSet2.add_2 e.eqs2 q q'
            ((e.eqs_same q').mpr (EqSet.add_3 e.eqs1 q q' hne h)))

def remove_equation (q : equation) (e : eqs) : eqs :=
  mkeqs (EqSet.remove q e.eqs1) (EqSet2.remove q e.eqs2) (fun q' => by
    constructor
    · intro h
      cases OrderedEquation'.eq_dec q q' with
      | left heq => exact False.elim (EqSet2.remove_1 e.eqs2 q q' heq h)
      | right hne =>
          exact EqSet.remove_2 e.eqs1 q q' hne
            ((e.eqs_same q').mp (EqSet2.remove_3 e.eqs2 q q' h))
    · intro h
      cases OrderedEquation.eq_dec q q' with
      | left heq => exact False.elim (EqSet.remove_1 e.eqs1 q q' heq h)
      | right hne =>
          exact EqSet2.remove_2 e.eqs2 q q' hne
            ((e.eqs_same q').mpr (EqSet.remove_3 e.eqs1 q q' h)))

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
    | .LT _ => false
    | _ => true

def select_loc_h (l : loc) : equation → Bool :=
  let lh := Locations.OrderedLoc.diff_high_bound l
  fun q =>
    match Locations.OrderedLoc.compare q.eloc lh with
    | .GT _ => false
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

def add_equations_args :
    List reg → List typ → List (rpair loc) → eqs → Option eqs
  | [], [], [], e => some e
  | r :: rs, _ty :: tys, .One l :: ls, e =>
      add_equations_args rs tys ls
        (add_equation { ekind := Full, ereg := r, eloc := l } e)
  | r :: rs, Tlong :: tys, .Twolong hi lo :: ls, e =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else add_equations_args rs tys ls
        (add_equation { ekind := Low, ereg := r, eloc := lo }
          (add_equation { ekind := High, ereg := r, eloc := hi } e))
  | _, _, _, _ => none

def add_equations_res (r : reg) (ty : typ) (p : rpair mreg)
    (e : eqs) : Option eqs :=
  match p, ty with
  | .One mr, _ => some (add_equation { ekind := Full, ereg := r, eloc := R mr } e)
  | .Twolong hi lo, Tlong =>
      if CompCert4Lean.X86_64.Archi.ptr64 then none
      else some (add_equation { ekind := Low, ereg := r, eloc := R lo }
        (add_equation { ekind := High, ereg := r, eloc := R hi } e))
  | _, _ => none

def remove_equations_res (r : reg) (p : rpair mreg)
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
          match remove_equations_res res res' e1 with
          | none => none
          | some e2 =>
              let resultRegs := regs_of_rpair res'
              let resultOk := resultRegs.all (fun l => reg_loc_unconstrained res (R l) e2)
              if resultOk && no_caller_saves cfg e2 then
                match add_equation_ros ros ros' e2 with
                | none => none
                | some e3 =>
                    match add_equations_args args (proj_sig_args sg) args' e3 with
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
            match add_equations_args args (proj_sig_args sg) args' e1 with
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
      match add_equations_res arg (proj_sig_res f.fn_sig)
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
  | OK a, OK b =>
      OK (mkeqs (EqSet.union a.eqs1 b.eqs1) (EqSet2.union a.eqs2 b.eqs2)
        (fun q => by
          constructor
          · intro h
            rcases EqSet2.union_1 a.eqs2 b.eqs2 q h with h | h
            · exact EqSet.union_2 a.eqs1 b.eqs1 q ((a.eqs_same q).mp h)
            · exact EqSet.union_3 a.eqs1 b.eqs1 q ((b.eqs_same q).mp h)
          · intro h
            rcases EqSet.union_1 a.eqs1 b.eqs1 q h with h | h
            · exact EqSet2.union_2 a.eqs2 b.eqs2 q ((a.eqs_same q).mpr h)
            · exact EqSet2.union_3 a.eqs2 b.eqs2 q ((b.eqs_same q).mpr h)))
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

def law_obligation : Prop :=
  SemiLatticeLaws L ∧ NodeSetBackward.law_obligation

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

def compat_entry : List reg → List (rpair loc) → eqs → Bool
  | [], [], _ => true
  | r :: rs, .One l :: ls, e => compat_left r l e && compat_entry rs ls e
  | r :: rs, .Twolong hi lo :: ls, e =>
      compat_left2 r hi lo e && compat_entry rs ls e
  | _, _, _ => false

def check_entrypoints_aux (cfg : CompilerConfig) (rtl : RTL.function)
    (ltl : LTL.function) (env : regenv) (e1 : eqs) : Option Unit :=
  match pair_entrypoints rtl ltl with
  | none => none
  | some mv =>
      match track_moves env mv e1 with
      | none => none
      | some e2 =>
          if compat_entry rtl.fn_params
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
