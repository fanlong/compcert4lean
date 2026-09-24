import CompCert4Lean.X86.Conventions1
import Std.Data.TreeSet
import Std.Data.TreeMap
import Std.Data.HashMap

namespace CompCert4Lean.Allocator

open Common.AST Backend.Locations X86.Machregs X86.Op
open Foundation.Numbers.Rocq.Coq

abbrev IndexSet := Std.TreeSet Nat
abbrev IndexMap := Std.TreeMap Nat Nat

structure AllocationContext where
  reserved : List mreg := []

def AllocationContext.empty : AllocationContext := {}

structure AllocationStats where
  pseudoRegisters : Nat := 0
  machineRegisters : Nat := 0
  rounds : Nat := 0
  spills : Nat := 0
  reloads : Nat := 0
  reloadsReused : Nat := 0
  movesRemoved : Nat := 0
  coalesced : Nat := 0
  stackSlots : Nat := 0
  stackWords : Nat := 0
  deadInstructions : Nat := 0
deriving Repr

def regEqual (left right : mreg) : Bool :=
  match mreg_eq left right with | .left _ => true | .right _ => false

def locEqual (left right : loc) : Bool :=
  match Loc.eq left right with | .left _ => true | .right _ => false

def locDisjoint (left right : loc) : Bool :=
  match Loc.diff_dec left right with | .left _ => true | .right _ => false

def typeEqual (left right : typ) : Bool :=
  match typ_eq left right with | .left _ => true | .right _ => false

def registerClass : typ → Nat
  | .Tfloat | .Tsingle => 1
  | _ => 0

def machineClass : mreg → Nat
  | .AX | .BX | .CX | .DX | .SI | .DI | .BP
  | .R8 | .R9 | .R10 | .R11 | .R12 | .R13 | .R14 | .R15 => 0
  | _ => 1

def integerPreferred : List mreg := [.AX, .CX, .DX, .SI, .DI, .R8, .R9, .R10, .R11]
def integerRemaining : List mreg := [.BX, .BP, .R12, .R13, .R14, .R15]
def floatRegisters : List mreg :=
  [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15]

def available (context : AllocationContext) (registers : List mreg) : List mreg :=
  registers.filter fun register => !context.reserved.any (regEqual register)

def preferredRegisters (context : AllocationContext) (classId : Nat) : List mreg :=
  available context (if classId == 0 then integerPreferred else floatRegisters)

def remainingRegisters (context : AllocationContext) (classId : Nat) : List mreg :=
  available context (if classId == 0 then integerRemaining else [])

def registerPool (context : AllocationContext) (classId : Nat) : List mreg :=
  preferredRegisters context classId ++ remainingRegisters context classId

def reservedWellFormed (context : AllocationContext) : Bool :=
  context.reserved.all (fun register =>
    integerRemaining.any (regEqual register) &&
    (context.reserved.filter (regEqual register)).length == 1)

def operationConstraints : operation → List (Option mreg) × Option mreg
  | .Omulhs | .Omulhu | .Omullhs | .Omullhu => ([some .AX, none], some .DX)
  | .Odiv | .Odivu | .Odivl | .Odivlu => ([some .AX, some .CX], some .AX)
  | .Omod | .Omodu | .Omodl | .Omodlu => ([some .AX, some .CX], some .DX)
  | .Oshl | .Oshr | .Oshru | .Oshll | .Oshrl | .Oshrlu => ([none, some .CX], none)
  | .Oshrximm _ | .Oshrxlimm _ => ([some .AX], some .AX)
  | _ => ([], none)

def stringEqual (name : Foundation.RocqString.Rocq.Coq.Strings.String.string)
    (text : String) : Bool :=
  match Foundation.RocqString.Rocq.Coq.Strings.String.string_dec name
      (text.toUTF8.toList.foldr .String .EmptyString) with
  | .left _ => true
  | .right _ => false

def builtinConstraints : external_function → List (Option mreg) × List (Option mreg)
  | .EF_memcpy size _ =>
      if intOfZ size <= 32 then ([some .AX, some .DX], [])
      else ([some .DI, some .SI], [])
  | .EF_builtin name _ =>
      if stringEqual name "__builtin_negl" then
        ([some .DX, some .AX], [some .DX, some .AX])
      else if stringEqual name "__builtin_addl" || stringEqual name "__builtin_subl" then
        ([some .DX, some .AX, some .CX, some .BX], [some .DX, some .AX])
      else if stringEqual name "__builtin_mull" then
        ([some .AX, some .DX], [some .DX, some .AX])
      else if stringEqual name "__builtin_va_start" then ([some .DX], [])
      else ([], [])
  | _ => ([], [])

def twoAddress : operation → Bool
  | .Oneg | .Osub | .Omul | .Omulimm _ | .Oand | .Oandimm _ | .Oor | .Oorimm _
  | .Oxor | .Oxorimm _ | .Onot | .Oshl | .Oshlimm _ | .Oshr | .Oshrimm _
  | .Oshru | .Oshruimm _ | .Ororimm _ | .Oshldimm _ | .Omakelong | .Olowlong
  | .Ohighlong | .Onegl | .Oaddlimm _ | .Osubl | .Omull | .Omullimm _ | .Oandl
  | .Oandlimm _ | .Oorl | .Oorlimm _ | .Oxorl | .Oxorlimm _ | .Onotl | .Oshll
  | .Oshllimm _ | .Oshrl | .Oshrlimm _ | .Oshrlu | .Oshrluimm _ | .Ororlimm _
  | .Onegf | .Oabsf | .Oaddf | .Osubf | .Omulf | .Odivf | .Omaxf | .Ominf
  | .Onegfs | .Oabsfs | .Oaddfs | .Osubfs | .Omulfs | .Odivfs | .Osel _ _ => true
  | _ => false

def machineIndex (register : mreg) : Nat :=
  PArith.BinPos.Pos.to_nat (IndexedMreg.index register) - 1

def setOfList (values : List Nat) : IndexSet :=
  values.foldl (fun result value => result.insert value) {}

def setUnion (left right : IndexSet) : IndexSet :=
  left.union right

def setRemove (values : List Nat) (set : IndexSet) : IndexSet :=
  values.foldl (fun result value => result.erase value) set

end CompCert4Lean.Allocator
