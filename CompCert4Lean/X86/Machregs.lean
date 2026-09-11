import CompCert4Lean.X86.Op

/-!
# x86 machine registers

Definition-bearing translation of CompCert's `x86/Machregs.v`. Proof
declarations assigned to later proof migration are represented by exact
transparent proposition descriptors.
-/

namespace CompCert4Lean.X86.Machregs

open CompCert4Lean.Common.AST
open CompCert4Lean.X86.Op

private abbrev Sumbool := CompCert4Lean.Foundation.Logic.Support.Sumbool
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string
private abbrev positive := CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev posOfNat :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.PArith.BinPos.Pos.of_nat
private abbrev zOfNat :=
  CompCert4Lean.Foundation.Numbers.Rocq.Coq.ZArith.BinInt.Z.of_nat

private def boolOfSumbool {P Q : Prop} (d : Sumbool P Q) : Bool :=
  match d with
  | .left _ => true
  | .right _ => false

private def ofString (s : String) : RocqString :=
  (String.toUTF8 s).toList.foldr
    (fun b tail =>
      CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.String b tail)
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.EmptyString

private def stringEq (s1 s2 : RocqString) : Bool :=
  boolOfSumbool
    (CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string_dec s1 s2)

/-! ## Machine registers -/

inductive mreg : Type where
  | AX | BX | CX | DX | SI | DI | BP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15
  | FP0

export mreg (AX BX CX DX SI DI BP R8 R9 R10 R11 R12 R13 R14 R15 X0 X1 X2
  X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 FP0)

def mreg_eqStatement :=
  ∀ r1 r2 : mreg, Sumbool (r1 = r2) (r1 ≠ r2)

def mreg_eq (r1 r2 : mreg) : Sumbool (r1 = r2) (r1 ≠ r2) := by
  cases r1 <;> cases r2 <;>
    first
    | exact .left rfl
    | exact .right (by intro h; cases h)

def all_mregs : List mreg :=
  [ AX, BX, CX, DX, SI, DI, BP
  , R8, R9, R10, R11, R12, R13, R14, R15
  , X0, X1, X2, X3, X4, X5, X6, X7
  , X8, X9, X10, X11, X12, X13, X14, X15
  , FP0
  ]

def all_mregs_completeStatement : Prop :=
  ∀ r : mreg, r ∈ all_mregs

def mreg_type : mreg → typ
  | .AX | .BX | .CX | .DX | .SI | .DI | .BP =>
      if CompCert4Lean.X86_64.Archi.ptr64 then Tany64 else Tany32
  | .R8 | .R9 | .R10 | .R11 | .R12 | .R13 | .R14 | .R15 => Tany64
  | .X0 | .X1 | .X2 | .X3 | .X4 | .X5 | .X6 | .X7 => Tany64
  | .X8 | .X9 | .X10 | .X11 | .X12 | .X13 | .X14 | .X15 => Tany64
  | .FP0 => Tany64

namespace IndexedMreg

def index : mreg → positive
  | .AX => posOfNat 1
  | .BX => posOfNat 2
  | .CX => posOfNat 3
  | .DX => posOfNat 4
  | .SI => posOfNat 5
  | .DI => posOfNat 6
  | .BP => posOfNat 7
  | .R8 => posOfNat 8
  | .R9 => posOfNat 9
  | .R10 => posOfNat 10
  | .R11 => posOfNat 11
  | .R12 => posOfNat 12
  | .R13 => posOfNat 13
  | .R14 => posOfNat 14
  | .R15 => posOfNat 15
  | .X0 => posOfNat 16
  | .X1 => posOfNat 17
  | .X2 => posOfNat 18
  | .X3 => posOfNat 19
  | .X4 => posOfNat 20
  | .X5 => posOfNat 21
  | .X6 => posOfNat 22
  | .X7 => posOfNat 23
  | .X8 => posOfNat 24
  | .X9 => posOfNat 25
  | .X10 => posOfNat 26
  | .X11 => posOfNat 27
  | .X12 => posOfNat 28
  | .X13 => posOfNat 29
  | .X14 => posOfNat 30
  | .X15 => posOfNat 31
  | .FP0 => posOfNat 32

def index_injStatement : Prop :=
  ∀ r1 r2 : mreg, index r1 = index r2 → r1 = r2

end IndexedMreg

/-! ## Register names -/

def register_names : List (RocqString × mreg) :=
  [ (ofString "RAX", AX), (ofString "RBX", BX), (ofString "RCX", CX)
  , (ofString "RDX", DX), (ofString "RSI", SI), (ofString "RDI", DI)
  , (ofString "RBP", BP), (ofString "EAX", AX), (ofString "EBX", BX)
  , (ofString "ECX", CX), (ofString "EDX", DX), (ofString "ESI", SI)
  , (ofString "EDI", DI), (ofString "EBP", BP), (ofString "R8", R8)
  , (ofString "R9", R9), (ofString "R10", R10), (ofString "R11", R11)
  , (ofString "R12", R12), (ofString "R13", R13), (ofString "R14", R14)
  , (ofString "R15", R15), (ofString "XMM0", X0), (ofString "XMM1", X1)
  , (ofString "XMM2", X2), (ofString "XMM3", X3), (ofString "XMM4", X4)
  , (ofString "XMM5", X5), (ofString "XMM6", X6), (ofString "XMM7", X7)
  , (ofString "XMM8", X8), (ofString "XMM9", X9), (ofString "XMM10", X10)
  , (ofString "XMM11", X11), (ofString "XMM12", X12)
  , (ofString "XMM13", X13), (ofString "XMM14", X14)
  , (ofString "XMM15", X15), (ofString "ST0", FP0)
  ]

def register_by_name (s : RocqString) : Option mreg :=
  let rec assoc : List (RocqString × mreg) → Option mreg
    | [] => none
    | (s1, r1) :: rest => if stringEq s s1 then some r1 else assoc rest
  assoc register_names

/-! ## Destroyed registers and builtin constraints -/

def destroyed_by_op : operation → List mreg
  | .Ocast8signed | .Ocast8unsigned => [AX]
  | .Omulhs | .Omulhu | .Odiv | .Odivu | .Omod | .Omodu => [AX, DX]
  | .Oshrximm _ => [CX]
  | .Omullhs | .Omullhu | .Odivl | .Odivlu | .Omodl | .Omodlu => [AX, DX]
  | .Oshrxlimm _ => [DX]
  | .Ocmp _ => [AX, CX]
  | _ => []

def destroyed_by_load (_chunk : memory_chunk) (_addr : addressing) : List mreg :=
  []

def destroyed_by_store (chunk : memory_chunk) (_addr : addressing) : List mreg :=
  match chunk with
  | .Mbool | .Mint8signed | .Mint8unsigned =>
      if CompCert4Lean.X86_64.Archi.ptr64 then [] else [AX, CX]
  | _ => []

def destroyed_by_cond (_cond : condition) : List mreg :=
  []

def destroyed_by_jumptable : List mreg :=
  [AX, DX]

def destroyed_by_clobber : List RocqString → List mreg
  | [] => []
  | clobber :: rest =>
      match register_by_name clobber with
      | some r => r :: destroyed_by_clobber rest
      | none => destroyed_by_clobber rest

def destroyed_by_builtin : external_function → List mreg
  | .EF_memcpy size _ =>
      if boolOfSumbool (CompCert4Lean.Lib.Coqlib.zle size (zOfNat 32)) then
        [CX, X7]
      else
        [CX, SI, DI]
  | .EF_vstore .Mint8unsigned | .EF_vstore .Mint8signed =>
      if CompCert4Lean.X86_64.Archi.ptr64 then [] else [AX, CX]
  | .EF_builtin name _ =>
      if stringEq name (ofString "__builtin_va_start") then
        [AX]
      else if stringEq name (ofString "__builtin_write16_reversed") ||
          stringEq name (ofString "__builtin_write32_reversed") then
        [CX, DX]
      else
        []
  | .EF_inline_asm _ _ clobbers => destroyed_by_clobber clobbers
  | _ => []

def destroyed_at_function_entry : List mreg :=
  [AX, FP0]

def destroyed_by_setstack : typ → List mreg
  | .Tfloat | .Tsingle => [FP0]
  | _ => []

def temp_for_parent_frame : mreg :=
  AX

def builtin_constraints : external_function → List builtin_arg_constraint
  | .EF_vload _ => [OK_addressing]
  | .EF_vstore _ => [OK_addressing, OK_default]
  | .EF_memcpy _ _ => [OK_addrstack, OK_addrstack]
  | .EF_annot _ _ targs => targs.map (fun _ => OK_all)
  | .EF_debug _ _ targs => targs.map (fun _ => OK_all)
  | _ => []

end CompCert4Lean.X86.Machregs

namespace CompCert4Lean.X86.Machregs

theorem all_mregs_complete : all_mregs_completeStatement := by
  intro r
  cases r <;> simp [all_mregs]

namespace IndexedMreg

theorem index_inj : index_injStatement := by
  intro r1 r2 h
  cases r1 <;> cases r2 <;>
    first
    | rfl
    | exfalso
      revert h
      decide

end IndexedMreg
end CompCert4Lean.X86.Machregs
