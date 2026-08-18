import CompCert4Lean.Config
import CompCert4Lean.Backend.Locations

/-!
# x86 calling conventions

Definition-bearing translation of CompCert's `x86/Conventions1.v`. Proof
declarations assigned to later proof migration are represented by exact
transparent proposition descriptors. The source `Archi.win64` parameter is
threaded through the accepted immutable compiler-configuration interface.
-/

namespace CompCert4Lean.X86.Conventions1

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.AST
open CompCert4Lean.Backend.Locations
open CompCert4Lean.X86.Machregs

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z

private abbrev z0 : Z := .Z0
private abbrev zOfNat := ZArith.BinInt.Z.of_nat
private abbrev zAdd := ZArith.BinInt.Z.add
private abbrev zLe := ZArith.BinInt.Z.le
private abbrev zDivide := ZArith.BinInt.Z.divide

private abbrev z1 : Z := zOfNat 1
private abbrev z2 : Z := zOfNat 2

/-! ## Classification of machine registers -/

def is_callee_save (cfg : CompilerConfig) : mreg → Bool
  | .AX | .CX | .DX => false
  | .BX | .BP => true
  | .SI | .DI => !CompCert4Lean.X86_64.Archi.ptr64 ||
      CompCert4Lean.X86_64.Archi.win64 cfg
  | .R8 | .R9 | .R10 | .R11 => false
  | .R12 | .R13 | .R14 | .R15 => true
  | .X0 | .X1 | .X2 | .X3 | .X4 | .X5 | .X6 | .X7 => false
  | .X8 | .X9 | .X10 | .X11 | .X12 | .X13 | .X14 | .X15 =>
      CompCert4Lean.X86_64.Archi.win64 cfg
  | .FP0 => false

def destroyed_at_call (cfg : CompilerConfig) : List mreg :=
  all_mregs.filter (fun r => !(is_callee_save cfg r))

/-! ## Location of function results -/

def loc_result_32 (s : signature) : rpair mreg :=
  match proj_sig_res s with
  | .Tint | .Tany32 => .One AX
  | .Tfloat | .Tsingle => .One FP0
  | .Tany64 => .One X0
  | .Tlong => .Twolong DX AX

def loc_result_64 (s : signature) : rpair mreg :=
  match proj_sig_res s with
  | .Tint | .Tlong | .Tany32 | .Tany64 => .One AX
  | .Tfloat | .Tsingle => .One X0

def loc_result : signature → rpair mreg :=
  if CompCert4Lean.X86_64.Archi.ptr64 then loc_result_64 else loc_result_32

def loc_result_typeStatement : Prop :=
  ∀ sig : signature,
    subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true

def loc_result_caller_saveStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature),
    forall_rpair (fun r => is_callee_save cfg r = false) (loc_result s)

def loc_result_pairStatement : Prop :=
  ∀ sg : signature,
    match loc_result sg with
    | .One _ => True
    | .Twolong r1 r2 =>
        r1 ≠ r2 ∧ proj_sig_res sg = Tlong ∧
          subtype Tint (mreg_type r1) = true ∧
          subtype Tint (mreg_type r2) = true ∧
          CompCert4Lean.X86_64.Archi.ptr64 = false

def loc_result_extenStatement : Prop :=
  ∀ s1 s2 : signature,
    s1.sig_res = s2.sig_res → loc_result s1 = loc_result s2

/-! ## Location of function arguments -/

def loc_arguments_32 : List typ → Z → List (rpair loc)
  | [], _ => []
  | ty :: tys, ofs =>
      (match ty with
      | .Tlong =>
          .Twolong (.S Outgoing (zAdd ofs z1) Tint) (.S Outgoing ofs Tint)
      | _ => .One (.S Outgoing ofs ty)) ::
        loc_arguments_32 tys
          (zAdd ofs (CompCert4Lean.Backend.Locations.typesize ty))

def int_param_regs_elf64 : List mreg :=
  [DI, SI, DX, CX, R8, R9]

def float_param_regs_elf64 : List mreg :=
  [X0, X1, X2, X3, X4, X5, X6, X7]

def loc_arguments_elf64 :
    List typ → Z → Z → Z → List (rpair loc)
  | [], _, _, _ => []
  | ty :: tys, ir, fr, ofs =>
      match ty with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z int_param_regs_elf64 ir with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_elf64 tys ir fr (zAdd ofs z2)
          | some ireg =>
              .One (.R ireg) ::
                loc_arguments_elf64 tys (zAdd ir z1) fr ofs
      | .Tfloat | .Tsingle =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z float_param_regs_elf64 fr with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_elf64 tys ir fr (zAdd ofs z2)
          | some freg =>
              .One (.R freg) ::
                loc_arguments_elf64 tys ir (zAdd fr z1) ofs

def int_param_regs_win64 : List mreg :=
  [CX, DX, R8, R9]

def float_param_regs_win64 : List mreg :=
  [X0, X1, X2, X3]

def loc_arguments_win64 : List typ → Z → Z → List (rpair loc)
  | [], _, _ => []
  | ty :: tys, r, ofs =>
      match ty with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z int_param_regs_win64 r with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_win64 tys r (zAdd ofs z2)
          | some ireg =>
              .One (.R ireg) ::
                loc_arguments_win64 tys (zAdd r z1) ofs
      | .Tfloat | .Tsingle =>
          match CompCert4Lean.Lib.Coqlib.list_nth_z float_param_regs_win64 r with
          | none =>
              .One (.S Outgoing ofs ty) ::
                loc_arguments_win64 tys r (zAdd ofs z2)
          | some freg =>
              .One (.R freg) ::
                loc_arguments_win64 tys (zAdd r z1) ofs

def loc_arguments (cfg : CompilerConfig) (s : signature) : List (rpair loc) :=
  if CompCert4Lean.X86_64.Archi.ptr64 then
    if CompCert4Lean.X86_64.Archi.win64 cfg then
      loc_arguments_win64 (proj_sig_args s) z0 z0
    else
      loc_arguments_elf64 (proj_sig_args s) z0 z0 z0
  else
    loc_arguments_32 (proj_sig_args s) z0

def loc_argument_acceptable (cfg : CompilerConfig) : loc → Prop
  | .R r => is_callee_save cfg r = false
  | .S .Outgoing ofs ty =>
      zLe z0 ofs ∧ zDivide (CompCert4Lean.Backend.Locations.typealign ty) ofs
  | _ => False

def loc_argument_32_charact (ofs : Z) : loc → Prop
  | .S .Outgoing ofs' ty =>
      zLe ofs ofs' ∧ CompCert4Lean.Backend.Locations.typealign ty = z1
  | _ => False

def loc_argument_elf64_charact (ofs : Z) : loc → Prop
  | .R r => r ∈ int_param_regs_elf64 ∨ r ∈ float_param_regs_elf64
  | .S .Outgoing ofs' _ => zLe ofs ofs' ∧ zDivide z2 ofs'
  | _ => False

def loc_argument_win64_charact (ofs : Z) : loc → Prop
  | .R r => r ∈ int_param_regs_win64 ∨ r ∈ float_param_regs_win64
  | .S .Outgoing ofs' _ => zLe ofs ofs' ∧ zDivide z2 ofs'
  | _ => False

def loc_arguments_32_charactStatement : Prop :=
  ∀ (tyl : List typ) (ofs : Z) (p : rpair loc),
    p ∈ loc_arguments_32 tyl ofs →
      forall_rpair (loc_argument_32_charact ofs) p

def loc_arguments_elf64_charactStatement : Prop :=
  ∀ (tyl : List typ) (ir fr ofs : Z) (p : rpair loc),
    p ∈ loc_arguments_elf64 tyl ir fr ofs → zDivide z2 ofs →
      forall_rpair (loc_argument_elf64_charact ofs) p

def loc_arguments_win64_charactStatement : Prop :=
  ∀ (tyl : List typ) (r ofs : Z) (p : rpair loc),
    p ∈ loc_arguments_win64 tyl r ofs → zDivide z2 ofs →
      forall_rpair (loc_argument_win64_charact ofs) p

def loc_arguments_acceptableStatement : Prop :=
  ∀ (cfg : CompilerConfig) (s : signature) (p : rpair loc),
    p ∈ loc_arguments cfg s →
      forall_rpair (loc_argument_acceptable cfg) p

def loc_arguments_mainStatement : Prop :=
  ∀ cfg : CompilerConfig, loc_arguments cfg signature_main = []

/-! ## Normalization of function results and parameters -/

def return_value_needs_normalization : xtype → Bool
  | .Xint8signed | .Xint8unsigned | .Xint16signed | .Xint16unsigned => true
  | _ => false

def parameter_needs_normalization (_t : xtype) : Bool :=
  false

end CompCert4Lean.X86.Conventions1
