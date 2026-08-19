import CompCert4Lean.Config
import CompCert4Lean.Foundation.RocqStdlib
import CompCert4Lean.Backend.Bounds
import CompCert4Lean.Backend.Lineartyping
import CompCert4Lean.Backend.Linear
import CompCert4Lean.Backend.Locations
import CompCert4Lean.Backend.Mach
import CompCert4Lean.Common.AST
import CompCert4Lean.Common.Errors
import CompCert4Lean.Lib.Coqlib
import CompCert4Lean.Lib.Integers
import CompCert4Lean.X86.Op
import CompCert4Lean.X86.Stacklayout

/-!
# Layout of activation records and Linear-to-Mach translation

Definition-bearing translation of CompCert's `backend/Stacking.v`.
-/

namespace CompCert4Lean.Backend.Stacking

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Bounds
open CompCert4Lean.Backend.Conventions
open CompCert4Lean.Backend.Lineartyping
open CompCert4Lean.Backend.Linear
open CompCert4Lean.Backend.Locations
open CompCert4Lean.Backend.Mach
open CompCert4Lean.Common.AST
open CompCert4Lean.Common.Errors
open CompCert4Lean.Lib.Coqlib
open CompCert4Lean.Lib.Integers
open CompCert4Lean.X86.Machregs
open CompCert4Lean.X86.Op
open CompCert4Lean.X86.Stacklayout

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Z := CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z
private abbrev LinearFunction := CompCert4Lean.Backend.Linear.function
private abbrev LinearFundef := CompCert4Lean.Backend.Linear.fundef
private abbrev LinearProgram := CompCert4Lean.Backend.Linear.program
private abbrev MachCode := CompCert4Lean.Backend.Mach.code
private abbrev MachFunction := CompCert4Lean.Backend.Mach.function
private abbrev MachFundef := CompCert4Lean.Backend.Mach.fundef
private abbrev MachProgram := CompCert4Lean.Backend.Mach.program
private abbrev RocqString :=
  CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string

private abbrev z4 : Z := ZArith.BinInt.Z.of_nat 4
private abbrev zAdd := ZArith.BinInt.Z.add

private def bytesToString : List UInt8 → RocqString
  | [] => .EmptyString
  | byte :: rest => .String byte (bytesToString rest)

private def illFormedLinearText : RocqString :=
  bytesToString
    [73, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 76, 105, 110, 101,
      97, 114, 32, 99, 111, 100, 101]

private def stackSizeExceededText : RocqString :=
  bytesToString
    [84, 111, 111, 32, 109, 97, 110, 121, 32, 115, 112, 105, 108, 108, 101,
      100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 44, 32, 115, 116,
      97, 99, 107, 32, 115, 105, 122, 101, 32, 101, 120, 99, 101, 101, 100,
      101, 100]

def offset_local (fe : frame_env) (x : Z) : Z :=
  zAdd fe.fe_ofs_local (ZArith.BinInt.Z.mul z4 x)

def offset_arg (cfg : CompilerConfig) (x : Z) : Z :=
  zAdd (fe_ofs_arg cfg) (ZArith.BinInt.Z.mul z4 x)

def save_callee_save_rec : List mreg → Z → MachCode → MachCode
  | [], _, k => k
  | r :: rl, ofs, k =>
      let ty := mreg_type r
      let sz := CompCert4Lean.Common.AST.typesize ty
      let ofs1 := align ofs sz
      Msetstack r (Ptrofs.repr ofs1) ty ::
        save_callee_save_rec rl (zAdd ofs1 sz) k

def save_callee_save (fe : frame_env) (k : MachCode) : MachCode :=
  save_callee_save_rec fe.fe_used_callee_save fe.fe_ofs_callee_save k

def restore_callee_save_rec : List mreg → Z → MachCode → MachCode
  | [], _, k => k
  | r :: rl, ofs, k =>
      let ty := mreg_type r
      let sz := CompCert4Lean.Common.AST.typesize ty
      let ofs1 := align ofs sz
      Mgetstack (Ptrofs.repr ofs1) ty r ::
        restore_callee_save_rec rl (zAdd ofs1 sz) k

def restore_callee_save (fe : frame_env) (k : MachCode) : MachCode :=
  restore_callee_save_rec fe.fe_used_callee_save fe.fe_ofs_callee_save k

def simplify_store (chunk : memory_chunk) : memory_chunk :=
  match chunk with
  | .Mbool => .Mint8unsigned
  | .Mint8signed => .Mint8unsigned
  | .Mint16signed => .Mint16unsigned
  | _ => chunk

def simplify_load (chunk : memory_chunk) : memory_chunk :=
  match chunk with
  | .Mbool => .Mint8unsigned
  | _ => chunk

def transl_op (fe : frame_env) (op : operation) : operation :=
  shift_stack_operation fe.fe_stack_data op

def transl_addr (fe : frame_env) (addr : addressing) : addressing :=
  shift_stack_addressing fe.fe_stack_data addr

def transl_builtin_arg (fe : frame_env) :
    builtin_arg loc → builtin_arg mreg
  | .BA (.R r) => .BA r
  | .BA (.S .Local ofs ty) =>
      .BA_loadstack (chunk_of_type ty) (Ptrofs.repr (offset_local fe ofs))
  | .BA (.S _ _ _) => .BA_int (CompCert4Lean.Lib.Integers.Int.zero)
  | .BA_int n => .BA_int n
  | .BA_long n => .BA_long n
  | .BA_float n => .BA_float n
  | .BA_single n => .BA_single n
  | .BA_loadstack chunk ofs =>
      .BA_loadstack chunk (Ptrofs.add ofs (Ptrofs.repr fe.fe_stack_data))
  | .BA_addrstack ofs =>
      .BA_addrstack (Ptrofs.add ofs (Ptrofs.repr fe.fe_stack_data))
  | .BA_loadglobal chunk id ofs => .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => .BA_addrglobal id ofs
  | .BA_splitlong hi lo =>
      .BA_splitlong (transl_builtin_arg fe hi) (transl_builtin_arg fe lo)
  | .BA_addptr a1 a2 =>
      .BA_addptr (transl_builtin_arg fe a1) (transl_builtin_arg fe a2)

def transl_instr (cfg : CompilerConfig) (fe : frame_env)
    (i : Linear.instruction) (k : MachCode) : MachCode :=
  match i with
  | .Lgetstack sl ofs ty r =>
      match sl with
      | .Local => Mgetstack (Ptrofs.repr (offset_local fe ofs)) ty r :: k
      | .Incoming => Mgetparam (Ptrofs.repr (offset_arg cfg ofs)) ty r :: k
      | .Outgoing => Mgetstack (Ptrofs.repr (offset_arg cfg ofs)) ty r :: k
  | .Lsetstack r sl ofs ty =>
      match sl with
      | .Local => Msetstack r (Ptrofs.repr (offset_local fe ofs)) ty :: k
      | .Incoming => k
      | .Outgoing => Msetstack r (Ptrofs.repr (offset_arg cfg ofs)) ty :: k
  | .Lop op args res => Mop (transl_op fe op) args res :: k
  | .Lload chunk addr args dst =>
      Mload (simplify_load chunk) (transl_addr fe addr) args dst :: k
  | .Lstore chunk addr args src =>
      Mstore (simplify_store chunk) (transl_addr fe addr) args src :: k
  | .Lcall sig ros => Mcall sig ros :: k
  | .Ltailcall sig ros => restore_callee_save fe (Mtailcall sig ros :: k)
  | .Lbuiltin ef args dst =>
      Mbuiltin ef (args.map (transl_builtin_arg fe)) dst :: k
  | .Llabel lbl => Mlabel lbl :: k
  | .Lgoto lbl => Mgoto lbl :: k
  | .Lcond cond args lbl => Mcond cond args lbl :: k
  | .Ljumptable arg tbl => Mjumptable arg tbl :: k
  | .Lreturn => restore_callee_save fe (Mreturn :: k)

def transl_code (cfg : CompilerConfig) (fe : frame_env)
    (il : List Linear.instruction) : MachCode :=
  list_fold_right (transl_instr cfg fe) il []

def transl_body (cfg : CompilerConfig) (f : LinearFunction) (fe : frame_env) : MachCode :=
  save_callee_save fe (transl_code cfg fe f.fn_code)

def transf_function (cfg : CompilerConfig) (f : LinearFunction) : res MachFunction :=
  let fe := make_env cfg (function_bounds cfg f)
  if wt_function cfg f = false then
    Error (msg illFormedLinearText)
  else
    match zlt Ptrofs.max_unsigned fe.fe_size with
    | .left _ =>
        OK
          { fn_sig := f.fn_sig
            fn_code := transl_body cfg f fe
            fn_stacksize := fe.fe_size
            fn_link_ofs := Ptrofs.repr fe.fe_ofs_link
            fn_retaddr_ofs := Ptrofs.repr fe.fe_ofs_retaddr }
    | .right _ => Error (msg stackSizeExceededText)

def transf_fundef (cfg : CompilerConfig) (f : LinearFundef) : res MachFundef :=
  CompCert4Lean.Common.AST.transf_partial_fundef (transf_function cfg) f

def transf_program (cfg : CompilerConfig) (p : LinearProgram) : res MachProgram :=
  CompCert4Lean.Common.AST.transform_partial_program (transf_fundef cfg) p

end CompCert4Lean.Backend.Stacking
