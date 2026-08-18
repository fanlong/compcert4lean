import CompCert4Lean.Backend.Conventions
import CompCert4Lean.Backend.RTL

/-!
# Tail-call recognition and transformation

Definition-bearing translation of CompCert's `backend/Tailcall.v`.  The
processor calling-convention parameter used by the source transformation is
represented by the integrated immutable compiler configuration.
-/

namespace CompCert4Lean.Backend.Tailcall

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Backend.Registers
open CompCert4Lean.Backend.RTL
open CompCert4Lean.Common.AST
open CompCert4Lean.Lib.Maps
open CompCert4Lean.X86.Op

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig

/--
Recognize a return of `rret`, allowing the no-op and register-move chains
introduced by RTL generation.  The fuel bounds both lookahead and recursion.
-/
def is_return : Nat → function → node → reg → Bool
  | 0, _, _, _ => false
  | n + 1, f, pc, rret =>
      match PTree.get pc f.fn_code with
      | some (Ireturn none) => true
      | some (Ireturn (some r)) => decide (r = rret)
      | some (Inop s) => is_return n f s rret
      | some (Iop op args dst s) =>
          match is_move_operation op args with
          | none => false
          | some src =>
              if decide (rret = src) then is_return n f s dst else false
      | _ => false

/-- Maximum no-op/move/return lookahead used by `is_return`. -/
def niter : Nat := 5

/-- Turn an eligible call followed by a recognized return chain into a tail call. -/
def transf_instr (cfg : CompilerConfig) (f : function) (_pc : node)
    (instr : instruction) : instruction :=
  match instr with
  | Icall sig ros args res s =>
      if is_return niter f s res &&
          CompCert4Lean.Backend.Conventions.tailcall_is_possible cfg sig &&
          decide (sig.sig_res = f.fn_sig.sig_res) then
        Itailcall sig ros args
      else
        instr
  | _ => instr

/-- Transform a function only when it has no stack block and is not variadic. -/
def transf_function (cfg : CompilerConfig) (f : function) : function :=
  if decide (f.fn_stacksize = .Z0) &&
      decide (f.fn_sig.sig_cc.cc_vararg = none) then
    CompCert4Lean.Backend.RTL.transf_function (transf_instr cfg f) f
  else
    f

def transf_fundef (cfg : CompilerConfig) (fd : fundef) : fundef :=
  CompCert4Lean.Common.AST.transf_fundef (transf_function cfg) fd

def transf_program (cfg : CompilerConfig) (p : program) : program :=
  CompCert4Lean.Common.AST.transform_program (transf_fundef cfg) p

end CompCert4Lean.Backend.Tailcall
