import CompCert4Lean.Driver.Compiler

/-!
# Per-invocation diagnostic effects

The theorem-facing compiler callbacks are pure `Unit` definitions.  This
module owns only their executable companion: a per-invocation sink whose
callbacks may perform `IO`, while keeping the sink out of immutable compiler
configuration and the pure `Errors.Res` result.

The sink remains outside the pure compiler and its `Errors.res` channel.  The
executable entry points below replay the pure pipeline at the `IO` boundary so
that successful prefixes are observable while a failed pass suppresses all
later events.
-/

namespace CompCert4Lean.Driver.Diagnostics

structure DiagnosticSink where
  clight : CompCert4Lean.Cfrontend.Clight.program → IO Unit
  cminor : CompCert4Lean.Backend.Cminor.program → IO Unit
  rtl : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z →
    CompCert4Lean.Backend.RTL.program → IO Unit
  ltl : CompCert4Lean.Backend.LTL.program → IO Unit
  mach : CompCert4Lean.Backend.Mach.program → IO Unit

/-- The ordinary no-diagnostics sink; every callback completes with no output. -/
def DiagnosticSink.silent : DiagnosticSink :=
  { clight := fun _ => pure ()
    cminor := fun _ => pure ()
    rtl := fun _ _ => pure ()
    ltl := fun _ => pure ()
    mach := fun _ => pure () }

open CompCert4Lean.Foundation.Numbers.Rocq.Coq
open CompCert4Lean.Common.Errors
open CompCert4Lean.Cfrontend
open CompCert4Lean.Backend
open CompCert4Lean.Backend.Selection
open CompCert4Lean.X86

private abbrev CompilerConfig := CompCert4Lean.Config.CompilerConfig
private abbrev Res := CompCert4Lean.Common.Errors.res
private abbrev BinaryNormalizeCertificate :=
  CompCert4Lean.Flocq.IEEE754.Binary.BinaryNormalizeCertificate
private abbrev BexactInverseCertificate :=
  CompCert4Lean.Lib.IEEE754_extra.Bexact_inverse_certificate
private abbrev zOfNat := ZArith.BinInt.Z.of_nat

private def rtlTag (n : Nat) : Z := ZArith.BinInt.Z.of_nat n

private def emitResult {A : Type} (emit : A → IO Unit) (value : A) :
    IO (Res A) := do
  emit value
  pure (.OK value)

private def bindIORes {A B : Type} (action : IO (Res A))
    (next : A → IO (Res B)) : IO (Res B) := do
  match ← action with
  | .Error message => pure (.Error message)
  | .OK value => next value

/-! ## Executable diagnostic companions -/

def transf_rtl_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    (sink : DiagnosticSink)
    (cfg : CompilerConfig) (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : RTL.program) : IO (Res Asm.program) :=
  let p0 : IO (Res RTL.program) :=
    emitResult (sink.rtl (rtlTag 0)) p
  let p1 := bindIORes p0 fun p =>
    let tp :=
      if CompCert4Lean.Driver.Compopts.optim_tailcalls cfg then
        Tailcall.transf_program cfg p
      else
        p
    emitResult (sink.rtl (rtlTag 1)) tp
  let p2 := bindIORes p1 fun p =>
    match Inlining.transf_program inlineCfg p with
    | .Error message => pure (.Error message)
    | .OK tp => emitResult (sink.rtl (rtlTag 2)) tp
  let p3 := bindIORes p2 fun p =>
    emitResult (sink.rtl (rtlTag 3)) (Renumber.transf_program p)
  let p4 := bindIORes p3 fun p =>
    let p := if CompCert4Lean.Driver.Compopts.optim_CSE cfg &&
        CompCert4Lean.Driver.Compopts.optim_constprop cfg then
      LoopUnroll.transf_program LoopUnroll.acyclic_paths p else p
    let tp :=
      if CompCert4Lean.Driver.Compopts.optim_constprop cfg then
        Constprop.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg p
      else
        p
    emitResult (sink.rtl (rtlTag 4)) tp
  let p5 := bindIORes p4 fun p =>
    let p := if CompCert4Lean.Driver.Compopts.optim_CSE cfg &&
        CompCert4Lean.Driver.Compopts.optim_constprop cfg then
      LoopUnroll.transf_program LoopUnroll.small_loops p else p
    let tp :=
      if CompCert4Lean.Driver.Compopts.optim_constprop cfg then
        Renumber.transf_program p
      else
        p
    emitResult (sink.rtl (rtlTag 5)) tp
  let p6 := bindIORes p5 fun p =>
    let result :=
      if CompCert4Lean.Driver.Compopts.optim_CSE cfg then
        CSE.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg p
      else
        .OK p
    match result with
    | .Error message => pure (.Error message)
    | .OK tp => emitResult (sink.rtl (rtlTag 6)) tp
  let p7 := bindIORes p6 fun p =>
    let result :=
      if CompCert4Lean.Driver.Compopts.optim_redundancy cfg then
        Deadcode.transf_program
          (binary64_certificate := binary64_certificate)
          (binary32_certificate := binary32_certificate) cfg p
      else
        .OK p
    match result with
    | .Error message => pure (.Error message)
    | .OK tp => emitResult (sink.rtl (rtlTag 7)) tp
  let p8 := bindIORes p7 fun p =>
    match Unusedglob.transform_program p with
    | .Error message => pure (.Error message)
    | .OK tp => emitResult (sink.rtl (rtlTag 8)) tp
  let p9 := bindIORes p8 fun p =>
    match Allocation.transf_program cfg regallocOracle p with
    | .Error message => pure (.Error message)
    | .OK tp => emitResult sink.ltl tp
  let p10 := bindIORes p9 fun p =>
    pure (.OK (Tunneling.tunnel_program p))
  let p11 := bindIORes p10 fun p =>
    pure (Linearize.transf_program enumerationService p)
  let p12 := bindIORes p11 fun p =>
    pure (.OK (CleanupLabels.transf_program p))
  let p13 := bindIORes p12 fun p =>
    if CompCert4Lean.Driver.Compopts.debug cfg then
      pure (Debugvar.transf_program cfg p)
    else
      pure (.OK p)
  let p14 := bindIORes p13 fun p =>
    match Stacking.transf_program cfg p with
    | .Error message => pure (.Error message)
    | .OK tp => emitResult sink.mach tp
  bindIORes p14 fun p => pure (Asmgen.transf_program p)

def transf_cminor_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (sink : DiagnosticSink)
    (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Cminor.program) : IO (Res Asm.program) :=
  let p0 : IO (Res Cminor.program) := emitResult sink.cminor p
  let p1 := bindIORes p0 fun p =>
    pure (Selection.sel_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      cfg selectionOracle p)
  let p2 := bindIORes p1 fun p => pure (RTLgen.transl_program p)
  bindIORes p2 fun p =>
    transf_rtl_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      sink cfg inlineCfg regallocOracle enumerationService p

def transf_clight_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (sink : DiagnosticSink)
    (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (p : Clight.program) : IO (Res Asm.program) :=
  let p0 : IO (Res Clight.program) := emitResult sink.clight p
  let p1 := bindIORes p0 fun p => pure (SimplLocals.transf_program cfg p)
  let p2 := bindIORes p1 fun p => pure (Cshmgen.transl_program p)
  let p3 := bindIORes p2 fun p => pure (Cminorgen.transl_program p)
  bindIORes p3 fun p =>
    transf_cminor_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate)
      (binary64_inverse_certificate := binary64_inverse_certificate)
      (binary32_inverse_certificate := binary32_inverse_certificate)
      sink cfg selectionOracle inlineCfg regallocOracle enumerationService p

def transf_c_program
    [binary64_certificate : BinaryNormalizeCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_certificate : BinaryNormalizeCertificate (zOfNat 24) (zOfNat 128)]
    [binary64_inverse_certificate : BexactInverseCertificate (zOfNat 53) (zOfNat 1024)]
    [binary32_inverse_certificate : BexactInverseCertificate (zOfNat 24) (zOfNat 128)]
    (sink : DiagnosticSink)
    (cfg : CompilerConfig) (selectionOracle : Selection.SelectionOracle)
    (inlineCfg : Inlining.InliningConfig)
    (regallocOracle : Allocation.RegallocOracle)
    (enumerationService : Linearize.EnumerationService)
    (ctx : SimplExpr.FreshIdentContext)
    (p : Csyntax.program) : IO (Res Asm.program) :=
  match SimplExpr.transl_program
      (binary64_certificate := binary64_certificate)
      (binary32_certificate := binary32_certificate) ctx p with
  | .Error message => pure (.Error message)
  | .OK tp =>
      transf_clight_program
        (binary64_certificate := binary64_certificate)
        (binary32_certificate := binary32_certificate)
        (binary64_inverse_certificate := binary64_inverse_certificate)
        (binary32_inverse_certificate := binary32_inverse_certificate)
        sink cfg selectionOracle inlineCfg regallocOracle enumerationService tp

end CompCert4Lean.Driver.Diagnostics
