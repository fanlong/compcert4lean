import CompCert4Lean.Config

/-!
# Per-invocation diagnostic effects

The theorem-facing compiler callbacks are pure `Unit` definitions.  This
module owns only their executable companion: a per-invocation sink whose
callbacks may perform `IO`, while keeping the sink out of immutable compiler
configuration and the pure `Errors.Res` result.

The language program providers are translated in later work units.  The sink
therefore abstracts over their five source-shaped program types here; each
consumer instantiates those parameters with its canonical provider type.
-/

namespace CompCert4Lean.Driver.Diagnostics

universe uClight uCminor uRTL uLTL uMach

structure DiagnosticSink
    (ClightProgram : Type uClight)
    (CminorProgram : Type uCminor)
    (RTLProgram : Type uRTL)
    (LTLProgram : Type uLTL)
    (MachProgram : Type uMach) where
  clight : ClightProgram → IO Unit
  cminor : CminorProgram → IO Unit
  rtl : CompCert4Lean.Foundation.Numbers.Rocq.Coq.Z → RTLProgram → IO Unit
  ltl : LTLProgram → IO Unit
  mach : MachProgram → IO Unit

/-- The ordinary no-diagnostics sink; every callback completes with no output. -/
def DiagnosticSink.silent
    {ClightProgram : Type uClight}
    {CminorProgram : Type uCminor}
    {RTLProgram : Type uRTL}
    {LTLProgram : Type uLTL}
    {MachProgram : Type uMach} :
    DiagnosticSink ClightProgram CminorProgram RTLProgram LTLProgram MachProgram :=
  { clight := fun _ => pure ()
    cminor := fun _ => pure ()
    rtl := fun _ _ => pure ()
    ltl := fun _ => pure ()
    mach := fun _ => pure () }

end CompCert4Lean.Driver.Diagnostics
