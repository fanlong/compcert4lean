import CompCert4Lean.Common.Events.Core

/-!
# External-call providers

The proof-bearing environment replacing CompCert's global external-function
and inline-assembly assumptions.  Executable adapters belong to the deferred
executor provider, not this module.
-/

namespace CompCert4Lean.Common.ExternalCalls

structure ExternalFunctionsProvider where
  sem :
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string →
      CompCert4Lean.Common.AST.signature →
      CompCert4Lean.Common.Events.extcall_sem
  properties : ∀ name sg,
    CompCert4Lean.Common.Events.extcall_properties (sem name sg) sg

structure InlineAssemblyProvider where
  sem :
    CompCert4Lean.Foundation.RocqString.Rocq.Coq.Strings.String.string →
      CompCert4Lean.Common.AST.signature →
      CompCert4Lean.Common.Events.extcall_sem
  properties : ∀ text sg,
    CompCert4Lean.Common.Events.extcall_properties (sem text sg) sg

structure ExternalCalls where
  external : ExternalFunctionsProvider
  inlineAssembly : InlineAssemblyProvider

end CompCert4Lean.Common.ExternalCalls
