import CompCert4Lean.Config

/-!
# Immutable compiler-option accessors

The source option queries are represented as pure projections from the one
immutable compiler configuration shared by executable and theorem-facing
consumers.
-/

namespace CompCert4Lean.Driver.Compopts

def optim_for_size (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.optimForSize

def propagate_float_constants (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.propagateFloatConstants

def generate_float_constants (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.generateFloatConstants

def va_strict (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.vaStrict

def optim_tailcalls (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.optimTailcalls

def optim_constprop (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.optimConstprop

def optim_CSE (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.optimCSE

def optim_redundancy (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.optimRedundancy

def debug (cfg : Config.CompilerConfig) : Bool :=
  cfg.options.debug

end CompCert4Lean.Driver.Compopts
