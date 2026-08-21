import CompCert4Lean.Foundation.Numbers

/-!
# Immutable compiler configuration

The theorem-facing compiler receives one explicit configuration value.  The
pinned Linux x86-64 constructor is the only place where the reference
command-line float level is decoded into the two independent core flags.
-/

namespace CompCert4Lean.Config

inductive X86_64ABI where
  | systemV
  | windows

structure CompilerOptions where
  optimForSize : Bool
  propagateFloatConstants : Bool
  generateFloatConstants : Bool
  vaStrict : Bool
  optimTailcalls : Bool
  optimConstprop : Bool
  optimCSE : Bool
  optimRedundancy : Bool
  debug : Bool

inductive StorageClass where
  | storageDefault
  | storageExtern
  | storageStatic
deriving DecidableEq

structure SymbolLinkageFacts where
  storage : StorageClass
  definedHere : Bool
  size : Option _root_.Int64

structure RelocationContext where
  pic : Bool
  pie : Bool
  common : Bool
  facts : CompCert4Lean.Foundation.Numbers.Rocq.Coq.positive →
    Option SymbolLinkageFacts

structure CompilerConfig where
  options : CompilerOptions
  x86_64ABI : X86_64ABI
  relocation : RelocationContext

/--
Construct the immutable configuration snapshot for the pinned standard Linux
x86-64 profile.  The reference driver's integer float level has two distinct
threshold observations; the other mutable driver flags are supplied once as
ordinary Boolean data.
-/
def pinnedLinuxX86_64
    (optimForSize : Bool)
    (floatConstantPropagationLevel : Int)
    (optimTailcalls : Bool)
    (optimConstprop : Bool)
    (optimCSE : Bool)
    (optimRedundancy : Bool)
    (debug : Bool) : CompilerConfig :=
  { options :=
      { optimForSize := optimForSize
        propagateFloatConstants := decide (floatConstantPropagationLevel >= 1)
        generateFloatConstants := decide (floatConstantPropagationLevel >= 2)
        vaStrict := false
        optimTailcalls := optimTailcalls
        optimConstprop := optimConstprop
        optimCSE := optimCSE
        optimRedundancy := optimRedundancy
        debug := debug }
    x86_64ABI := .systemV
    relocation :=
      { pic := false
        pie := false
        common := false
        facts := fun _ => none } }

end CompCert4Lean.Config
