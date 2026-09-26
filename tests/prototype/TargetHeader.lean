import CompCert4Lean.Prototype.Main

open Lean CompCert4Lean CompCert4Lean.Prototype

namespace TargetHeaderTest

theorem encodeHeader_eq (input : Json) (target : X86.Asm.program) :
    encodeHeader (targetHeader input) target = encodeTarget input target := by
  rfl

def originalCompileJson (value : Json) : CodecResult Json := do
  let (source, fresh) ← decodeSource value
  let configuration ← decodeConfiguration value
  let allocationContext ← decodeAllocationContext value
  let inlining ← decodeInlining value
  match Driver.Compiler.transf_c_program configuration (selectionFor configuration) inlining
      (Allocator.regalloc configuration allocationContext) enumeration fresh source with
  | .Error errors => throw ("Lean compiler: " ++ errorText errors)
  | .OK target => encodeTarget value target

theorem compileJson_eq (value : Json) : compileJson value = originalCompileJson value := by
  rfl

#print axioms encodeHeader_eq
#print axioms compileJson_eq

end TargetHeaderTest
