import CompCert4Lean.Prototype.Codecs
import CompCert4Lean.Prototype.Services

namespace CompCert4Lean.Prototype

open Lean Foundation.Numbers.Rocq.Coq

def formatVersion := "compcert4lean-prototype-v1"
def codecFuel := 4096

def getField (value : Json) (name : String) : CodecResult Json := value.getObjVal? name

def decodeSource (value : Json) : CodecResult (Cfrontend.Csyntax.program × Cfrontend.SimplExpr.FreshIdentContext) := do
  unless (← (← getField value "format").getStr?) == formatVersion do
    throw "unsupported interchange version"
  unless (← (← getField value "target").getStr?) == "x86_64-linux-sysv-O0" do
    throw "unsupported target configuration"
  let fresh ← dec_pos codecFuel (← getField value "fresh")
  let definitions ← decList (decPair (dec_pos codecFuel) (dec_CGlobdef codecFuel)) (← getField value "definitions")
  let publicSymbols ← decList (dec_pos codecFuel) (← getField value "public")
  let mainIdent ← dec_pos codecFuel (← getField value "main")
  let types ← decList (dec_Ctypes_composite_definition codecFuel) (← getField value "composites")
  match built : Cfrontend.Ctypes.build_composite_env types with
  | .Error errors => throw ("composite environment: " ++ errorText errors)
  | .OK environment =>
      return ({ prog_defs := definitions, prog_public := publicSymbols, prog_main := mainIdent,
                prog_types := types, prog_comp_env := environment, prog_comp_env_eq := built },
              ⟨.sequential fresh⟩)

def encodeTarget (target : X86.Asm.program) : CodecResult Json := do
  return Json.mkObj [("format", .str formatVersion), ("target", .str "x86_64-linux-sysv-O0"),
    ("allocator", .str "spill"), ("program", ← enc_AProgram codecFuel target)]

def compileJson (value : Json) : CodecResult Json := do
  let (source, fresh) ← decodeSource value
  match Driver.Compiler.transf_c_program cfg selectionOracle inlineCfg
      (spillAllocator cfg) enumeration fresh source with
  | .Error errors => throw ("Lean compiler: " ++ errorText errors)
  | .OK target => encodeTarget target

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--test-invalid-allocation", input] =>
      let text ← IO.FS.readFile input
      let result := do
        let (source, fresh) ← Json.parse text >>= decodeSource
        let corrupt : Backend.Allocation.RegallocOracle := fun function => do
          let proposed ← spillAllocator cfg function
          .OK { proposed with fn_stacksize := ZArith.BinInt.Z.add function.fn_stacksize (z 1) }
        match Driver.Compiler.transf_c_program cfg selectionOracle inlineCfg corrupt enumeration fresh source with
        | .Error errors => throw (errorText errors)
        | .OK _ => pure ()
      match result with
      | .error message => (← IO.getStderr).putStrLn message; return 1
      | .ok () => return 0
  | ["--test-codecs"] =>
      let result : CodecResult Unit := do
        for bits in ["0", "9223372036854775808", "9218868437227405312", "9221120237041090561", "18446744073709551615"] do
          let encoded ← enc_float codecFuel (← dec_float codecFuel (.str bits))
          unless encoded == .str bits do throw ("float bits changed: " ++ bits)
        for bits in ["0", "2147483648", "2139095040", "2143289345", "4294967295"] do
          let encoded ← enc_single codecFuel (← dec_single codecFuel (.str bits))
          unless encoded == .str bits do throw ("single bits changed: " ++ bits)
        let identifier := "18446744073709551616000000000001"
        unless (← enc_pos codecFuel (← dec_pos codecFuel (.str identifier))) == .str identifier do
          throw "identifier bits changed"
      match result with
      | .error message => (← IO.getStderr).putStrLn message; return 1
      | .ok () => return 0
  | [input, output] =>
      let text ← IO.FS.readFile input
      match Json.parse text >>= compileJson with
      | .error message =>
          (← IO.getStderr).putStrLn message
          return 1
      | .ok value =>
          IO.FS.writeFile output (value.compress ++ "\n")
          return 0
  | _ =>
      (← IO.getStderr).putStrLn "usage: leanCompiler input.json output.json"
      return 2

end CompCert4Lean.Prototype

def main (args : List String) : IO UInt32 := do
  try CompCert4Lean.Prototype.run args
  catch error =>
    (← IO.getStderr).putStrLn ("leanCompiler: " ++ error.toString)
    return 1
