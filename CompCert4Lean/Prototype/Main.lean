import CompCert4Lean.Prototype.Codecs
import CompCert4Lean.Prototype.Services

namespace CompCert4Lean.Prototype

open Lean Foundation.Numbers.Rocq.Coq

def formatVersion := "compcert4lean-prototype-v2"
def codecFuel := 4096

def getField (value : Json) (name : String) : CodecResult Json := value.getObjVal? name

def exactFields (value : Json) (names : List String) : CodecResult Unit := do
  let object ← value.getObj?
  unless object.size == names.length && names.all (fun name => (value.getObjVal? name).isOk) do
    throw "invalid configuration fields"

def decodeLinkage (value : Json) : CodecResult Config.SymbolLinkageFacts := do
  exactFields value ["storage", "definedHere", "size"]
  let storage ← match ← (← getField value "storage").getStr? with
    | "default" => pure Config.StorageClass.storageDefault
    | "extern" => pure Config.StorageClass.storageExtern
    | "static" => pure Config.StorageClass.storageStatic
    | _ => throw "invalid symbol storage"
  let definedHere ← (← getField value "definedHere").getBool?
  let size ← decOption (fun value => do
    let number ← decimal value
    unless number >= 0 && number < (2 : Int)^63 do throw "invalid symbol size"
    return Int64.ofInt number) (← getField value "size")
  return { storage, definedHere, size }

def decodeConfiguration (value : Json) : CodecResult Config.CompilerConfig := do
  let version ← (← getField value "format").getStr?
  if version == "compcert4lean-prototype-v1" then
    if (value.getObjVal? "configuration").isOk then throw "legacy input cannot specify configuration"
    return cfg
  unless version == formatVersion do throw "unsupported interchange version"
  let config ← getField value "configuration"
  exactFields config ["pic", "pie", "common", "symbols"]
  let pic ← (← getField config "pic").getBool?
  let pie ← (← getField config "pie").getBool?
  if pie then throw "PIE is not supported by this profile"
  let common ← (← getField config "common").getBool?
  let symbols ← decList (decPair (dec_pos codecFuel) decodeLinkage) (← getField config "symbols")
  let identifiers := symbols.map Prod.fst
  unless identifiers.eraseDups.length == identifiers.length do throw "duplicate symbol linkage"
  let fresh ← dec_pos codecFuel (← getField value "fresh")
  unless identifiers.all (fun identifier => PArith.BinPos.Pos.to_nat identifier < PArith.BinPos.Pos.to_nat fresh) do
    throw "symbol linkage exceeds fresh identifier boundary"
  let relocation : Config.RelocationContext :=
    { pic := pic
      pie := pie
      common := common
      facts := fun identifier => (symbols.find? (fun pair => pair.1 == identifier)).map Prod.snd }
  return { cfg with relocation := relocation }

def decodeSource (value : Json) : CodecResult (Cfrontend.Csyntax.program × Cfrontend.SimplExpr.FreshIdentContext) := do
  let _ ← decodeConfiguration value
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

def encodeTarget (input : Json) (target : X86.Asm.program) : CodecResult Json := do
  let configuration := match input.getObjVal? "configuration" with
    | .ok config => [("configuration", config)]
    | .error _ => []
  return Json.mkObj ([("format", ← getField input "format"), ("target", .str "x86_64-linux-sysv-O0"),
    ("allocator", .str "spill"), ("program", ← enc_AProgram codecFuel target)] ++ configuration)

def compileJson (value : Json) : CodecResult Json := do
  let (source, fresh) ← decodeSource value
  let configuration ← decodeConfiguration value
  match Driver.Compiler.transf_c_program configuration selectionOracle inlineCfg
      (spillAllocator configuration) enumeration fresh source with
  | .Error errors => throw ("Lean compiler: " ++ errorText errors)
  | .OK target => encodeTarget value target

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
