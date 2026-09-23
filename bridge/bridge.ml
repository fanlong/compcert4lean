open Primitives
open Codecs

let format_version = "compcert4lean-prototype-v2"
let member name value = Yojson.Basic.Util.member name value
let text name value = Yojson.Basic.Util.to_string (member name value)

let language_options = [
  "longdouble", Clflags.option_flongdouble;
  "struct-passing", Clflags.option_fstruct_passing;
  "vararg-calls", Clflags.option_fvararg_calls;
  "unprototyped", Clflags.option_funprototyped;
  "packed-structs", Clflags.option_fpacked_structs;
  "unstructured-switch", Clflags.option_funstructured_switch;
  "inline-asm", Clflags.option_finline_asm]

let configure request =
  let root = text "root" request in
  if Configuration.arch <> "x86" || Configuration.model <> "64" ||
     Configuration.abi <> "standard" || Configuration.system <> "linux" ||
     Configuration.is_big_endian then failwith "expected System V x86-64 Linux CompCert";
  Clflags.stdlib_path := Filename.concat root "runtime";
  Clflags.option_fpic := false;
  Clflags.option_fpie := false;
  Clflags.option_fcommon := false;
  (match member "configuration" request with
   | `Null -> ()
   | `Assoc fields as config ->
       if List.sort compare (List.map fst fields) <> ["common"; "pic"; "pie"]
       then failwith "invalid configuration fields";
       Clflags.option_fpic := Yojson.Basic.Util.to_bool (member "pic" config);
       Clflags.option_fcommon := Yojson.Basic.Util.to_bool (member "common" config);
       if Yojson.Basic.Util.to_bool (member "pie" config)
       then failwith "PIE is not supported by this profile"
   | _ -> failwith "invalid configuration");
  (match member "language" request with
   | `Null -> ()
   | flags -> List.iter (fun flag ->
       let flag = Yojson.Basic.Util.to_string flag in
       if flag = "-fall" || flag = "-fnone" then
         List.iter (fun (_, setting) -> setting := (flag = "-fall")) language_options
       else
         let enabled = not (String.starts_with ~prefix:"-fno-" flag) in
         let prefix = if enabled then "-f" else "-fno-" in
         if not (String.starts_with ~prefix flag) then failwith "invalid language option";
         let name = String.sub flag (String.length prefix) (String.length flag - String.length prefix) in
         (List.assoc name language_options) := enabled)
       (Yojson.Basic.Util.to_list flags));
  Clflags.option_ffloatconstprop := 0;
  Clflags.option_ftailcalls := false;
  Clflags.option_fconstprop := false;
  Clflags.option_fcse := false;
  Clflags.option_fredundancy := false;
  Clflags.option_fifconversion := false;
  Clflags.option_finline := false;
  Clflags.option_finline_functions_called_once := false;
  Clflags.option_g := false;
  Camlcoq.use_canonical_atoms := false;
  Frontend.init ()

let configuration_json () =
  let symbols = Hashtbl.fold (fun identifier facts result ->
    let storage = match facts.C2C.a_storage with
      | C.Storage_default -> "default"
      | C.Storage_extern -> "extern"
      | C.Storage_static -> "static"
      | _ -> failwith "unsupported global storage class" in
    (identifier, `List [enc_pos identifier; `Assoc [
      "storage", `String storage;
      "definedHere", `Bool facts.C2C.a_defined;
      "size", (match facts.C2C.a_size with None -> `Null | Some size -> `String (Int64.to_string size))]]) :: result)
    C2C.decl_atom [] in
  `Assoc ["pic", `Bool !Clflags.option_fpic; "pie", `Bool false;
          "common", `Bool !Clflags.option_fcommon;
          "symbols", `List (List.map snd (List.sort (fun (left, _) (right, _) -> compare left right) symbols))]

let source_json configuration (source : Csyntax.program) =
  `Assoc ["format", `String format_version;
          "target", `String "x86_64-linux-sysv-O0";
          "configuration", configuration;
          "fresh", enc_pos (Camlcoq.first_unused_ident ());
          "definitions", enc_list (enc_pair enc_pos enc_CGlobdef) source.prog_defs;
          "public", enc_list enc_pos source.prog_public;
          "main", enc_pos source.prog_main;
          "composites", enc_list enc_Ctypes_composite_definition source.prog_types]

let print_assembly configuration input output =
  let data = Yojson.Basic.from_file input in
  let version = text "format" data in
  if (version <> format_version && version <> "compcert4lean-prototype-v1") ||
     text "target" data <> "x86_64-linux-sysv-O0"
  then failwith "unsupported assembly interchange version/target";
  let compatible =
    if version = format_version then Yojson.Basic.equal (member "configuration" data) configuration
    else member "configuration" data = `Null &&
         not !Clflags.option_fpic && not !Clflags.option_fpie && not !Clflags.option_fcommon in
  if not compatible then
    failwith "inconsistent assembly relocation configuration";
  let program = dec_AProgram (member "program" data) in
  match Asmexpand.expand_program program with
  | Errors.Error errors ->
      Format.eprintf "%a@." Driveraux.print_error errors;
      failwith "assembly expansion failed"
  | Errors.OK expanded ->
      let channel = open_out output in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> PrintAsm.print_program channel expanded)

let respond fields =
  Yojson.Basic.to_channel stdout (`Assoc (("ok", `Bool true) :: fields));
  output_char stdout '\n'; flush stdout

let run () =
  let request = Yojson.Basic.from_string (read_line ()) in
  configure request;
  Clflags.prepro_options := List.rev (dec_list Yojson.Basic.Util.to_string (member "preprocessor" request));
  let input = text "source" request in
  let preprocessed = text "preprocessed" request in
  Frontend.preprocess input preprocessed;
  let source = Frontend.parse_c_file input preprocessed in
  Diagnostics.raise_on_errors ();
  let configuration = configuration_json () in
  Yojson.Basic.to_file (text "csyntax" request) (source_json configuration source);
  respond ["phase", `String "frontend"];
  let request = Yojson.Basic.from_string (read_line ()) in
  if text "operation" request <> "print" then failwith "unknown bridge operation";
  print_assembly configuration (text "input" request) (text "output" request);
  respond ["phase", `String "assembly"]

let () =
  try run () with
  | Assert_failure (file, line, _) ->
      Printf.eprintf "CompCert bridge: unsupported construct for assembly expansion/printing (%s:%d); retain asm.json\n" file line;
      exit 1
  | error ->
      prerr_endline ("CompCert bridge: " ^ Printexc.to_string error);
      exit 1
