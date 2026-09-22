open Primitives
open Codecs

let format_version = "compcert4lean-prototype-v1"
let member name value = Yojson.Basic.Util.member name value
let text name value = Yojson.Basic.Util.to_string (member name value)

let configure root =
  if Configuration.arch <> "x86" || Configuration.model <> "64" ||
     Configuration.abi <> "standard" || Configuration.system <> "linux" ||
     Configuration.is_big_endian then failwith "expected System V x86-64 Linux CompCert";
  Clflags.stdlib_path := Filename.concat root "runtime";
  Clflags.option_fpic := false;
  Clflags.option_fpie := false;
  Clflags.option_fcommon := false;
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

let source_json (source : Csyntax.program) =
  `Assoc ["format", `String format_version;
          "target", `String "x86_64-linux-sysv-O0";
          "fresh", enc_pos (Camlcoq.first_unused_ident ());
          "definitions", enc_list (enc_pair enc_pos enc_CGlobdef) source.prog_defs;
          "public", enc_list enc_pos source.prog_public;
          "main", enc_pos source.prog_main;
          "composites", enc_list enc_Ctypes_composite_definition source.prog_types]

let print_assembly input output =
  let data = Yojson.Basic.from_file input in
  if text "format" data <> format_version || text "target" data <> "x86_64-linux-sysv-O0"
  then failwith "unsupported assembly interchange version/target";
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
  configure (text "root" request);
  Clflags.prepro_options := List.rev (dec_list Yojson.Basic.Util.to_string (member "preprocessor" request));
  let input = text "source" request in
  let preprocessed = text "preprocessed" request in
  Frontend.preprocess input preprocessed;
  let source = Frontend.parse_c_file input preprocessed in
  Diagnostics.raise_on_errors ();
  Yojson.Basic.to_file (text "csyntax" request) (source_json source);
  respond ["phase", `String "frontend"];
  let request = Yojson.Basic.from_string (read_line ()) in
  if text "operation" request <> "print" then failwith "unknown bridge operation";
  print_assembly (text "input" request) (text "output" request);
  respond ["phase", `String "assembly"]

let () =
  try run () with
  | Assert_failure (file, line, _) ->
      Printf.eprintf "CompCert bridge: unsupported construct for assembly expansion/printing (%s:%d); retain asm.json\n" file line;
      exit 1
  | error ->
      prerr_endline ("CompCert bridge: " ^ Printexc.to_string error);
      exit 1
