"""Generate explicit, typed codecs from the pinned extraction interfaces.

The allowlist below defines the prototype boundary. No OCaml runtime object
inspection or Lean replacement declarations are used. Generated files remain
reviewable; both compilers type-check every constructor and field.
"""

import argparse
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[1]
MODULES = {
    "AST": "Common.AST", "Ctypes": "Cfrontend.Ctypes",
    "Cop": "Cfrontend.Cop", "Csyntax": "Cfrontend.Csyntax",
    "Values": "Common.Values", "Asm": "X86.Asm",
}
SELECT = {
    "AST": "typ xtype calling_convention signature memory_chunk init_data external_function",
    "Ctypes": "signedness intsize floatsize attr coq_type struct_or_union member composite_definition bitfield",
    "Cop": "unary_operation binary_operation incr_or_decr",
    "Values": "coq_val",
    "Csyntax": "expr exprlist statement labeled_statements coq_function",
    "Asm": "ireg freg crbit preg addrmode testcond instruction coq_function",
}
PRIMITIVES = {
    "bool": ("bool", "Bool"), "unit": ("unit", "Unit"),
    "coq_Z": ("z", "Z"), "coq_N": ("n", "N"),
    "positive": ("pos", "positive"), "ident": ("pos", "positive"),
    "label": ("pos", "positive"), "block": ("pos", "positive"),
    "Int.int": ("int", "Lib.Integers.int"),
    "Int64.int": ("long", "Lib.Integers.int64"),
    "Ptrofs.int": ("ptr", "Lib.Integers.ptrofs"),
    "float": ("float", "Lib.Floats.float"), "float32": ("single", "Lib.Floats.float32"),
    "string": ("string", "RocqString"),
}


def split_outer(text, separator):
    depth = 0
    start = 0
    result = []
    for index, char in enumerate(text):
        depth += char == "("
        depth -= char == ")"
        if char == separator and depth == 0:
            result.append(text[start:index].strip())
            start = index + 1
    result.append(text[start:].strip())
    return result


def parse_decoder(block):
    name = re.match(r"def (dec_\w+) :", block)[1]
    cases = re.findall(r'    \| \[\.str "([^"]+)"([^\n]*)\] =>\n(      return [^\n]+)', block)
    if not cases:
        raise RuntimeError("no constructor cases: " + name)
    result = []
    for tag, args, body in cases:
        names = [part.strip() for part in args.split(",") if part.strip()]
        result.append((tag, names, body.strip()))
    error = re.search(r'    \| _ => throw "([^"]+)"', block)[1]
    return name, result, error


def transform(block):
    name, cases, error = parse_decoder(block)
    prefix = block[:block.index("    match ← fields value with")]
    lines = [prefix.rstrip(), "    let values ← value.getArr?"]
    arities = sorted({len(args) + 1 for _, args, _ in cases})
    for index, arity in enumerate(arities):
        lines.append(f"    {'if' if index == 0 else 'else if'} size : values.size = {arity} then")
        lines.append("      match values[0] with")
        for tag, args, body in cases:
            if len(args) + 1 != arity:
                continue
            for offset, arg in enumerate(args, 1):
                body = re.sub(r"\b" + re.escape(arg) + r"\b", f"values[{offset}]", body)
            lines += [f'      | .str "{tag}" =>', "        " + body]
        lines.append(f'      | _ => throw "{error}"')
    lines.append(f'    else throw "{error}"')
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compcert-root", type=Path, default=REPO.parent / "CompCert")
    parser.add_argument("--patch", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "-C", str(args.compcert_root), "rev-parse", "HEAD"], text=True).strip()
    if revision != "7b1f02b09954b9b916eb2a91d283c9b5355bf172":
        raise ValueError("codec generation requires the pinned CompCert revision")
    schemas = {}
    for module, names in SELECT.items():
        source = (args.compcert_root / "extraction" / (module + ".mli")).read_text()
        for name in names.split():
            match = re.search(r"^(?:type|and) " + name + r" =\s*([\s\S]*?)(?=\n(?:type|and|val|module|open) |\Z)", source, re.M)
            if not match:
                raise ValueError((module, name))
            body = " ".join(match[1].split())
            key = module + "_" + name
            lean_name = {"coq_type": "type", "coq_val": "val", "coq_function": "function"}.get(name, name)
            schema = {"module": module, "ocaml": module + "." + name,
                      "lean": MODULES[module] + "." + lean_name}
            if body.startswith("{"):
                schema["fields"] = [tuple(part.strip().split(" : ", 1)) for part in body[1:-1].split(";") if part.strip()]
            else:
                schema["variants"] = [(part.split(" of ", 1)[0], split_outer(part.split(" of ", 1)[1], "*") if " of " in part else [])
                                      for part in body.split(" | ") if part.strip(" |") for part in [part.strip(" |")]]
            schemas[key] = schema

    def add_variant(key, module, ocaml_type, lean_type, variants):
        schemas[key] = {"module": module, "ocaml": ocaml_type, "lean": lean_type, "variants": variants}

    def add_record(key, module, ocaml_type, lean_type, fields):
        schemas[key] = {"module": module, "ocaml": ocaml_type, "lean": lean_type, "fields": fields}

    for prefix, module, function_type, variable_type in [
        ("C", "Ctypes", "Csyntax_coq_function", "Ctypes_coq_type"),
        ("A", "AST", "Asm_coq_function", "unit"),
    ]:
        add_variant(prefix + "Fundef", module, schemas[function_type]["ocaml"] + " " + module + ".fundef",
                    MODULES[module] + ".fundef (" + schemas[function_type]["lean"] + ")",
                    [("Internal", [function_type]), ("External", ["AST_external_function", "Ctypes_coq_type list", "Ctypes_coq_type", "AST_calling_convention"] if prefix == "C" else ["AST_external_function"])])
        lean_var = schemas[variable_type]["lean"] if prefix == "C" else "Unit"
        ocaml_var = schemas[variable_type]["ocaml"] if prefix == "C" else "unit"
        add_record(prefix + "Globvar", "AST", ocaml_var + " AST.globvar", "Common.AST.globvar (" + lean_var + ")",
                   [("gvar_info", variable_type), ("gvar_init", "AST_init_data list"), ("gvar_readonly", "bool"), ("gvar_volatile", "bool")])
        add_variant(prefix + "Globdef", "AST", "(" + schemas[prefix + "Fundef"]["ocaml"] + ", " + ocaml_var + ") AST.globdef",
                    "Common.AST.globdef (" + schemas[prefix + "Fundef"]["lean"] + ") (" + lean_var + ")",
                    [("Gfun", [prefix + "Fundef"]), ("Gvar", [prefix + "Globvar"])])
    add_record("AProgram", "AST", "Asm.program", "X86.Asm.program",
               [("prog_defs", "(ident * AGlobdef) list"), ("prog_public", "ident list"), ("prog_main", "ident")])
    source = (args.compcert_root / "extraction/AST.mli").read_text()
    for kind in ["builtin_arg", "builtin_res"]:
        body = re.search(r"type 'a " + kind + r" =\s*([\s\S]*?)(?=\n(?:type|val) )", source)[1]
        body = " ".join(body.split()).replace("'a " + kind, "A_" + kind).replace("'a", "Asm_preg")
        add_variant("A_" + kind, "AST", "Asm.preg AST." + kind, "Common.AST." + kind + " X86.Asm.preg",
                    [(part.split(" of ", 1)[0], split_outer(part.split(" of ", 1)[1], "*") if " of " in part else [])
                     for part in body.split(" | ") for part in [part.strip(" |")]])

    def resolve(text, module):
        text = text.strip()
        if text == "members":
            return ("List", "Ctypes_member")
        if text.endswith(" list"):
            return ("List", resolve(text[:-5], module))
        if text.endswith(" option"):
            return ("Option", resolve(text[:-7], module))
        if text.endswith(" sum"):
            parts = split_outer(text[:-4].strip()[1:-1], ",")
            return ("Sum", *(resolve(part, module) for part in parts))
        parts = split_outer(text, "*")
        if len(parts) == 2:
            return ("Pair", *(resolve(part, module) for part in parts))
        if text.startswith("(") and text.endswith(")"):
            parts = split_outer(text[1:-1], "*")
            if len(parts) != 2:
                raise ValueError(text)
            return ("Pair", *(resolve(part, module) for part in parts))
        if text in ("preg builtin_arg", "preg builtin_res"):
            return "A_" + text.split()[1]
        if text == "code":
            return ("List", "Asm_instruction")
        if text in PRIMITIVES or text in schemas:
            return text
        if module + "_" + text in schemas:
            return module + "_" + text
        candidates = [key for key in schemas if key.endswith("_" + text)]
        if len(candidates) == 1:
            return candidates[0]
        raise ValueError((module, text, candidates))

    def call(shape, language, direction):
        if isinstance(shape, tuple):
            kind, *children = shape
            name = direction + (kind if language == "lean" else "_" + kind.lower())
            return "(" + name + " " + " ".join(call(child, language, direction) for child in children) + ")"
        name = PRIMITIVES[shape][0] if shape in PRIMITIVES else shape
        return "(" + direction + "_" + name + (" fuel" if language == "lean" else "") + ")"

    lean = ["import CompCert4Lean.Prototype.Json", "", "namespace CompCert4Lean.Prototype", "open Lean Foundation.Numbers.Rocq.Coq", "set_option maxRecDepth 4096", "set_option maxHeartbeats 0", ""]
    ocaml = ["open Primitives", ""]
    for direction in ["enc", "dec"]:
        lean.append("mutual")
        for index, (key, schema) in enumerate(schemas.items()):
            typename = schema["lean"]
            lean.append(f"def {direction}_{key} : Nat → " + (f"{typename} → CodecResult Json" if direction == "enc" else f"Json → CodecResult ({typename})"))
            lean.append('  | 0, _ => throw "interchange depth exceeded"')
            lean.append("  | fuel + 1, value => do")
            if direction == "dec":
                lean.append("    match ← fields value with")
            elif "variants" in schema:
                lean.append("    match value with")
            ocaml.append(("let rec " if index == 0 else "and ") + direction + "_" + key + (" (value : " + schema["ocaml"] + ") =" if direction == "enc" else " value : " + schema["ocaml"] + " ="))
            if direction == "dec" or "variants" in schema:
                ocaml.append("  match value with")
            cases = schema.get("variants", [(key, [field_type for _, field_type in schema["fields"]])] if "fields" in schema else [])
            for tag, field_types in cases:
                variables = ["arg" + str(number) for number in range(len(field_types))]
                shapes = [resolve(field_type, schema["module"]) for field_type in field_types]
                if direction == "enc":
                    lean_values = variables if "variants" in schema else ["value." + name for name, _ in schema["fields"]]
                    ocaml_values = variables if "variants" in schema else ["value." + name for name, _ in schema["fields"]]
                    lean_prefix = "    | ." + tag + (" " + " ".join(variables) if variables else "") + " => " if "variants" in schema else "    "
                    if "variants" in schema:
                        ocaml.append("  | " + schema["module"] + "." + tag + (" (" + ", ".join(variables) + ")" if variables else "") + " ->")
                    lean.append(lean_prefix + "return node " + repr(tag).replace("'", '"') + " [" + ", ".join("← " + call(shape, "lean", direction) + " " + value for shape, value in zip(shapes, lean_values)) + "]")
                    ocaml.append('    node "' + tag + '" [' + "; ".join(call(shape, "ocaml", direction) + " " + value for shape, value in zip(shapes, ocaml_values)) + "]")
                else:
                    lean_args = ["(← " + call(shape, "lean", direction) + " " + value + ")" for shape, value in zip(shapes, variables)]
                    ocaml_args = [call(shape, "ocaml", direction) + " " + value for shape, value in zip(shapes, variables)]
                    lean.append('    | [.str "' + tag + '"' + (", " + ", ".join(variables) if variables else "") + "] =>")
                    ocaml.append('  | `List [`String "' + tag + '"' + ("; " + "; ".join(variables) if variables else "") + "] ->")
                    if "variants" in schema:
                        lean.append("      return ." + tag + (" " + " ".join(lean_args) if lean_args else ""))
                        ocaml.append("    " + schema["module"] + "." + tag + (" (" + ", ".join(ocaml_args) + ")" if ocaml_args else ""))
                    else:
                        lean.append("      return { " + ", ".join(name + " := " + value for (name, _), value in zip(schema["fields"], lean_args)) + " }")
                        ocaml.append("    { " + "; ".join(name + " = " + value for (name, _), value in zip(schema["fields"], ocaml_args)) + " }")
            if direction == "dec":
                lean.append('    | _ => throw "invalid ' + key + ' constructor or arity"')
                ocaml.append('  | _ -> failwith "invalid ' + key + ' constructor or arity"')
            lean.append("")
            ocaml.append("")
        lean.append("end\n")
    lean.append("end CompCert4Lean.Prototype\n")
    lean_text = "\n".join(lean)
    decoder_block = lean_text.split("mutual\n")[2].split("\nend\n", 1)[0]
    blocks = re.split(r"\n(?=def dec_)", decoder_block.strip())
    indexed_names = set(['dec_AST_calling_convention', 'dec_AST_external_function', 'dec_AST_init_data', 'dec_AST_memory_chunk', 'dec_AST_signature', 'dec_AST_typ', 'dec_AST_xtype', 'dec_CFundef', 'dec_CGlobdef', 'dec_CGlobvar', 'dec_Cop_binary_operation', 'dec_Cop_incr_or_decr', 'dec_Cop_unary_operation', 'dec_Csyntax_coq_function', 'dec_Csyntax_expr', 'dec_Csyntax_exprlist', 'dec_Csyntax_labeled_statements', 'dec_Csyntax_statement', 'dec_Ctypes_attr', 'dec_Ctypes_bitfield', 'dec_Ctypes_composite_definition', 'dec_Ctypes_coq_type', 'dec_Ctypes_floatsize', 'dec_Ctypes_intsize', 'dec_Ctypes_member', 'dec_Ctypes_signedness', 'dec_Ctypes_struct_or_union', 'dec_Values_coq_val'])
    indexed_block = "\n\n".join(transform(block) if parse_decoder(block)[0] in indexed_names
                                  else block.rstrip() for block in blocks) + "\n"
    lean_text = lean_text.replace(decoder_block, indexed_block, 1)
    outputs = {"CompCert4Lean/Prototype/Codecs.lean": lean_text, "bridge/codecs.ml": "\n".join(ocaml)}
    if args.check:
        for name, content in outputs.items():
            if (REPO / name).read_text() != content.rstrip("\n") + "\n":
                raise ValueError("generated codec differs: " + name)
        print("Generated codecs match pinned interfaces")
    elif args.patch:
        print("*** Begin Patch")
        for name, content in outputs.items():
            print("*** Add File: compcert4lean/" + name)
            print("\n".join("+" + line for line in content.splitlines()))
        print("*** End Patch")
    else:
        for name, content in outputs.items():
            (REPO / name).write_text(content.rstrip("\n") + "\n")


if __name__ == "__main__":
    main()
