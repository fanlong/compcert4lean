"""Small, reproducible allocation comparison with the pinned O0 compiler."""

import json
from pathlib import Path
import re
import sys
import tempfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, LEAN, REFERENCE_FLAGS, REPO, compile_source, execute, prepare, tool_environment


def reference_metrics(dump):
    registers = r"(?:[er](?:ax|bx|cx|dx|si|di|bp)|r(?:[89]|1[0-5])|xmm(?:[0-9]|1[0-5])|st0)"
    widths = {"int": 1, "long": 2, "float": 2, "single": 1, "any32": 1, "any64": 2}
    slots = re.findall(r"local\((\d+),(\w+)\)", dump)
    return {
        "spills": len(re.findall(r"local\(\d+,\w+\)\s*=", dump)),
        "reloads": len(re.findall(r"=\s*local\(\d+,\w+\)", dump)),
        "moves": len(re.findall(registers + r"\s*=\s*" + registers + r"(?=\s*(?:;|\n))", dump, re.I)),
        "stackWords": max((int(offset) + widths[kind] for offset, kind in slots), default=0),
    }


def main():
    root = REPO.parent / "CompCert"
    versions = prepare(root)
    folder = Path(tempfile.mkdtemp(prefix="allocator-comparison-", dir=BUILD))
    print(f"Artifacts: {folder}", flush=True)
    fixtures = {"copy": "int copy(int a){int b=a; int c=b; int d=c; return d;}\n",
                "calls": "extern int opaque(int); int across(int a, int b){int c=opaque(a); return a+b+c;}\n"}
    for name, type_name in [("pressure", "int"), ("floating", "double")]:
        fixtures[name] = (f"extern volatile {type_name} values[24]; {type_name} sum(void){{" +
                          "".join(f"{type_name} value{index}=values[{index}];" for index in range(24)) +
                          "return " + "+".join(f"value{index}" for index in range(24)) + ";}\n")
    comparisons = []
    for name, source_text in fixtures.items():
        case = folder / name
        case.mkdir()
        source = case / (name + ".c")
        source.write_text(source_text)
        started = time.monotonic()
        compile_source(parse_args([str(source), "-S", "-o", str(case / "lean.s")]),
                       prepared=True, artifact_dir=case / "lean", timeout=300)
        lean_seconds = time.monotonic() - started
        execute([LEAN, "--allocator-report", case / "lean/csyntax.json", case / "allocation.json"], timeout=30)
        functions = json.loads((case / "allocation.json").read_text())
        metrics = {field: sum(function[field] for function in functions)
                   for field in ["spills", "reloads", "moves"]}
        metrics["stackWords"] = max((function["stackWords"] for function in functions), default=0)
        started = time.monotonic()
        execute([root / "ccomp", "-stdlib", root / "runtime", *REFERENCE_FLAGS, "-dltl", "-S",
                 source, "-o", case / "reference.s"], env=tool_environment(root), cwd=case, timeout=300,
                log=case / "reference-command")
        reference_seconds = time.monotonic() - started
        dumps = list(case.glob("*.ltl"))
        if len(dumps) != 1:
            raise RuntimeError("missing or ambiguous CompCert LTL dump")
        reference = reference_metrics(dumps[0].read_text())
        comparisons.append({"fixture": name, "lean": {"seconds": lean_seconds, **metrics},
                            "compcert": {"seconds": reference_seconds, **reference}, "functions": functions})
    summary = {"versions": versions, "comparisons": comparisons,
               "measurement": "Single warm compilation to assembly, including frontend and bridge; no build time. "
                              "Spills/reloads count Local LTL stores/loads, moves count LTL Omove, "
                              "stackWords is the largest per-function local slot extent in four-byte words."}
    (folder / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(comparisons, indent=2))


if __name__ == "__main__":
    main()
