#!/usr/bin/env python3
"""Vendor the pinned small-test tree and derive its explicit Linux x86-64 manifest."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from prototype import REPO

PIN = "081175df374260304a5cd78dd3dfaded93dceb41"
DESTINATION = REPO / "tests/small-tests"


def make_variable(directory, name):
    text = (directory / "Makefile").read_text().replace("\\\n", " ")
    match = re.search(r"^" + re.escape(name) + r"\s*=([^\n]*)", text, re.MULTILINE)
    if not match:
        raise ValueError(f"missing Makefile variable {directory.name}/{name}")
    return match[1].replace("$(ARCH)", "x86").split()


def manifest(root):
    cases = []
    exclusions = []
    def add(group, name, sources, check, flags=None, **extra):
        cases.append({"id": group + "/" + name, "group": group,
                      "sources": [group + "/" + source for source in sources],
                      "check": check, "flags": flags or [], **extra})
    regression = root / "regression"
    active = set()
    for variable, kind in [("TESTS", "stdout"), ("TESTS_COMP", "stdout"),
                           ("TESTS_DIFF", "interpreter"), ("EXTRAS", "compile")]:
        for name in make_variable(regression, variable):
            active.add(name)
            expected = next(("regression/Results/" + name + suffix for suffix in
                             ["-x86-64", "-x86", "-64", ""]
                             if (regression / "Results" / (name + suffix)).is_file()), None)
            check = {"kind": "exit" if kind == "stdout" and expected is None else kind}
            if expected:
                check["expected"] = expected
            add("regression", name, [name + ".c"], check,
                ["-fall", "-DARCH_x86", "-DMODEL_64"], upstream="regression/Makefile:" + variable,
                condition=("regression/" + name + ".cond") if (regression / (name + ".cond")).exists() else None)
    for source in sorted(regression.glob("*.c")):
        name = source.stem
        if name in active:
            continue
        reason = None
        if name.startswith("builtins-"):
            reason = "Other architecture; Linux System V x86-64 uses builtins-x86.c"
        if name in make_variable(regression, "FAILURES"):
            reason = "Frontend-only negative test: wrong argument count; upstream FAILURES, no C-AST"
        if reason:
            exclusions.append({"id": "regression/" + name, "paths": ["regression/" + source.name], "reason": reason})
            continue
        expected = "regression/Results/" + name
        check = {"kind": "stdout", "expected": expected} if (root / expected).is_file() else {"kind": "compile"}
        add("supplemental", name, [], check, ["-fall", "-DARCH_x86", "-DMODEL_64"],
            upstream="regression/Makefile: omitted source",
            annotation="upstream temporarily removed" if name in {"stringlit", "charlit"} else "omitted from active Makefile lists")
        cases[-1]["sources"] = ["regression/" + source.name]
    for name in make_variable(root / "c", "PROGS"):
        add("c", name, [name + ".c"], {"kind": "stdout", "expected": "c/Results/" + name}, upstream="c/Makefile:PROGS")
    for name in make_variable(root / "compression", "EXE"):
        objects = make_variable(root / "compression", name.upper() + "_OBJS")
        objects = [part for item in objects for part in
                   (make_variable(root / "compression", "COMMON_OBJS") if item == "$(COMMON_OBJS)" else [item])]
        add("compression", name, [str(Path(item).with_suffix(".c")) for item in objects],
            {"kind": "roundtrip", "input": "LICENSE"}, ["-U__GNUC__"],
            upstream="compression/Makefile:test (fixed input replaces host-dependent TESTFILE)")
    add("raytracer", "render", [str(Path(item).with_suffix(".c")) for item in make_variable(root / "raytracer", "OBJS")],
        {"kind": "file", "stdin": "raytracer/kal.gml", "actual": "kal.ppm", "expected": "raytracer/Results/kal.ppm"},
        ["-fstruct-passing"], upstream="raytracer/Makefile:test")
    add("spass", "small_problem", make_variable(root / "spass", "SRCS"),
        {"kind": "contains", "text": "Proof found", "args": ["small_problem.dfg"]},
        ["-fstruct-passing"], upstream="spass/Makefile:test")
    for name in ["fixed", "vararg", "struct"]:
        for variant in ["native", "gcc_to_native", "native_to_gcc"]:
            identifier = "abi/" + name + "-" + variant
            if name == "struct" and variant != "native":
                exclusions.append({"id": identifier, "paths": ["abi/Runtest"],
                                   "reason": "Upstream abi/Runtest excludes mixed struct ABI on x86-64"})
                continue
            add("abi", name + "-" + variant, [name + "_def.c", name + "_use.c"], {"kind": "exit"},
                ["-fstruct-passing"] if name == "struct" else [], variant=variant, fixture=name,
                upstream="abi/Makefile:TESTS and abi/Runtest")
    for name in ["layout", "staticlayout"]:
        add("abi", name, [name + ".c"], {"kind": "gcc_stdout"}, fixture="layout", upstream="abi/Makefile:DIFFTESTS")
    add("pic", "shared", ["lib1.c", "lib2.c", "dylib.c", "main.c"],
        {"kind": "stdout", "expected": "pic/main.reference"}, ["-fpic"], upstream="pic/Makefile:test")
    exclusions.append({"id": "export", "paths": [str(path.relative_to(root)) for path in sorted((root / "export").rglob("*")) if path.is_file()],
                       "reason": "Rocq/Clight/Csyntax export validation is outside C-AST to x86-64"})
    return {"format": "compcert4lean-small-tests-v1", "revision": PIN, "target": "x86_64-linux-sysv-O0",
            "abi": {"seed": 20260922, "random_functions": 500, "layout_count": 1000, "layout_size": 4},
            "cases": cases, "exclusions": exclusions}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    options = parser.parse_args()
    root = options.checkout.resolve()
    revision = subprocess.check_output(["git", "-C", root, "rev-parse", "HEAD"], text=True).strip()
    if revision != PIN:
        parser.error("checkout must be at " + PIN)
    files = subprocess.check_output(["git", "-C", root, "ls-tree", "-rz", PIN]).decode().split("\0")
    records = {}
    for entry in filter(None, files):
        attributes, name = entry.split("\t", 1)
        mode, kind, _ = attributes.split()
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise ValueError("unsupported upstream entry: " + name)
        content = subprocess.check_output(["git", "-C", root, "show", PIN + ":" + name])
        output = DESTINATION / name
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(content)
        output.chmod(int(mode, 8) & 0o777)
        records[name] = {"upstream": name, "sha256": hashlib.sha256(content).hexdigest(), "mode": mode}
    (DESTINATION / "provenance.json").write_text(json.dumps({"repository": "https://github.com/AbsInt/CompCert-small-tests",
        "revision": PIN, "files": records}, indent=2) + "\n")
    (DESTINATION / "manifest.json").write_text(json.dumps(manifest(DESTINATION), indent=2) + "\n")
    print(f"Imported {len(records)} pinned files into {DESTINATION}")


if __name__ == "__main__":
    main()
