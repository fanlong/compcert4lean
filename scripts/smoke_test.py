#!/usr/bin/env python3
"""Run pinned upstream programs through Lean and independently through CompCert."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import time

from compile_c import parse_args as compiler_options
from prototype import ALLOCATOR, BUILD, Bridge, CompileError, LEAN, REFERENCE_FLAGS, REPO
from prototype import compile_source, execute, prepare, tool_environment
from small_tests import verify_corpus

TESTS = REPO / "tests" / "small-tests" / "regression"


def require(condition, message):
    if not condition:
        raise CompileError(message)


def expect_failure(command, log, *, timeout=120, cwd=None):
    try:
        execute(command, cwd=cwd, log=log, timeout=timeout)
    except CompileError:
        record = json.loads(Path(log).with_suffix(".json").read_text())
        require(not record["timeout"], "negative test timed out")
        return
    raise CompileError("expected command failure: " + repr(command))


def integration_checks(root, folder, compile_timeout, run_timeout):
    folder.mkdir()
    source = folder / "source with spaces.c"
    source.write_text('#include "value.h"\n#include <math.h>\nint main(void) { volatile double value = NUMBER; return (int)sqrt(value) - 3; }\n')
    include = folder / "include with spaces"
    include.mkdir()
    (include / "value.h").write_text("#ifdef REMOVE_ME\n#error -U failed\n#endif\n#ifndef NUMBER\n#error -D failed\n#endif\n")
    command = [sys.executable, REPO / "scripts/compile_c.py", source,
               "--compcert-root", root, "-I" + str(include), "-UNUMBER", "-DNUMBER=9", "-DREMOVE_ME", "-UREMOVE_ME",
               "-L" + str(folder), "-lm", "-O0", "--keep-temps"]
    for mode, suffix in [(None, ""), ("-S", ".s"), ("-c", ".o")]:
        output = folder / ("output with spaces" + suffix)
        with tempfile.TemporaryDirectory(prefix="compcert4lean-caller-") as outside:
            require(not Path(outside).is_relative_to(REPO), "caller must be outside the repository")
            execute([*command, *([mode] if mode else []), "-o", output], cwd=outside,
                    timeout=compile_timeout, log=folder / ("mode-" + (suffix[1:] or "exe")))
        require(output.is_file() and output.stat().st_size > 0, "missing output")
        if mode is None:
            execute([output], timeout=run_timeout, log=folder / "spaces-run")
        elif mode == "-c":
            require(output.read_bytes().startswith(b"\x7fELF"), "object is not ELF")
        if mode:
            linked = folder / ("linked-" + suffix[1:])
            execute(["gcc", "-m64", "-no-pie", output, root / "runtime/libcompcert.a", "-lm", "-o", linked],
                    timeout=compile_timeout, log=folder / ("link-" + suffix[1:]))
            execute([linked], timeout=run_timeout, log=folder / ("run-" + suffix[1:]))
    invalid = folder / "invalid.c"
    invalid.write_text("int main( { this is invalid C; }\n")
    expect_failure([sys.executable, REPO / "scripts/compile_c.py", invalid], folder / "invalid-c", timeout=compile_timeout)
    expect_failure([*command, "-O4"], folder / "unsupported-option", timeout=compile_timeout)
    protected_output = folder / "must survive link error"
    protected_output.write_bytes(b"previous output\n")
    expect_failure([*command, "-lcompcert4lean_nonexistent_test_library", "-o", protected_output],
                   folder / "link-error", timeout=compile_timeout)
    require(protected_output.read_bytes() == b"previous output\n", "failed compilation damaged previous output")
    malformed = folder / "malformed.json"
    malformed.write_text('{"format":"wrong"}\n')
    expect_failure([LEAN, malformed, folder / "bad-output.json"], folder / "bad-format")
    original = json.loads((folder.parent / "for2" / "lean" / "csyntax.json").read_text())
    original["fresh"] = "0"
    malformed.write_text(json.dumps(original))
    expect_failure([LEAN, malformed, folder / "bad-output.json"], folder / "bad-identifier")
    original["fresh"] = "1e6"
    malformed.write_text(json.dumps(original))
    expect_failure([LEAN, malformed, folder / "bad-output.json"], folder / "bad-number")
    malformed.write_text('{"format":')
    expect_failure([LEAN, malformed, folder / "bad-output.json"], folder / "invalid-json")
    original = json.loads((folder.parent / "for2" / "lean" / "csyntax.json").read_text())
    original["definitions"][0][1] = ["Gfun"]
    malformed.write_text(json.dumps(original))
    expect_failure([LEAN, malformed, folder / "bad-output.json"], folder / "bad-arity")
    assembly_check = folder / "malformed-assembly"
    assembly_check.mkdir()
    malformed.write_text('{"format":"wrong","target":"x86_64-linux-sysv-O0"}\n')
    bridge = Bridge(root, assembly_check, time.monotonic() + compile_timeout)
    try:
        bridge.request({"root": str(root), "source": str(TESTS / "for2.c"), "preprocessor": [],
                        "preprocessed": str(assembly_check / "input.i"), "csyntax": str(assembly_check / "csyntax.json")})
        try:
            bridge.request({"operation": "print", "input": str(malformed), "output": str(assembly_check / "output.s")})
        except CompileError:
            require(b"unsupported assembly interchange" in (assembly_check / "bridge.stderr").read_bytes(),
                    "unexpected assembly error")
        else:
            raise CompileError("malformed assembly interchange was accepted")
    finally:
        bridge.close()
    expect_failure([LEAN, "--test-invalid-allocation", folder.parent / "for2" / "lean" / "csyntax.json"],
                   folder / "corrupt-allocation")
    require(b"invalid register allocation" in (folder / "corrupt-allocation.stderr").read_bytes().lower(),
            "allocation corruption did not reach Lean validator")
    execute([LEAN, "--test-codecs"], log=folder / "codecs", timeout=run_timeout)


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--compcert-root", type=Path, default=REPO.parent / "CompCert")
    parser.add_argument("--compile-timeout", type=float, default=120)
    parser.add_argument("--run-timeout", type=float, default=10)
    options = parser.parse_args()
    root = options.compcert_root.resolve()
    if options.compile_timeout <= 0 or options.run_timeout <= 0:
        parser.error("timeouts must be positive")
    BUILD.mkdir(parents=True, exist_ok=True)
    folder = Path(tempfile.mkdtemp(prefix="smoke-" + datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-", dir=BUILD))
    summary = {"allocator": ALLOCATOR, "tests": [], "integration": None, "success": False}
    print(f"Artifacts: {folder}", flush=True)
    try:
        summary["versions"] = prepare(root)
        verify_corpus()
        for name in ["for2", "funct3", "switch"]:
            case = folder / name
            case.mkdir()
            source = TESTS / (name + ".c")
            expected = (TESTS / "Results" / name).read_bytes()
            result = {"name": name}
            for pipeline in ["reference", "lean"]:
                artifacts = case / pipeline
                artifacts.mkdir()
                output = artifacts / name
                try:
                    if pipeline == "reference":
                        execute([root / "ccomp", "-stdlib", root / "runtime", *REFERENCE_FLAGS,
                                 source, "-o", output], env=tool_environment(root), timeout=options.compile_timeout,
                                log=artifacts / "compile")
                    else:
                        compile_source(compiler_options([str(source), "-o", str(output), "--compcert-root", str(root)]),
                                       prepared=True, artifact_dir=artifacts, timeout=options.compile_timeout)
                    stdout = execute([output], timeout=options.run_timeout, log=artifacts / "run")
                    require(stdout == expected, f"{name}/{pipeline}: stdout differs from upstream")
                    result[pipeline] = {"success": True}
                except (CompileError, OSError) as error:
                    result[pipeline] = {"success": False, "error": str(error)}
                print(f"{name}/{pipeline}: {'PASS' if result[pipeline]['success'] else 'FAIL'}", flush=True)
            summary["tests"].append(result)
        if all(case[pipeline]["success"] for case in summary["tests"] for pipeline in ["reference", "lean"]):
            try:
                integration_checks(root, folder / "integration", options.compile_timeout, options.run_timeout)
                summary["integration"] = {"success": True}
            except (CompileError, OSError) as error:
                summary["integration"] = {"success": False, "error": str(error)}
            summary["success"] = summary["integration"]["success"]
    except (CompileError, OSError) as error:
        summary["error"] = str(error)
    finally:
        (folder / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0 if summary["success"] else 1


if __name__ == "__main__":
    sys.exit(main())
