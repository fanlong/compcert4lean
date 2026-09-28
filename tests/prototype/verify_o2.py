"""Run the focused runtime, preservation and trust checks."""

import json
from pathlib import Path
import re
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from prototype import BUILD, REPO, CompileError, execute


def main():
    folder = Path(tempfile.mkdtemp(prefix="o2-verification-", dir=BUILD))
    print(f"Artifacts: {folder}", flush=True)
    commands = [
        ["lake", "build", "coreDiagnostics"],
        ["timeout", "30", REPO / ".lake/build/bin/coreDiagnostics"],
        ["lake", "build", "allocatorTests"],
        [REPO / ".lake/build/bin/allocatorTests"],
        ["lake", "env", "lean", "--run", "tests/prototype/RuntimeHelpers.lean"],
        ["lake", "env", "lean", "tests/prototype/TargetHeader.lean"],
        ["lake", "env", "lean", "tests/prototype/MapDefault.lean"],
        ["lake", "env", "lean", "tests/prototype/CodecDecoding.lean"],
        [sys.executable, "tests/prototype/test_optimization.py"],
        [sys.executable, "tests/prototype/test_small_inlining.py"],
        [sys.executable, "tests/prototype/test_loop_unroll.py"],
        [sys.executable, "tests/prototype/test_path_splitting.py"],
        [sys.executable, "tests/prototype/test_pair_scheduling.py"],
        [sys.executable, "tests/prototype/test_benchmarks.py"],
        [sys.executable, "tests/prototype/test_framework.py"],
        [sys.executable, "tests/prototype/test_batch.py"],
        [sys.executable, "tests/prototype/test_bridge_server.py"],
        [sys.executable, "tests/prototype/test_c_standard.py"],
        [sys.executable, "tests/allocator/test_interchange.py"],
        [sys.executable, "scripts/smoke_test.py"],
        [sys.executable, "scripts/generate_codecs.py", "--check"],
        ["lake", "env", "lean", "tests/prototype/Trust.lean"],
        ["lake", "build"],
    ]
    failures = []
    for index, command in enumerate(commands):
        try:
            output = execute(command, cwd=REPO, log=folder / f"check-{index:02d}")
            if command[-1] in {"tests/prototype/Trust.lean", "tests/prototype/TargetHeader.lean", "tests/prototype/CodecDecoding.lean"}:
                for axioms in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output.decode()):
                    if set(filter(None, map(str.strip, axioms.split(",")))) - {"propext", "Classical.choice", "Quot.sound"}:
                        raise CompileError("unapproved transitive axiom dependency: " + axioms)
                if "depends on axioms" not in output.decode():
                    raise CompileError("missing axiom audit output")
            print(str(command[-1]) + ": PASS", flush=True)
        except CompileError as error:
            failures.append({"command": list(map(str, command)), "error": str(error)})
            print(str(command[-1]) + ": FAIL " + str(error), flush=True)
    (folder / "results.json").write_text(json.dumps({"success": not failures, "failures": failures}, indent=2) + "\n")
    return bool(failures)


if __name__ == "__main__":
    sys.exit(main())
