#!/usr/bin/env python3
"""Archive O2 evidence without modifying verdicts or either proof ledger."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

from prototype import PIN, REPO


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1048576), b""):
            result.update(block)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--o0", required=True, type=Path)
    parser.add_argument("--o2", required=True, type=Path)
    parser.add_argument("--benchmarks", required=True, type=Path)
    parser.add_argument("--checks", required=True, type=Path)
    parser.add_argument("--attempt", action="append", default=[], type=Path)
    parser.add_argument("--verification", action="append", default=[], type=Path)
    parser.add_argument("--diagnostics", action="append", default=[], type=Path)
    parser.add_argument("--destination", type=Path, default=REPO / "tests/benchmarks/o2-baseline")
    options = parser.parse_args()
    destination = options.destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    if (destination / "evidence.tar.gz").exists():
        parser.error("archive already exists; preserve it and choose a new destination")
    entries = {}
    summaries = {}
    for name, run in [("o0", options.o0), ("o2", options.o2), ("benchmarks", options.benchmarks)]:
        summary = json.loads((run / "results.json").read_text())
        if not summary.get("complete"):
            parser.error(name + " run is incomplete")
        summaries[name] = summary
        target = destination / name
        target.mkdir(exist_ok=True)
        for filename in ["results.json", "report.md"]:
            shutil.copy2(run / filename, target / filename)
    manifest = json.loads((REPO / "tests/small-tests/manifest.json").read_text())
    expected_cases = {case["id"] for case in manifest["cases"]}
    if len(expected_cases) != 139 or len(manifest["exclusions"]) != 9:
        parser.error("unexpected applicable suite inventory")
    dossiers = [json.loads(path.read_text()) for path in (destination / "failures").glob("*.json")]
    if any(not dossier.get("investigation_complete") for dossier in dossiers):
        parser.error("unfinished failure investigation")
    diagnosed_cases = {name for dossier in dossiers for name in dossier["affected_correctness_cases"]}
    diagnosed_benchmarks = {name for dossier in dossiers for name in dossier["affected_benchmark_workloads"]}
    for level in ["o0", "o2"]:
        summary = summaries[level]
        if {case["id"] for case in summary["cases"]} != expected_cases or len(summary["cases"]) != 139:
            parser.error("missing or duplicated correctness cases")
        if summary["exclusions"] != manifest["exclusions"] or summary["options"]["seed"] != 20260922:
            parser.error("changed exclusions or ABI seed")
        if summary["options"]["optimization"] != level.upper():
            parser.error("mismatched correctness profile")
        for case in summary["cases"]:
            if case["reference"]["verdict"] != "pass":
                parser.error("unresolved reference correctness failure")
            if case["lean"]["verdict"] != "pass" and (level == "o0" or case["id"] not in diagnosed_cases):
                parser.error("unresolved correctness failure: " + case["id"])
    benchmark_cases = summaries["benchmarks"]["cases"]
    expected_benchmarks = {"spass/problem" if case["group"] == "spass" else case["id"]
                           for case in manifest["cases"] if case["group"] in {"c", "compression", "raytracer", "spass"}}
    if len(benchmark_cases) != 29 or {case["id"] for case in benchmark_cases} != expected_benchmarks:
        parser.error("missing or duplicated benchmark workloads")
    for case in benchmark_cases:
        for pipeline in ["lean", "reference", "gcc"]:
            result = case[pipeline]
            if result["verdict"] != "pass":
                if pipeline != "lean" or case["id"] not in diagnosed_benchmarks or case["ratios"]:
                    parser.error("unresolved benchmark failure: " + case["id"] + "/" + pipeline)
            elif len(result["samples"]) != 7 or "validation" not in result or "warmup" not in result:
                parser.error("incomplete validated timing samples")
    checks = json.loads((options.checks / "results.json").read_text())
    if not checks["success"]:
        parser.error("final build/runtime/trust checks did not pass")
    acceptance = {"milestone_complete": True, "investigation_complete": True,
                  "all_o2_tests_passed": summaries["o2"]["success"],
                  "o0_counts": summaries["o0"]["counts"], "o2_counts": summaries["o2"]["counts"],
                  "benchmark_workloads": len(benchmark_cases),
                  "benchmarks_all_passed": summaries["benchmarks"]["success"],
                  "core_failure_dossiers": [dossier["id"] for dossier in dossiers],
                  "unresolved_failures": [], "checks": str(options.checks),
                  "correctness_nonzero_exit_required": not summaries["o2"]["success"]}
    (destination / "acceptance.json").write_text(json.dumps(acceptance, indent=2) + "\n")
    for run in [options.o0, options.o2, options.benchmarks, *options.attempt]:
        for path in run.rglob("*"):
            if path.is_file() and (path.suffix in {".json", ".jsonl", ".stdout", ".stderr", ".log", ".i", ".s", ".input"}
                                  or path.name in {"program", "recovered", "compressed", "kal.ppm"}
                                  or ("fixtures" in path.relative_to(run).parts and path.suffix in {".c", ".h", ".ml"})):
                entries["runs/" + run.name + "/" + str(path.relative_to(run))] = path
    for folder in options.verification:
        drain = folder / "DRAINED.json"
        if not drain.is_file() or not json.loads(drain.read_text()).get("all_descendants_drained"):
            parser.error("guard has not drained: " + str(folder))
        for path in folder.rglob("*"):
            if path.is_file():
                entries["verification/" + folder.name + "/" + str(path.relative_to(folder))] = path
    for folder in [options.checks, *options.diagnostics]:
        for path in folder.rglob("*"):
            if path.is_file():
                entries["diagnostics/" + folder.name + "/" + str(path.relative_to(folder))] = path
    for name in ["CompCert4Lean", "bridge", "scripts", "tests/prototype", "tests/allocator", "tests/small-tests"]:
        for path in (REPO / name).rglob("*"):
            if path.is_file() and path.suffix not in {".pyc", ".tar", ".gz"} and "__pycache__" not in path.parts:
                entries["source/" + str(path.relative_to(REPO))] = path
    for name in ["CompCert4Lean.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain", "PROTOTYPE.md"]:
        entries["source/" + name] = REPO / name
    entries["diagnostics/generated-Kildall.c"] = REPO / ".lake/build/ir/CompCert4Lean/Backend/Kildall.c"
    entries["reference/Kildall.v"] = REPO.parent / "CompCert/backend/Kildall.v"
    entries["reference/Kildall.ml"] = REPO.parent / "CompCert/extraction/Kildall.ml"
    for path in destination.rglob("*"):
        if path.is_file():
            entries["reports/" + str(path.relative_to(destination))] = path
    changed = subprocess.check_output(["git", "diff", "--name-only", "HEAD"], cwd=REPO, text=True).splitlines()
    protected_changes = [name for name in changed if name.startswith("CompCert4Lean/") and
                         not name.startswith(("CompCert4Lean/Prototype/", "CompCert4Lean/Allocator/"))]
    if protected_changes:
        parser.error("compiler-core changes: " + repr(protected_changes))
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "tests/small-tests", "tests/small-tests-baseline"], cwd=REPO, check=True)
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", "proof-status.json"], cwd=REPO.parent, check=True)
    upstream = REPO.parent / "CompCert"
    upstream_revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=upstream, text=True).strip()
    upstream_status = subprocess.check_output(["git", "status", "--porcelain"], cwd=upstream, text=True)
    if upstream_revision != PIN or upstream_status:
        parser.error("pinned upstream has changed")
    preservation = {"compiler_core_changes": protected_changes, "changed_tracked_files": changed,
                    "lean_base_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
                    "upstream_revision": upstream_revision, "upstream_status": upstream_status,
                    "imported_sources_and_o0_baseline_unchanged": True,
                    "proof_status_sha256": digest(REPO.parent / "proof-status.json"),
                    "legacy_state_sha256": digest(REPO.parent / "agent-runs/proof-grinding-first-pass-v1/STATE.json"),
                    "protected_lean_sha256": {str(path.relative_to(REPO)): digest(path)
                      for path in sorted((REPO / "CompCert4Lean").rglob("*.lean"))
                      if not str(path.relative_to(REPO)).startswith(("CompCert4Lean/Prototype/", "CompCert4Lean/Allocator/"))}}
    (destination / "preservation.json").write_text(json.dumps(preservation, indent=2) + "\n")
    entries["reports/preservation.json"] = destination / "preservation.json"
    inventory = {}
    seen = {}
    archive = destination / "evidence.tar.gz"
    with archive.open("xb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w|") as output:
            for name, path in sorted(entries.items()):
                checksum = digest(path)
                mode = 0o755 if path.name == "program" else 0o644
                inventory[name] = {"sha256": checksum, "bytes": path.stat().st_size}
                info = tarfile.TarInfo(name)
                info.mode = mode
                key = (checksum, mode)
                if key in seen:
                    info.type = tarfile.LNKTYPE
                    info.linkname = seen[key]
                    output.addfile(info)
                else:
                    seen[key] = name
                    info.size = path.stat().st_size
                    with path.open("rb") as source:
                        output.addfile(info, source)
    (destination / "evidence.json").write_text(json.dumps({"archive_sha256": digest(archive), "files": inventory}, indent=2) + "\n")
    print(f"Recorded {len(inventory)} files in {destination}")


if __name__ == "__main__":
    main()
