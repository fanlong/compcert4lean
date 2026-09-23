#!/usr/bin/env python3
"""Validate and time the 29 pinned upstream workloads on one CPU."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import copy
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import platform
import shutil
import statistics
import sys
import tempfile
import time

from prototype import BUILD, REPO, CompileError, execute, prepare
from small_tests import CORPUS, Stages, compare_bytes, digest, verify_corpus

PIPELINES = ("lean", "reference", "gcc")


def workloads():
    manifest = json.loads((CORPUS / "manifest.json").read_text())
    cases = [copy.deepcopy(case) for case in manifest["cases"]
             if case["group"] in {"c", "compression", "raytracer", "spass"}]
    for case in cases:
        if case["group"] == "spass":
            case["id"] = "spass/problem"
            case["check"]["args"] = ["problem.dfg"]
    if len(cases) != 29:
        raise CompileError("expected exactly 29 benchmark workloads")
    return cases


def build(case, pipeline, folder, root, options):
    folder.mkdir(parents=True)
    work = folder / case["group"]
    stages = Stages(folder, root, options)
    result = {"pipeline": pipeline, "stages": stages.records, "artifacts": str(folder),
              "samples": [], "verdict": "unavailable"}
    try:
        shutil.copytree(CORPUS / case["group"], work)
        shutil.copy2(CORPUS / "endian.h", folder / "endian.h")
        sources = [work / Path(name).name for name in case["sources"]]
        started = time.monotonic()
        stages.compile(pipeline, sources, work / "program", case["flags"], libraries=["-lm"])
        result["compilation_seconds"] = time.monotonic() - started
        result["executable_sha256"] = digest(work / "program")
        sections = stages.command("size", ["size", "-A", work / "program"]).decode()
        result["text_bytes"] = next(int(line.split()[1]) for line in sections.splitlines()
                                    if line.split()[:1] == [".text"])
        stages.command("disassemble", ["objdump", "-d", work / "program"])
        if case["group"] == "compression":
            license_bytes = (CORPUS / "LICENSE").read_bytes()
            data = (license_bytes * ((1048576 + len(license_bytes) - 1) // len(license_bytes)))[:1048576]
            (work / "benchmark.input").write_bytes(data)
            result["input_sha256"] = digest(work / "benchmark.input")
            result["input_bytes"] = len(data)
        else:
            inputs = [case["check"]["stdin"]] if "stdin" in case["check"] else []
            inputs += [str(Path(case["group"]) / argument) for argument in case["check"].get("args", [])
                       if (work / argument).is_file()]
            inputs += [str(path.relative_to(CORPUS)) for path in (CORPUS / case["group"]).rglob("*.txt")]
            result["input_sha256"] = {name: digest(CORPUS / name) for name in inputs}
        result["verdict"] = "compiled"
    except (CompileError, OSError, StopIteration, ValueError) as error:
        result.update(verdict="timeout" if getattr(error, "timed_out", False) else "fail",
                      error=str(error), category=getattr(error, "category", None) or "harness_failure")
    (folder / "build.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def workload(case, pipeline, root, options, phase):
    folder = Path(pipeline["artifacts"])
    work = folder / case["group"]
    output = work / "program"
    check = case["check"]
    run_folder = folder / phase
    run_folder.mkdir()
    stages = Stages(run_folder, root, options)
    if case["group"] == "compression":
        stages.command("execute-compress", [output, "-c", "-i", "benchmark.input", "-o", "compressed"], cwd=work)
        stages.command("execute-decompress", [output, "-d", "-i", "compressed", "-o", "recovered"], cwd=work)
        compare_bytes((work / "recovered").read_bytes(), (work / "benchmark.input").read_bytes(), "roundtrip")
    else:
        stdout = stages.command("execute", [output, *check.get("args", [])], cwd=work,
                                stdin=(CORPUS / check["stdin"]).read_bytes() if "stdin" in check else None)
        if check["kind"] == "contains":
            if check["text"].encode() not in stdout:
                raise CompileError("missing Proof found", category="incorrect_output")
        elif check["kind"] == "file":
            compare_bytes((work / check["actual"]).read_bytes(), (CORPUS / check["expected"]).read_bytes(), "image")
        else:
            compare_bytes(stdout, (CORPUS / check["expected"]).read_bytes(), "stdout")
    return {"seconds": sum(record["seconds"] for record in stages.records), "stages": stages.records}


def report(folder, summary):
    lines = ["# O2 benchmark comparison", "", "Executable wall time in seconds; one warmup and seven measured runs, compiler order rotated each round.", "",
             "Compilation excludes helper builds and is completed before measurements. All executions use the recorded CPU affinity.", "",
             "Ratios greater than one mean Lean is slower. Failed workloads have no ratio.", "",
             "| Workload | Lean median | CompCert median | GCC median | Lean/CompCert | Lean/GCC | Notes |",
             "| --- | ---: | ---: | ---: | ---: | ---: | --- |"]
    ratios = {"reference": [], "gcc": []}
    for case in summary["cases"]:
        notes = list(case.get("notes", []))
        for name in PIPELINES:
            pipeline = case[name]
            values = [sample["seconds"] for sample in pipeline["samples"]]
            if pipeline["verdict"] == "pass" and len(values) == 7:
                pipeline["timing"] = {"median": statistics.median(values), "minimum": min(values),
                                      "maximum": max(values), "stdev": statistics.stdev(values),
                                      "coefficient_of_variation": statistics.stdev(values) / statistics.mean(values)}
            else:
                pipeline.pop("timing", None)
        times = {name: case[name].get("timing", {}).get("median") for name in PIPELINES}
        if any(value is not None and value < 0.01 for value in times.values()):
            notes.append("short runtime (<10 ms); excluded conservatively for startup overhead")
        case["aggregate_eligible"] = not notes
        case["ratios"] = {}
        for name in ratios:
            if times["lean"] is not None and times[name] is not None:
                ratio = times["lean"] / times[name]
                case["ratios"][name] = ratio
                if case["aggregate_eligible"]:
                    ratios[name].append(ratio)
        display = lambda value: "—" if value is None else f"{value:.6f}"
        lines.append("| " + " | ".join([case["id"], *[display(times[name]) for name in PIPELINES],
            display(case["ratios"].get("reference")), display(case["ratios"].get("gcc")),
            "; ".join(notes + [name + ": " + case[name]["verdict"] for name in PIPELINES if case[name]["verdict"] != "pass"])]) + " |")
    summary["aggregate"] = {name: {"count": len(values), "geometric_mean_ratio":
        math.exp(statistics.mean(map(math.log, values))) if values else None} for name, values in ratios.items()}
    summary["complete"] = "finished" in summary and len(summary["cases"]) == 29
    summary["success"] = summary["complete"] and all(case[name]["verdict"] == "pass"
                                                     for case in summary["cases"] for name in PIPELINES)
    lines.extend(["", "## Compilation, code size, and variability", "",
                  "| Workload | Compiler | Compilation s | .text bytes | Sample stdev s | Min–max s |",
                  "| --- | --- | ---: | ---: | ---: | --- |"])
    for case in summary["cases"]:
        for name in PIPELINES:
            result = case[name]
            timing = result.get("timing", {})
            lines.append(f"| {case['id']} | {name} | {result.get('compilation_seconds', '—')} | {result.get('text_bytes', '—')} | "
                         f"{timing.get('stdev', '—')} | {timing.get('minimum', '—')}–{timing.get('maximum', '—')} |")
    lines.extend(["", "Aggregate: `" + json.dumps(summary["aggregate"]) + "`.", "",
                  "Full commands, verdicts, raw samples, hashes and identities are in `results.json` and each workload directory.", ""])
    (folder / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    (folder / "report.md").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path)
    parser.add_argument("--compcert-root", type=Path, default=REPO.parent / "CompCert")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--cpu", type=int)
    parser.add_argument("--report-only", type=Path)
    parser.add_argument("--observations", type=Path)
    parser.add_argument("--retry-from", type=Path)
    for stage in ["compile", "link", "run"]:
        parser.add_argument("--" + stage + "-timeout", type=float, default=300)
    options = parser.parse_args()
    if options.report_only:
        folder = options.report_only.resolve()
        summary = json.loads((folder / "results.json").read_text())
        if options.observations:
            observations = json.loads(options.observations.read_text())
            unknown = set(observations) - {case["id"] for case in summary["cases"]}
            if unknown:
                parser.error("observations name unknown workloads: " + repr(unknown))
            for case in summary["cases"]:
                case["notes"] = observations.get(case["id"], {}).get("notes", [])
                case["work_observations"] = observations.get(case["id"], {})
            summary["observations_sha256"] = digest(options.observations)
        report(folder, summary)
        return 0 if summary["success"] else 1
    if options.observations:
        parser.error("--observations requires --report-only")
    previous = None
    if options.retry_from:
        previous = json.loads((options.retry_from / "results.json").read_text())
        if not previous.get("complete"):
            parser.error("retry requires a complete original run")
    options.optimization = "O2"
    if not 1 <= options.jobs <= 32 or min(options.compile_timeout, options.link_timeout, options.run_timeout) <= 0:
        parser.error("jobs must be 1..32 and timeouts positive")
    available = sorted(os.sched_getaffinity(0))
    cpu = (previous["cpu"] if previous else available[0]) if options.cpu is None else options.cpu
    if cpu not in available:
        parser.error("CPU is outside the allowed affinity")
    if previous and cpu != previous["cpu"]:
        parser.error("retry must use the original recorded CPU")
    BUILD.mkdir(parents=True, exist_ok=True)
    folder = options.artifacts.resolve() if options.artifacts else Path(tempfile.mkdtemp(prefix="benchmarks-o2-", dir=BUILD))
    folder.mkdir(parents=True, exist_ok=True)
    if any(folder.iterdir()):
        parser.error("artifact directory must be empty")
    root = options.compcert_root.resolve()
    summary = {"format": "compcert4lean-benchmarks-v1", "started": datetime.now(timezone.utc).isoformat(),
               "options": {name: str(value) if isinstance(value, Path) else value for name, value in vars(options).items()},
               "cpu": cpu, "available_cpus": available, "platform": platform.platform(),
               "cpuinfo": Path("/proc/cpuinfo").read_text(), "provenance": verify_corpus(),
               "versions": prepare(root), "cases": []}
    print(f"Artifacts: {folder}", flush=True)
    cases = workloads()
    previous_cases = {case["id"]: case for case in previous["cases"]} if previous else {}
    if previous:
        if previous["provenance"] != summary["provenance"] or set(previous_cases) != {case["id"] for case in cases}:
            parser.error("retry source provenance or workload inventory changed")
        summary["previous_run"] = {"path": str(options.retry_from.resolve()),
                                   "results_sha256": digest(options.retry_from / "results.json"),
                                   "versions": previous["versions"]}
    selected = [case for case in cases if not previous or
                any(previous_cases[case["id"]][name]["verdict"] != "pass" for name in PIPELINES)]
    tasks = [(case, pipeline) for case in selected for pipeline in PIPELINES]
    def compile_task(task):
        case, pipeline = task
        result = build(case, pipeline, folder / case["id"] / pipeline, root, options)
        print(f"{case['id']} / {pipeline}: {result['verdict'].upper()}", flush=True)
        return result
    with ThreadPoolExecutor(max_workers=options.jobs) as executor:
        built = list(executor.map(compile_task, tasks))
    replacements = {case["id"]: {**case, **dict(zip(PIPELINES, built[index * 3:index * 3 + 3]))}
                    for index, case in enumerate(selected)}
    summary["cases"] = [replacements.get(case["id"], previous_cases.get(case["id"])) for case in cases]
    summary["compilation_finished"] = datetime.now(timezone.utc).isoformat()
    os.sched_setaffinity(0, {cpu})
    summary["measurement_affinity"] = sorted(os.sched_getaffinity(0))
    summary["measurement_started"] = datetime.now(timezone.utc).isoformat()
    report(folder, summary)
    for case in summary["cases"]:
        if case["id"] not in replacements:
            continue
        for name in PIPELINES:
            result = case[name]
            if result["verdict"] != "compiled":
                continue
            try:
                result["validation"] = workload(case, result, root, options, "validation")
                result["warmup"] = workload(case, result, root, options, "warmup")
                result["verdict"] = "pass"
            except (CompileError, OSError) as error:
                result.update(verdict="fail", error=str(error), category=getattr(error, "category", None) or "execution_failure")
        for round_index in range(7):
            order = PIPELINES[round_index % 3:] + PIPELINES[:round_index % 3]
            for name in order:
                result = case[name]
                if result["verdict"] != "pass":
                    continue
                try:
                    sample = workload(case, result, root, options, f"round-{round_index}")
                    sample.update(round=round_index, order=list(order), cpu=cpu)
                    result["samples"].append(sample)
                except (CompileError, OSError) as error:
                    result.update(verdict="fail", error=str(error), category=getattr(error, "category", None) or "execution_failure")
            report(folder, summary)
        print(case["id"] + ": " + ", ".join(name + " " + case[name]["verdict"] for name in PIPELINES), flush=True)
    summary["finished"] = datetime.now(timezone.utc).isoformat()
    report(folder, summary)
    return 0 if summary["success"] else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (CompileError, OSError) as error:
        print(f"benchmarks: {error}", file=sys.stderr)
        sys.exit(1)
