#!/usr/bin/env python3
"""Run the pinned upstream small tests and retain independent Lean/reference verdicts."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import time

from compile_c import parse_args as compiler_options
from prototype import BUILD, REFERENCE_FLAGS, REPO, SWITCH, CompileError
from prototype import compile_source, execute, prepare, tool_environment

CORPUS = REPO / "tests/small-tests"
PIPELINES = ("lean", "reference")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def verify_corpus():
    provenance = json.loads((CORPUS / "provenance.json").read_text())
    for name, record in provenance["files"].items():
        if digest(CORPUS / name) != record["sha256"]:
            raise CompileError("vendored upstream bytes changed: " + name, category="harness_failure")
    return provenance


def compare_bytes(actual, expected, description):
    if actual != expected:
        raise CompileError(description + ": bytes differ", category="incorrect_output")


def stage_status(records, compile_only=False):
    result = {name: "blocked" for name in ["compile", "assemble", "link", "execute", "compare"]}
    if compile_only:
        result.update(assemble="not_applicable", link="not_applicable", execute="not_applicable", compare="not_applicable")
    for record in records:
        name = record["stage"].split("-")[0]
        if name in result:
            result[name] = record["status"]
        if name == "compile" and "compiler" in record:
            for nested in record["compiler"]["stages"]:
                if nested["stage"] == "assemble":
                    result["assemble"] = nested["status"]
    return result


class Stages:
    def __init__(self, folder, root, options):
        self.folder = folder
        self.root = root
        self.options = options
        self.records = []

    def call(self, name, category, action):
        record = {"stage": name, "status": "running"}
        self.records.append(record)
        started = time.monotonic()
        try:
            value = action()
            record["status"] = "passed"
            return value
        except (CompileError, OSError) as error:
            record.update(status="timeout" if getattr(error, "timed_out", False) else "failed",
                          category=getattr(error, "category", None) or category, error=str(error))
            if isinstance(error, CompileError):
                error.category = record["category"]
            else:
                raise CompileError(str(error), category=category) from error
            raise
        finally:
            record["seconds"] = time.monotonic() - started

    def command(self, stage, command, *, cwd=None, stdin=None, env=None, category=None):
        log = self.folder / f"{len(self.records):03d}-{stage}"
        timeout = self.options.run_timeout if stage.startswith("execute") else (
            self.options.link_timeout if stage.startswith(("link", "assemble")) else self.options.compile_timeout)
        try:
            return self.call(stage, category or ("execution_failure" if stage.startswith("execute") else "reference_failure"),
                lambda: execute(command, cwd=cwd, stdin=stdin, env=env, timeout=timeout, log=log))
        finally:
            if log.with_suffix(".json").exists():
                self.records[-1].update(json.loads(log.with_suffix(".json").read_text()))
                self.records[-1]["stdout"] = str(log.with_suffix(".stdout"))
                self.records[-1]["stderr"] = str(log.with_suffix(".stderr"))

    def compile(self, pipeline, sources, output, flags, *, assembly=False, shared=False, libraries=()):
        objects = []
        for index, source in enumerate(sources):
            target = output.parent / (output.name + f"-{index:03d}" + (".s" if assembly else ".o"))
            if pipeline == "lean":
                artifacts = self.folder / f"compile-{len(self.records):03d}"
                arguments = [str(source), "-S" if assembly else "-c", *flags,
                             "-o", str(target), "--compcert-root", str(self.root),
                             "--link-timeout", str(self.options.link_timeout)]
                try:
                    self.call("compile", "lean_rejection", lambda: compile_source(compiler_options(arguments),
                              prepared=True, artifact_dir=artifacts, timeout=self.options.compile_timeout))
                finally:
                    if (artifacts / "result.json").exists():
                        self.records[-1]["compiler"] = json.loads((artifacts / "result.json").read_text())
                    self.records[-1]["artifacts"] = str(artifacts)
            else:
                compiler = ([self.root / "ccomp", "-stdlib", self.root / "runtime", *REFERENCE_FLAGS]
                            if pipeline == "reference" else ["gcc", "-O0", "-m64", "-fno-pie", "-fno-common"])
                source_flags = flags if pipeline == "reference" else [flag for flag in flags if not flag.startswith("-fstruct")]
                self.command("compile", [*compiler, "-S", *source_flags, source, "-o", target.with_suffix(".s")],
                             env=tool_environment(self.root), category="reference_failure")
                if not assembly:
                    self.command("assemble", ["gcc", "-m64", "-c", target.with_suffix(".s"), "-o", target],
                                 category="assembly_failure")
            objects.append(target)
        if not assembly:
            self.link(objects, output, shared=shared, libraries=libraries)
        return output

    def link(self, objects, output, *, shared=False, libraries=()):
        self.command("link", ["gcc", "-m64", "-shared" if shared else "-no-pie", *objects,
                              *libraries, self.root / "runtime/libcompcert.a", "-o", output], category="link_failure")


def generate_abi(folder, root, options, specification):
    folder.mkdir()
    shutil.copytree(CORPUS / "abi", folder / "abi")
    shutil.copy2(CORPUS / "endian.h", folder / "endian.h")
    stages = Stages(folder, root, options)
    work = folder / "abi"
    metadata = {"seed": options.seed, "specification": specification, "stages": stages.records}
    try:
        for generator in ["generator", "genlayout"]:
            stages.command("generator-build", ["opam", "exec", "--switch=" + SWITCH, "--", "ocamlopt",
                           "-o", generator + ".exe", generator + ".ml"], cwd=work, category="harness_failure")
        for name, flags in [("fixed", ["-rnd", str(specification["random_functions"])]),
                            ("vararg", ["-vararg", "-rnd", str(specification["random_functions"])]),
                            ("struct", ["-structs"])]:
            stages.command("generator", [work / "generator.exe", "-seed", str(options.seed), *flags, "-o", name],
                           cwd=work, category="harness_failure")
        output = stages.command("generator", [work / "genlayout.exe", "-seed", str(options.seed),
                                "-n", str(specification["layout_count"]), "-size", str(specification["layout_size"])],
                                cwd=work, category="harness_failure")
        (work / "layout.h").write_bytes(output)
        metadata["sha256"] = {str(path.relative_to(folder)): digest(path) for path in sorted(work.iterdir())
                              if path.suffix in {".c", ".h"}}
    finally:
        (folder / "fixtures.json").write_text(json.dumps(metadata, indent=2) + "\n")
    return metadata


def run_pipeline(case, pipeline, folder, root, options, fixtures):
    folder.mkdir(parents=True)
    stages = Stages(folder, root, options)
    result = {"pipeline": pipeline, "stages": stages.records, "artifacts": str(folder)}
    group = "regression" if case["group"] == "supplemental" else case["group"]
    source_tree = fixtures if group == "abi" else CORPUS
    work = folder / group
    output = work / "program"
    try:
        shutil.copytree(source_tree / group, work)
        shutil.copy2(CORPUS / "endian.h", folder / "endian.h")
        sources = [work / Path(name).name for name in case["sources"]]
        flags = case["flags"]
        check = case["check"]
        kind = check["kind"]
        if group == "pic":
            for name, dependencies in [("lib1", []), ("lib2", ["-l1"]), ("dylib", ["-l1"]), ("main", ["-l2", "-l1", "-ldl"])]:
                target = work / (name + ".so" if name != "main" else "program")
                stages.compile(pipeline, [work / (name + ".c")], target, flags, shared=name != "main",
                               libraries=["-L" + str(work), *dependencies])
        elif group == "abi" and case.get("variant") in {"gcc_to_native", "native_to_gcc"}:
            objects = []
            for index, source in enumerate(sources):
                tool = pipeline if (index == 0) == (case["variant"] == "gcc_to_native") else "gcc"
                target = work / (source.stem + ".s")
                stages.compile(tool, [source], target, flags, assembly=True)
                generated = target.with_name(target.name + "-000.s")
                obj = target.with_suffix(".o")
                stages.command("assemble", ["gcc", "-m64", "-c", generated, "-o", obj], category="assembly_failure")
                objects.append(obj)
            stages.link(objects, output)
        else:
            stages.compile(pipeline, sources, output, flags, assembly=kind == "compile", libraries=["-lm"])
        if kind == "compile":
            result["verdict"] = "pass"
            return result
        expected = (CORPUS / check["expected"]).read_bytes() if "expected" in check else None
        if kind == "interpreter":
            expected = stages.command("reference-interpreter", [root / "ccomp", "-stdlib", root / "runtime",
                                      "-interp", "-quiet", *flags, sources[0]], cwd=work,
                                      env=tool_environment(root), category="reference_failure")
        if kind == "gcc_stdout":
            oracle = work / "gcc-program"
            stages.compile("gcc", sources, oracle, flags)
            expected = stages.command("execute-gcc-reference", [oracle], cwd=work, category="reference_failure")
        environment = {**os.environ, "LD_LIBRARY_PATH": str(work)} if group == "pic" else None
        if kind == "roundtrip":
            data = (CORPUS / check["input"]).read_bytes()
            (work / "roundtrip.input").write_bytes(data)
            result["input_sha256"] = hashlib.sha256(data).hexdigest()
            stages.command("execute-compress", [output, "-c", "-i", "roundtrip.input", "-o", "compressed"], cwd=work)
            stages.command("execute-decompress", [output, "-d", "-i", "compressed", "-o", "recovered"], cwd=work)
            stages.call("compare", "incorrect_output", lambda: compare_bytes((work / "recovered").read_bytes(), data, "roundtrip"))
        else:
            stdout = stages.command("execute", [output, *check.get("args", [])], cwd=work, env=environment,
                                    stdin=(CORPUS / check["stdin"]).read_bytes() if "stdin" in check else None)
            def compare():
                if kind == "contains":
                    if check["text"].encode() not in stdout:
                        raise CompileError("missing upstream proof-found condition", category="incorrect_output")
                elif kind == "file":
                    compare_bytes((work / check["actual"]).read_bytes(), expected, check["actual"])
                elif expected is not None:
                    compare_bytes(stdout, expected, "stdout")
            stages.call("compare", "incorrect_output", compare)
        result["verdict"] = "pass"
    except (CompileError, OSError) as error:
        category = getattr(error, "category", None) or "harness_failure"
        result.update(verdict="timeout" if getattr(error, "timed_out", False) else
                      "unavailable" if category in {"reference_failure", "harness_failure"} else "fail",
                      category=category, error=str(error))
    finally:
        result["stage_status"] = stage_status(stages.records, case["check"]["kind"] == "compile")
        (folder / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def run_case(case, folder, root, options, fixtures, setup_error=None):
    results = {}
    for pipeline in PIPELINES:
        if setup_error:
            results[pipeline] = {"verdict": "unavailable", "category": "harness_failure", "error": setup_error,
                                 "stages": [], "stage_status": stage_status([], case["check"]["kind"] == "compile")}
        else:
            results[pipeline] = run_pipeline(case, pipeline, folder / case["id"] / pipeline, root, options, fixtures)
    verdicts = [result["verdict"] for result in results.values()]
    verdict = next((status for status in ["fail", "timeout", "unavailable"] if status in verdicts), "pass")
    result = {"id": case["id"], "verdict": verdict, "specification": case, **results}
    print(f"{case['id']}: {verdict.upper()} (Lean {results['lean']['verdict']}, reference {results['reference']['verdict']})", flush=True)
    return result


def write_report(folder, summary):
    summary["counts"] = {verdict: sum(case["verdict"] == verdict for case in summary["cases"])
                         for verdict in ["pass", "fail", "timeout", "unavailable"]}
    summary["counts"]["excluded"] = len(summary["exclusions"])
    summary["pipeline_counts"] = {pipeline: {verdict: sum(case[pipeline]["verdict"] == verdict for case in summary["cases"])
                                            for verdict in ["pass", "fail", "timeout", "unavailable"]} for pipeline in PIPELINES}
    summary["complete"] = "finished" in summary and len(summary["cases"]) == len(summary["selected"])
    summary["success"] = summary["complete"] and all(case["verdict"] == "pass" for case in summary["cases"])
    lines = ["# Small-test correctness report", "", "Target: Linux System V x86-64, O0, spill allocator.", "",
             "Run complete: " + str(summary["complete"]) + ".", "",
             "Counts: " + ", ".join(f"{name}={count}" for name, count in summary["counts"].items()), "",
             "Pipeline counts: " + json.dumps(summary["pipeline_counts"], sort_keys=True), "",
             "Compiler failures remain failures. Reference/harness failures make a check unavailable.", "",
             "| Case | Verdict | Lean | CompCert |", "| --- | --- | --- | --- |"]
    for case in summary["cases"]:
        lines.append(f"| {case['id']} | {case['verdict']} | {case['lean']['verdict']} | {case['reference']['verdict']} |")
    lines.extend(["", "## Failures and unavailable checks", ""])
    for case in summary["cases"]:
        for pipeline in PIPELINES:
            result = case[pipeline]
            if result["verdict"] != "pass":
                lines.extend([f"### {case['id']} / {pipeline}", "", f"Category: {result.get('category')}", "",
                              "```text", result.get("error", ""), "```", ""])
    lines.extend(["## Justified exclusions", ""])
    for excluded in summary["exclusions"]:
        lines.append(f"- {excluded['id']}: {excluded['reason']}")
    lines.extend(["", "Commands, flags, timings, versions, hashes and artifact locations: `results.json`.", ""])
    (folder / "results.json").write_text(json.dumps(summary, indent=2) + "\n")
    (folder / "report.md").write_text("\n".join(lines))


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--suite", action="append", default=[], help="group (repeatable)")
    parser.add_argument("--test", action="append", default=[], help="case ID glob (repeatable)")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--compile-timeout", type=float, default=300)
    parser.add_argument("--link-timeout", type=float, default=300)
    parser.add_argument("--run-timeout", type=float, default=300)
    parser.add_argument("--seed", type=int, default=20260922)
    parser.add_argument("--compcert-root", type=Path, default=REPO.parent / "CompCert")
    parser.add_argument("--artifacts", type=Path)
    options = parser.parse_args(argv)
    if not 1 <= options.jobs <= 32 or min(options.compile_timeout, options.link_timeout, options.run_timeout) <= 0:
        parser.error("jobs must be 1..32 and timeouts positive")
    return options


def main(argv=None):
    options = parse_args(argv)
    manifest = json.loads((CORPUS / "manifest.json").read_text())
    selected = [case for case in manifest["cases"] if (not options.suite or case["group"] in options.suite)
                and (not options.test or any(fnmatch.fnmatchcase(case["id"], pattern) for pattern in options.test))]
    exclusions = [item for item in manifest["exclusions"] if (not options.suite or item["id"].split("/")[0] in options.suite)
                  and (not options.test or any(fnmatch.fnmatchcase(item["id"], pattern) for pattern in options.test))]
    if not selected and not exclusions:
        raise CompileError("selection matches no test or exclusion", category="harness_failure")
    if options.list:
        for case in selected:
            print(case["id"] + "\t" + case["check"]["kind"] + "\t" + case.get("annotation", ""))
        for item in exclusions:
            print(item["id"] + "\texcluded\t" + item["reason"])
        return 0
    BUILD.mkdir(parents=True, exist_ok=True)
    folder = options.artifacts.resolve() if options.artifacts else Path(tempfile.mkdtemp(prefix="small-tests-", dir=BUILD))
    folder.mkdir(parents=True, exist_ok=True)
    if (folder / "results.json").exists() or (folder / "fixtures").exists():
        raise CompileError("artifact directory already contains a run")
    print(f"Artifacts: {folder}", flush=True)
    root = options.compcert_root.resolve()
    summary = {"format": "compcert4lean-small-test-results-v1", "started": datetime.now(timezone.utc).isoformat(),
               "options": {name: str(value) if isinstance(value, Path) else value for name, value in vars(options).items()},
               "manifest_sha256": digest(CORPUS / "manifest.json"), "selected": [case["id"] for case in selected],
               "cases": [], "exclusions": exclusions}
    setup_error = None
    fixture_error = None
    fixtures = folder / "fixtures"
    try:
        summary["provenance"] = verify_corpus()
        summary["versions"] = prepare(root)
    except (CompileError, OSError) as error:
        setup_error = str(error)
        summary["setup_error"] = setup_error
    if not setup_error and any(case["group"] == "abi" for case in selected):
        try:
            summary["generated_fixtures"] = generate_abi(fixtures, root, options, manifest["abi"])
        except (CompileError, OSError) as error:
            fixture_error = str(error)
            summary["fixture_error"] = fixture_error
    def run(case):
        return run_case(case, folder, root, options, fixtures,
                        setup_error or (fixture_error if case["group"] == "abi" else None))
    with ThreadPoolExecutor(max_workers=options.jobs) as executor:
        for result in executor.map(run, selected):
            summary["cases"].append(result)
            write_report(folder, summary)
    summary["finished"] = datetime.now(timezone.utc).isoformat()
    write_report(folder, summary)
    print(json.dumps(summary["counts"], sort_keys=True))
    return 0 if summary["success"] else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (CompileError, OSError) as error:
        print(f"small_tests: {error}", file=sys.stderr)
        sys.exit(1)
