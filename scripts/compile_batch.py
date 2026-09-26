#!/usr/bin/env python3
"""Compile a JSON list of {arguments, cwd} jobs, preparing once per batch."""

import argparse
import contextlib
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import sys
import time

from compile_c import parse_args
from prototype import BridgeServer, CompileError, LeanSession, compile_source, prepare


@contextlib.contextmanager
def working_directory(path):
    previous = Path.cwd()
    os.chdir(path)
    try:
        yield
    finally:
        os.chdir(previous)


def compile_batch(jobs, output):
    if not isinstance(jobs, list) or not jobs:
        raise ValueError("batch must be a nonempty list")
    parsed = []
    for job in jobs:
        if not isinstance(job, dict) or set(job) - {"arguments", "cwd", "label"}:
            raise ValueError("invalid batch job")
        arguments = job.get("arguments")
        if not isinstance(arguments, list) or not all(isinstance(argument, str) for argument in arguments):
            raise ValueError("arguments must be a list of strings")
        cwd = Path(job.get("cwd", ".")).resolve()
        with working_directory(cwd):
            options = parse_args(arguments)
            options.compcert_root = options.compcert_root.resolve()
        parsed.append((job, cwd, options))
    roots = {options.compcert_root for _, _, options in parsed}
    if len(roots) != 1:
        raise ValueError("all batch jobs must use the same CompCert root")
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    result = {"success": False, "jobs": []}
    started = time.monotonic()
    lean_session = LeanSession(output)
    bridge_session = BridgeServer(next(iter(roots)), output)
    try:
        prepare(next(iter(roots)), lean_session=lean_session)
        result["preparation_seconds"] = time.monotonic() - started
        for index, (job, cwd, options) in enumerate(parsed):
            folder = output / str(index)
            folder.mkdir()
            record = {"label": job.get("label", str(index)), "arguments": job["arguments"],
                      "cwd": str(cwd), "passed": False, "timed_out": False,
                      "stdout": str(folder / "stdout.txt"), "stderr": str(folder / "stderr.txt"),
                      "started_utc": datetime.now(timezone.utc).isoformat()}
            unit_started = time.monotonic()
            with (folder / "stdout.txt").open("w") as stdout, (folder / "stderr.txt").open("w") as stderr:
                with working_directory(cwd), contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                    try:
                        artifacts = compile_source(options, prepared=True, lean_session=lean_session,
                                                   bridge_session=bridge_session)
                        if options.keep_temps:
                            print(f"Artifacts: {artifacts}")
                        record.update(passed=True, exit_status=0)
                    except (CompileError, OSError) as error:
                        print(f"compile_batch: {error}", file=sys.stderr)
                        record.update(exit_status=1, timed_out=getattr(error, "timed_out", False),
                                      error=str(error), failure_kind=getattr(error, "category", None))
            record["wall_seconds"] = time.monotonic() - unit_started
            result["jobs"].append(record)
            (output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
            print(f"{record['label']}: {'PASS' if record['passed'] else 'FAIL'} "
                  f"({record['wall_seconds']:.3f}s)", flush=True)
        result["success"] = all(record["passed"] for record in result["jobs"])
    finally:
        lean_session.close()
        bridge_session.close()
        result["seconds"] = time.monotonic() - started
        (output / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--results", type=Path, required=True, help="new directory for batch logs")
    options = parser.parse_args()
    try:
        result = compile_batch(json.loads(options.manifest.read_text()), options.results)
        return 0 if result["success"] else 1
    except (CompileError, OSError, ValueError) as error:
        print(f"compile_batch: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
