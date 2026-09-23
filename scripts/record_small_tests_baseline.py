#!/usr/bin/env python3
"""Preserve a complete suite report, command logs, fixtures and failure evidence."""

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--verification", type=Path, action="append", default=[], help="guard evidence directory to preserve")
    options = parser.parse_args()
    run = options.run.resolve()
    destination = options.destination.resolve()
    summary = json.loads((run / "results.json").read_text())
    if not summary.get("complete"):
        parser.error("only a complete, fully accounted run can be recorded as a baseline")
    destination.mkdir(parents=True, exist_ok=False)
    for name in ["results.json", "report.md"]:
        shutil.copy2(run / name, destination / name)
    files = set()
    for path in run.rglob("*"):
        if not path.is_file():
            continue
        if path.suffix in {".stdout", ".stderr", ".jsonl"}:
            files.add(path)
        elif path.suffix == ".json" and path.name not in {"csyntax.json", "asm.json"}:
            files.add(path)
    fixtures = run / "fixtures"
    if fixtures.exists():
        files.update(path for path in fixtures.rglob("*") if path.is_file() and path.suffix in {".c", ".h", ".ml"})
    for case in summary["cases"]:
        for pipeline in ["lean", "reference"]:
            if case[pipeline]["verdict"] == "pass":
                continue
            folder = run / case["id"] / pipeline
            files.update(path for path in folder.rglob("*") if path.is_file() and
                         (path.suffix in {".i", ".s"} or path.name in {"csyntax.json", "asm.json"}))
    entries = {str(path.relative_to(run)): path for path in files}
    for folder in options.verification:
        for name in ["REQUEST.json", "ADMISSION.json", "RESULT.json", "DRAINED.json", "stdout.log", "stderr.log"]:
            entries["verification/" + folder.name + "/" + name] = folder / name
    archive = destination / "evidence.tar.gz"
    hashes = {}
    with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode="w|") as output:
            for name, path in sorted(entries.items()):
                content = path.read_bytes()
                hashes[name] = hashlib.sha256(content).hexdigest()
                info = tarfile.TarInfo(name)
                info.size = len(content)
                info.mode = 0o644
                output.addfile(info, io.BytesIO(content))
    inventory = {"run": str(run), "counts": summary["counts"], "files": hashes,
                 "archive_sha256": hashlib.sha256(archive.read_bytes()).hexdigest()}
    (destination / "evidence.json").write_text(json.dumps(inventory, indent=2) + "\n")
    print(f"Recorded {len(hashes)} evidence files in {destination}")


if __name__ == "__main__":
    main()
