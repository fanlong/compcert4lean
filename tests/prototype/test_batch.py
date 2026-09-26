"""Batch preparation, per-job flags and failure reporting."""

import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import compile_batch
import prototype
from compile_c import parse_args
from prototype import BUILD, LEAN, CompileError, LeanSession, compile_source, execute, prepare


class BatchTests(unittest.TestCase):
    def test_preparation_reuses_version_process_and_cleans_up_failures(self):
        root = prototype.REPO.parent / "CompCert"
        BUILD.mkdir(parents=True, exist_ok=True)
        folder = Path(tempfile.mkdtemp(prefix="prepare-session-test-", dir=BUILD))
        session = LeanSession(folder)
        try:
            prepare(root)
            expected = execute([LEAN, "--version"]).decode().strip()
            self.assertEqual(session.version(deadline=time.monotonic() + 30), expected)
            previous = session.process
            versions = prepare(root, lean_session=session)
            self.assertEqual(versions["lean"], expected)
            self.assertIsNot(session.process, previous)
            self.assertIsNotNone(previous.poll())
            self.assertEqual(session.version(deadline=time.monotonic() + 30), expected)
            original_version = session.version

            def incompatible_version(**kwargs):
                original_version(**kwargs)
                return "Lean (version incompatible)"

            with patch.object(session, "version", side_effect=incompatible_version):
                with self.assertRaisesRegex(CompileError, "expected Lean"):
                    prepare(root, lean_session=session)
            self.assertIsNone(session.process)
            original_execute = prototype.execute

            def failed_bridge_probe(command, **kwargs):
                if Path(str(command[0])).name == "modorder":
                    raise CompileError("bridge dependency probe failed")
                return original_execute(command, **kwargs)

            with patch.object(prototype, "execute", side_effect=failed_bridge_probe):
                with self.assertRaisesRegex(CompileError, "bridge dependency probe failed"):
                    prepare(root, lean_session=session)
            self.assertIsNone(session.process)
            with patch.object(prototype.json, "loads", return_value={"ok": True}):
                with self.assertRaisesRegex(CompileError, "missing runtime version"):
                    session.version(deadline=time.monotonic() + 30)
            self.assertIsNone(session.process)
            self.assertEqual(session.version(deadline=time.monotonic() + 30), expected)
            with self.assertRaises(CompileError) as failure:
                session.version(deadline=time.monotonic() - 1)
            self.assertTrue(failure.exception.timed_out)
            self.assertIsNone(session.process)
        finally:
            session.close()
        requests = [{"operation": "version"}, {"operation": "version", "input": "unused"},
                    {"operation": "version"}]
        responses = execute([LEAN, "--server"], stdin=("\n".join(map(json.dumps, requests)) + "\n").encode(), timeout=30)
        decoded = list(map(json.loads, responses.splitlines()))
        self.assertEqual([response["ok"] for response in decoded], [True, False, True])
        self.assertEqual([decoded[index]["version"] for index in [0, 2]], [expected, expected])

    def test_multi_source_reuses_version_process(self):
        BUILD.mkdir(parents=True, exist_ok=True)
        folder = Path(tempfile.mkdtemp(prefix="multi-session-test-", dir=BUILD))
        sources = [folder / "first.c", folder / "second.c"]
        for index, source in enumerate(sources):
            source.write_text(f"int {source.stem}(void) {{ return {index}; }}\n")
        artifacts = folder / "artifacts"
        with compile_batch.working_directory(folder):
            compile_source(parse_args([*map(str, sources), "-O2", "-S"]), artifact_dir=artifacts)
        version = json.loads((artifacts / "lean-version.json").read_text())
        for index, source in enumerate(sources):
            compilation = json.loads((artifacts / f"unit-{index:03d}-{source.stem}/lean.json").read_text())
            self.assertEqual(compilation["pid"], version["pid"])
            self.assertTrue(source.with_suffix(".s").exists())

    def test_preparation_reports_compiler_runtime_and_rejects_probe_failures(self):
        from prototype import REPO
        versions = prepare(REPO.parent / "CompCert")
        installed_version = execute(["lake", "env", "lean", "--version"], cwd=REPO).decode().strip()
        # Both report version, target and source commit. The Lean shell also
        # includes its own build-mode label, which is not public runtime data.
        self.assertEqual(versions["lean"].removesuffix(")"), installed_version.rsplit(", ", 1)[0])
        original_execute = prototype.execute

        def changed_version(command, **kwargs):
            if list(map(str, command)) == [str(LEAN), "--version"]:
                return b"Lean (version incompatible)\n"
            return original_execute(command, **kwargs)

        with patch.object(prototype, "execute", side_effect=changed_version):
            with self.assertRaisesRegex(CompileError, "expected Lean"):
                prepare(REPO.parent / "CompCert")

        def failed_ocaml_probe(command, **kwargs):
            if command[0] == "opam":
                raise CompileError("OCaml probe failed")
            return original_execute(command, **kwargs)

        with patch.object(prototype, "execute", side_effect=failed_ocaml_probe):
            with self.assertRaisesRegex(CompileError, "OCaml probe failed"):
                prepare(REPO.parent / "CompCert")

    def test_objects_flags_link_and_failed_job(self):
        BUILD.mkdir(parents=True, exist_ok=True)
        folder = Path(tempfile.mkdtemp(prefix="batch-test-", dir=BUILD))
        print(f"Artifacts: {folder}", flush=True)
        (folder / "value.c").write_text("int value(void) { return VALUE; }\n")
        (folder / "main.c").write_text("int value(void); int main(void) { return value() != 37; }\n")
        (folder / "bad.c").write_text("#error intentional batch failure\n")
        arguments = [
            ["-O0", "-DVALUE=37", "-c", "value.c", "-o", "value.o", "--keep-temps"],
            ["-O2", "-std=c18", "-c", "main.c", "-o", "main.o", "--keep-temps"],
            ["-c", "bad.c", "-o", "bad.o"],
            ["value.o", "main.o", "-o", "program"],
        ]
        with patch.object(compile_batch, "prepare", wraps=compile_batch.prepare) as preparation:
            result = compile_batch.compile_batch(
                [{"arguments": argv, "cwd": str(folder)} for argv in arguments], folder / "results")
        self.assertEqual(preparation.call_count, 1)
        self.assertFalse(result["success"])
        self.assertEqual([record["passed"] for record in result["jobs"]], [True, True, False, True])
        self.assertFalse((folder / "bad.o").exists())
        execute([folder / "program"], timeout=10)
        compile_source(parse_args(["-O0", "-DVALUE=37", "-c", str(folder / "value.c"),
                                   "-o", str(folder / "reference.o")]), prepared=True)
        self.assertEqual((folder / "value.o").read_bytes(), (folder / "reference.o").read_bytes())
        retained = Path(result["jobs"][0]["stdout"]).read_text().strip().removeprefix("Artifacts: ")
        metadata = json.loads((Path(retained) / "result.json").read_text())
        self.assertEqual(metadata["configuration"]["optimization"], "O0")
        second = Path(result["jobs"][1]["stdout"]).read_text().strip().removeprefix("Artifacts: ")
        first_lean = json.loads((Path(retained) / "lean.json").read_text())
        second_lean = json.loads((Path(second) / "lean.json").read_text())
        self.assertEqual(first_lean["pid"], second_lean["pid"])
        version_probe = json.loads((folder / "results/lean-version.json").read_text())
        self.assertEqual(first_lean["pid"], version_probe["pid"])
        self.assertEqual(first_lean["command"][-1], "--server")
        server_protocol = Path(folder / "results/bridge-server-protocol.jsonl").read_text()
        self.assertGreaterEqual(server_protocol.count('"phase": "frontend"'), 2)
        self.assertGreaterEqual(server_protocol.count('"phase": "assembly"'), 2)
        self.assertEqual(json.loads((folder / "results/results.json").read_text()), result)

    def test_server_matches_standalone_and_recovers(self):
        from prototype import REPO
        prepare(REPO.parent / "CompCert")
        folder = Path(tempfile.mkdtemp(prefix="server-test-", dir=BUILD))
        source = folder / "source.c"
        source.write_text("static int next(int value) { return value + 1; }\n"
                          "int main(void) { return next(41) != 42; }\n")
        inputs = []
        for optimization in ["O0", "O2"]:
            artifacts = folder / optimization
            compile_source(parse_args([str(source), "-" + optimization, "-S", "-o", str(folder / (optimization + ".s"))]),
                           prepared=True, artifact_dir=artifacts)
            inputs.append(artifacts)
        session = LeanSession(folder)
        target = folder / "target.json"
        try:
            for index, artifacts in enumerate(inputs + list(reversed(inputs))):
                session.compile(artifacts / "csyntax.json", target, deadline=time.monotonic() + 30,
                                log=folder / ("request-" + str(index)))
                self.assertEqual(target.read_bytes(), (artifacts / "asm.json").read_bytes())
            invalid = folder / "invalid.json"
            invalid.write_text('{"format": "unknown"}')
            previous = target.read_bytes()
            with self.assertRaises(CompileError):
                session.compile(invalid, target, deadline=time.monotonic() + 30, log=folder / "invalid")
            self.assertEqual(target.read_bytes(), previous)
            self.assertIsNone(session.process)
            session.compile(inputs[0] / "csyntax.json", target, deadline=time.monotonic() + 30, log=folder / "recovered")
            self.assertEqual(target.read_bytes(), (inputs[0] / "asm.json").read_bytes())
            with self.assertRaises(CompileError) as failure:
                session.compile(inputs[0] / "csyntax.json", target, deadline=time.monotonic() - 1, log=folder / "timeout")
            self.assertTrue(failure.exception.timed_out)
            self.assertIsNone(session.process)
            session.compile(inputs[1] / "csyntax.json", target, deadline=time.monotonic() + 30, log=folder / "after-timeout")
            self.assertEqual(target.read_bytes(), (inputs[1] / "asm.json").read_bytes())
        finally:
            session.close()
        requests = ["not-json", json.dumps({"input": str(inputs[0] / "csyntax.json"), "output": str(target)})]
        responses = execute([LEAN, "--server"], stdin=("\n".join(requests) + "\n").encode(), timeout=30)
        self.assertEqual([json.loads(line)["ok"] for line in responses.splitlines()], [False, True])
        self.assertEqual(target.read_bytes(), (inputs[0] / "asm.json").read_bytes())

    def test_mixed_roots_rejected_before_preparation(self):
        with patch.object(compile_batch, "prepare") as preparation:
            with self.assertRaisesRegex(ValueError, "same CompCert root"):
                compile_batch.compile_batch([
                    {"arguments": ["input.c", "--compcert-root", "/first"]},
                    {"arguments": ["input.c", "--compcert-root", "/second"]},
                ], "unused")
        preparation.assert_not_called()


if __name__ == "__main__":
    unittest.main()
