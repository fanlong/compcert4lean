"""Check transaction isolation and recovery when the bridge parent is reused."""

import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_batch import working_directory
from compile_c import parse_args
from prototype import BUILD, REPO, BridgeServer, CompileError, LeanSession, compile_source, execute, prepare, tool_environment


class BridgeServerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = (REPO.parent / "CompCert").resolve()
        prepare(cls.root)
        cls.artifacts = Path(tempfile.mkdtemp(prefix="bridge-server-test-", dir=BUILD))
        print(f"Artifacts: {cls.artifacts}", flush=True)

    def setUp(self):
        self.folder = self.artifacts / self._testMethodName
        self.folder.mkdir()
        self.session = BridgeServer(self.root, self.folder)
        self.lean = LeanSession(self.folder)
        self.addCleanup(self.session.close)
        self.addCleanup(self.lean.close)

    def source(self, name, content):
        path = self.folder / (name + ".c")
        path.write_text(content)
        return path

    def compile(self, source, label, flags=(), *, session=True, cwd=None):
        folder = self.folder / label
        with working_directory(cwd or self.folder):
            compile_source(parse_args([str(source), *flags, "-S", "-o", str(self.folder / (label + ".s")),
                                       "--compcert-root", str(self.root)]),
                           prepared=True, artifact_dir=folder, lean_session=self.lean,
                           bridge_session=self.session if session else None)
        return folder

    def assert_equivalent(self, source, label, flags=(), *, cwd=None):
        reference = self.compile(source, label + "-reference", flags, session=False, cwd=cwd)
        candidate = self.compile(source, label + "-candidate", flags, cwd=cwd)
        for name in ["csyntax.json", "asm.json", "output.s"]:
            self.assertEqual((reference / name).read_bytes(), (candidate / name).read_bytes(), name)
        return candidate

    def test_mixed_programs_options_and_pragmas(self):
        floating = self.source("floating", "double negate(double value) { return -value; }\n")
        ordinary = self.source("ordinary", "static int value = 3; int get(int count) {\n"
                               "while (count > 0) { value = value * 5 + count; --count; } return value; }\n")
        structured = self.source("structured", "struct pair { int first; int second; };\n"
                                 "struct pair swap(struct pair value) {\n"
                                 "struct pair result = {value.second, value.first}; return result; }\n")
        calls = self.source("calls", "#include <stdio.h>\nint show(void) { return printf(\"value=%d\\n\", 7); }\n")
        reserved = self.source("reserved", '#pragma reserve_register r12\nint add(int value) { return value + 7; }\n')
        cases = [(floating, ["-O2", "-fpic"]), (ordinary, ["-O0", "-fnone"]),
                 (structured, ["-O2", "-fstruct-passing"]), (calls, ["-O0"]),
                 (reserved, ["-O2", "-fcommon"]), (ordinary, ["-O2", "-std=c18"]),
                 (floating, ["-O0"]), (calls, ["-O2", "-std=c11"])]
        parents = []
        for index, (source, flags) in enumerate(cases):
            self.assert_equivalent(source, str(index), flags)
            parents.append(self.session.process.pid)
        self.assertEqual(len(set(parents)), 1)
        with self.assertRaises(CompileError):
            self.compile(structured, "default-struct-rejected", ["-O2"])
        self.assertIsNone(self.session.process)
        self.assert_equivalent(calls, "after-language-rejection", ["-O2"])

    def test_relative_includes_follow_each_job_directory(self):
        source = self.source("include", "#include <value.h>\nint value(void) { return VALUE; }\n")
        parents = []
        outputs = []
        for index in range(2):
            cwd = self.folder / ("cwd-" + str(index))
            (cwd / "include").mkdir(parents=True)
            (cwd / "include/value.h").write_text(f"#define VALUE {31 + index}\n")
            artifacts = self.assert_equivalent(source, str(index), ["-O2", "-Iinclude"], cwd=cwd)
            parents.append(self.session.process.pid)
            outputs.append((artifacts / "output.s").read_bytes())
        self.assertNotEqual(parents[0], parents[1])
        self.assertNotEqual(outputs[0], outputs[1])

    def test_frontend_lean_and_printer_failures_recover(self):
        source = self.source("valid", "int value(void) { return 42; }\n")
        invalid = self.source("invalid", "int broken( {\n")
        self.assert_equivalent(source, "initial")
        with self.assertRaises(CompileError) as failure:
            self.compile(invalid, "frontend-failure")
        self.assertEqual(failure.exception.stage, "frontend")
        self.assertIsNone(self.session.process)
        self.assert_equivalent(source, "after-frontend")
        with patch.object(self.lean, "compile", side_effect=CompileError("injected Lean rejection")):
            with self.assertRaises(CompileError) as failure:
                self.compile(source, "lean-failure")
        self.assertEqual(failure.exception.stage, "lean")
        self.assertIsNone(self.session.process)
        self.assert_equivalent(source, "after-lean")
        original_compile = self.lean.compile

        def wrong_assembly(source, target, **options):
            original_compile(source, target, **options)
            target.write_text('{"format":"wrong"}')

        with patch.object(self.lean, "compile", side_effect=wrong_assembly):
            with self.assertRaises(CompileError) as failure:
                self.compile(source, "printer-failure")
        self.assertEqual(failure.exception.stage, "assembly_print")
        self.assertIsNone(self.session.process)
        self.assert_equivalent(source, "after-printer")

    def test_timeout_during_pair_discards_transaction(self):
        source = self.source("valid", "int value(void) { return 42; }\n")
        self.session.request({"root": str(self.root), "source": str(source), "preprocessor": [],
                              "preprocessed": str(self.folder / "input.i"),
                              "csyntax": str(self.folder / "csyntax.json")}, deadline=time.monotonic() + 30)
        with self.assertRaises(CompileError) as failure:
            self.session.request({"operation": "print"}, deadline=time.monotonic() - 1)
        self.assertTrue(failure.exception.timed_out)
        self.assertIsNone(self.session.process)
        self.assert_equivalent(source, "after-timeout")

    def test_invalid_response_and_eof_restart_parent(self):
        source = self.source("valid", "int value(void) { return 42; }\n")
        original_command = self.session.command
        responses = ["[]", "invalid-json", '{"ok":true,"phase":"assembly"}', None]
        for index, response in enumerate(responses):
            script = "import sys; sys.stdin.readline(); "
            script += "pass" if response is None else "print(" + repr(response) + ", flush=True)"
            self.session.command = [sys.executable, "-c", script]
            with self.assertRaises(CompileError):
                self.session.request({}, deadline=time.monotonic() + 30)
            self.assertIsNone(self.session.process)
            self.session.command = original_command
            self.assert_equivalent(source, "recovered-" + str(index))
            self.session.reset()

    def test_buffered_client_requests_do_not_cross_transactions(self):
        source = self.source("valid", "int value(void) { return 42; }\n")
        reference = self.compile(source, "reference", session=False)
        frontend = {"root": str(self.root), "source": str(source), "preprocessor": [],
                    "preprocessed": str(self.folder / "input.i"), "csyntax": str(self.folder / "csyntax.json")}
        printer = {"operation": "print", "input": str(reference / "asm.json"),
                   "output": str(self.folder / "output.s")}
        requests = ["not-json", json.dumps(frontend), json.dumps(printer), json.dumps(frontend), json.dumps(printer)]
        response = execute([BUILD / "bridge/bridge"],
                           env={**tool_environment(self.root), "COMPCERT4LEAN_BRIDGE_SERVER": "1"},
                           stdin=("\n".join(requests) + "\n").encode(), timeout=30)
        self.assertEqual([json.loads(line)["ok"] for line in response.splitlines()], [False, True, True, True, True])
        self.assertEqual((self.folder / "output.s").read_bytes(), (reference / "output.s").read_bytes())
        self.assertEqual((self.folder / "csyntax.json").read_bytes(), (reference / "csyntax.json").read_bytes())

if __name__ == "__main__":
    unittest.main()
