"""Integration contracts for multi-file linking, relocation and failure reporting."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, LEAN, REPO, Bridge, CompileError, compile_source, execute, prepare
from small_tests import Stages, compare_bytes, parse_args as suite_options, run_pipeline, write_report
import time


class FrameworkTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = REPO.parent / "CompCert"
        prepare(cls.root)
        cls.artifacts = Path(tempfile.mkdtemp(prefix="framework-", dir=BUILD))
        print(f"Artifacts: {cls.artifacts}", flush=True)

    def setUp(self):
        self.folder = self.artifacts / self._testMethodName
        self.folder.mkdir()
        self.counter = 0

    def source(self, name, text):
        path = self.folder / name
        path.parent.mkdir(exist_ok=True)
        path.write_text(text)
        return path

    def compile(self, *arguments):
        self.counter += 1
        folder = self.folder / f"compile-{self.counter}"
        compile_source(parse_args([*map(str, arguments), "--compcert-root", str(self.root)]),
                       prepared=True, artifact_dir=folder)
        return folder

    def test_cross_file_private_names_and_objects(self):
        first = self.source("first.c", "static int value=2; static int local(void){return value;} int global=5; int read(void){return local();}")
        second = self.source("second.c", "static int value=3; static int local(void){return value;} extern int global; int read(void); int main(void){return read()+local()+global-10;}")
        output = self.folder / "multi"
        self.compile(first, second, "-o", output)
        execute([output], timeout=10)
        obj = self.folder / "first.o"
        self.compile(first, "-c", "-o", obj)
        self.compile(second, obj, "-o", output)
        execute([output], timeout=10)
        obj2 = self.folder / "second.o"
        self.compile(second, "-c", "-o", obj2)
        self.compile(obj, obj2, "-o", output)
        execute([output], timeout=10)
        combined = self.folder / "combined.o"
        self.compile(obj, obj2, "-r", "-o", combined)
        self.compile(combined, "-o", output)
        execute([output], timeout=10)
        asm = self.folder / "first.s"
        self.compile(first, "-S", "-o", asm)
        self.compile(asm, second, "-o", output)
        execute([output], timeout=10)

    def test_archive_order_and_failure_preservation(self):
        provider = self.source("provider.c", "int value(void){return 7;}")
        caller = self.source("caller.c", "int value(void); int main(void){return value()-7;}")
        obj = self.folder / "provider.o"
        archive = self.folder / "libprovider.a"
        output = self.folder / "program"
        self.compile(provider, "-c", "-o", obj)
        execute(["ar", "rcs", archive, obj], timeout=30)
        self.compile(caller, "-L" + str(self.folder), "-lprovider", "-o", output)
        execute([output], timeout=10)
        previous = output.read_bytes()
        with self.assertRaises(CompileError) as failure:
            self.compile(archive, caller, "-o", output)
        self.assertEqual(failure.exception.category, "link_failure")
        self.assertEqual(output.read_bytes(), previous)
        invalid = self.source("invalid.c", "int main( {")
        with self.assertRaises(CompileError) as failure:
            self.compile(caller, invalid, "-o", output)
        self.assertEqual(failure.exception.category, "frontend_rejection")
        self.assertEqual(output.read_bytes(), previous)

    def test_multiple_outputs_and_collisions(self):
        first = self.source("one.c", "int one(void){return 1;}")
        second = self.source("two.c", "int two(void){return 2;}")
        command = [sys.executable, REPO / "scripts/compile_c.py", first, second]
        for mode, suffix in [("-c", ".o"), ("-S", ".s")]:
            execute([*command, mode], cwd=self.folder, timeout=120)
            for name in ["one", "two"]:
                self.assertTrue((self.folder / (name + suffix)).is_file())
        with self.assertRaises(SystemExit):
            parse_args([str(first), str(second), "-c", "-o", "ambiguous.o"])
        duplicate = self.source("nested/one.c", "invalid source must not reach frontend")
        with self.assertRaisesRegex(CompileError, "collision"):
            self.compile(first, duplicate, "-c")
        with self.assertRaisesRegex(CompileError, "differ"):
            self.compile(first, "-o", first)
        previous = (self.folder / "one.o").read_bytes()
        invalid = self.source("bad.c", "bad C")
        with self.assertRaises(CompileError):
            execute([sys.executable, REPO / "scripts/compile_c.py", first, invalid, "-c"], cwd=self.folder, timeout=120)
        self.assertEqual((self.folder / "one.o").read_bytes(), previous)

    def test_pic_shared_and_common(self):
        library = self.source("library.c", "static int private=3; int global=4; int tentative; extern int outside; int sum(void){return private+global+tentative+outside;}")
        caller = self.source("caller.c", "int outside=5; int sum(void); int main(void){return sum()-12;}")
        shared = self.folder / "libtest.so"
        folder = self.compile(library, "-fpic", "-fcommon", "-shared", "-o", shared)
        self.compile(caller, shared, "-o", self.folder / "program")
        execute([self.folder / "program"], timeout=10)
        config = json.loads((folder / "csyntax.json").read_text())["configuration"]
        facts = [value for _, value in config["symbols"]]
        self.assertTrue(config["pic"] and config["common"])
        self.assertTrue(any(item["storage"] == "static" and item["definedHere"] for item in facts))
        self.assertTrue(any(item["storage"] == "extern" and not item["definedHere"] for item in facts))
        self.assertTrue(any(item["storage"] == "default" and item["definedHere"] for item in facts))
        self.assertTrue(any(item["storage"] == "default" and not item["definedHere"] and item["size"] == "4" for item in facts))
        self.assertIn(b"GOTPCREL", (folder / "output.s").read_bytes())
        self.assertNotIn(b"private@GOTPCREL", (folder / "output.s").read_bytes())
        for symbol in ["global", "tentative", "outside"]:
            self.assertIn((symbol + "@GOTPCREL").encode(), (folder / "output.s").read_bytes())
        self.assertEqual(config, json.loads((folder / "asm.json").read_text())["configuration"])
        first = self.source("common1.c", "int common; int read(void){return common;}")
        second = self.source("common2.c", "int common; int read(void); int main(void){common=7; return read()-7;}")
        self.compile(first, second, "-fcommon", "-o", self.folder / "common")
        execute([self.folder / "common"], timeout=10)
        with self.assertRaises(CompileError):
            self.compile(first, second, "-fno-common", "-o", self.folder / "common")

    def test_configuration_and_legacy(self):
        source = self.source("test.c", "static int value=4; int main(void){return value-4;}")
        folder = self.compile(source, "-S", "-o", self.folder / "test.s")
        data = json.loads((folder / "csyntax.json").read_text())
        malformed = self.folder / "input.json"
        target = self.folder / "output.json"
        mutations = [lambda value: value["configuration"].update(pic="true"),
                     lambda value: value["configuration"].update(pie=True),
                     lambda value: value["configuration"].update(unrecognized=False),
                     lambda value: value["configuration"].pop("common"),
                     lambda value: value["configuration"]["symbols"].append(value["configuration"]["symbols"][0]),
                     lambda value: value["configuration"]["symbols"][0][1].update(storage="bogus"),
                     lambda value: value["configuration"]["symbols"][0][1].update(size="9223372036854775808"),
                     lambda value: value.update(format="compcert4lean-prototype-v1")]
        for mutate in mutations:
            value = copy.deepcopy(data)
            mutate(value)
            malformed.write_text(json.dumps(value))
            with self.assertRaises(CompileError):
                execute([LEAN, malformed, target], timeout=30)
        data.pop("configuration")
        data["format"] = "compcert4lean-prototype-v1"
        malformed.write_text(json.dumps(data))
        execute([LEAN, malformed, target], timeout=30)
        self.assertEqual(json.loads(target.read_text())["format"], data["format"])
        printer = self.folder / "printer"
        printer.mkdir()
        bridge = Bridge(self.root, printer, time.monotonic() + 30)
        try:
            bridge.request({"root": str(self.root), "source": str(source), "preprocessor": [],
                            "preprocessed": str(printer / "input.i"), "csyntax": str(printer / "csyntax.json")})
            execute([LEAN, printer / "csyntax.json", target], timeout=30)
            data = json.loads(target.read_text())
            data["configuration"]["pic"] = True
            target.write_text(json.dumps(data))
            with self.assertRaises(CompileError):
                bridge.request({"operation": "print", "input": str(target), "output": str(printer / "output.s")})
        finally:
            bridge.close()
        self.assertIn(b"inconsistent assembly relocation", (printer / "bridge.stderr").read_bytes())
        legacy = self.folder / "legacy-printer"
        legacy.mkdir()
        bridge = Bridge(self.root, legacy, time.monotonic() + 30)
        try:
            bridge.request({"root": str(self.root), "source": str(source), "preprocessor": [],
                            "preprocessed": str(legacy / "input.i"), "csyntax": str(legacy / "csyntax.json")})
            data = json.loads((legacy / "csyntax.json").read_text())
            data["format"] = "compcert4lean-prototype-v1"
            data.pop("configuration")
            malformed.write_text(json.dumps(data))
            execute([LEAN, malformed, target], timeout=30)
            bridge.request({"operation": "print", "input": str(target), "output": str(legacy / "output.s")})
        finally:
            bridge.close()
        self.assertTrue((legacy / "output.s").exists())

    def test_reporting_failures(self):
        stages = Stages(self.folder, self.root, suite_options(["--run-timeout", "0.1"]))
        for category, action in [
            ("incorrect_output", lambda: compare_bytes(b"wrong stdout", b"expected", "stdout")),
            ("incorrect_output", lambda: compare_bytes(b"wrong image", b"expected", "output file"))]:
            with self.assertRaises(CompileError):
                stages.call("compare", category, action)
            self.assertEqual(stages.records[-1]["category"], category)
        with self.assertRaises(CompileError):
            stages.command("execute", [sys.executable, "-c", "import time; time.sleep(5)"])
        self.assertEqual(stages.records[-1]["status"], "timeout")
        with self.assertRaises(CompileError):
            stages.command("reference-interpreter", [sys.executable, "-c", "raise SystemExit(7)"], category="reference_failure")
        self.assertEqual(stages.records[-1]["category"], "reference_failure")
        summary = {"selected": ["deliberate/fail"], "finished": "test", "cases": [{"id": "deliberate/fail", "verdict": "fail", "lean": {"verdict": "fail", "error": "wrong stdout"},
                              "reference": {"verdict": "unavailable", "error": "reference failed"}}], "exclusions": []}
        write_report(self.folder, summary)
        self.assertFalse(summary["success"])
        self.assertEqual(summary["counts"]["fail"], 1)
        self.assertTrue((self.folder / "report.md").exists())

    def test_pipeline_failure_verdicts(self):
        corpus = self.folder / "corpus"
        (corpus / "regression").mkdir(parents=True)
        (corpus / "endian.h").write_text("")
        (corpus / "expected").write_bytes(b"expected bytes\n")
        cases = [
            ("invalid", "int main( {", {"kind": "exit"}, "fail", "frontend_rejection"),
            ("stdout", "int main(void){return 0;}", {"kind": "stdout", "expected": "expected"}, "fail", "incorrect_output"),
            ("image", '#include <stdio.h>\nint main(void){FILE *out=fopen("image", "w"); fputs("wrong", out); fclose(out); return 0;}',
             {"kind": "file", "expected": "expected", "actual": "image"}, "fail", "incorrect_output"),
            ("timeout", "int main(void){volatile int value=1; while(value){} return 0;}", {"kind": "exit"}, "timeout", "execution_failure"),
            ("reference", "int main(void){return 0;}", {"kind": "interpreter"}, "unavailable", "reference_failure")]
        for name, source, check, verdict, category in cases:
            (corpus / "regression" / (name + ".c")).write_text(source)
            case = {"id": "regression/" + name, "group": "regression", "sources": ["regression/" + name + ".c"],
                    "flags": [], "check": check}
            original = Stages.command
            def command(stages, stage, *args, **kwargs):
                if stage == "reference-interpreter":
                    return original(stages, stage, [sys.executable, "-c", "raise SystemExit(3)"], category="reference_failure")
                return original(stages, stage, *args, **kwargs)
            with self.subTest(name=name), patch("small_tests.CORPUS", corpus), patch.object(Stages, "command", command):
                result = run_pipeline(case, "lean", self.folder / name, self.root,
                                      suite_options(["--run-timeout", "0.1"]), corpus)
                self.assertEqual(result["verdict"], verdict)
                self.assertEqual(result["category"], category)
                if name == "invalid":
                    self.assertEqual(result["stage_status"]["execute"], "blocked")


if __name__ == "__main__":
    unittest.main(verbosity=2)
