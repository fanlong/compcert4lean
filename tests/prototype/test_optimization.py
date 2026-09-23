"""Optimization profiles, frontend metadata, and executable pass witnesses."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, LEAN, REPO, Bridge, CompileError, compile_source, execute, prepare, reference_flags


class OptimizationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = REPO.parent / "CompCert"
        prepare(cls.root)
        cls.folder = Path(tempfile.mkdtemp(prefix="optimization-", dir=BUILD))
        print(f"Artifacts: {cls.folder}", flush=True)

    def test_aliases_and_order(self):
        for flags, expected in [([], "O0"), (["-O0"], "O0"), (["-O"], "O2"),
                                (["-O1"], "O2"), (["-O2"], "O2"), (["-O3"], "O2"),
                                (["-O3", "-O0"], "O0"), (["-O0", "-O"], "O2")]:
            self.assertEqual(parse_args(["test.c", *flags]).optimization, expected)
        for flag in ["-O4", "-Os", "-Og", "-Ofast", "-Obranchless", "-fno-inline", "-march=native"]:
            with self.assertRaises(SystemExit):
                parse_args(["test.c", flag])
        self.assertIn("-finline", reference_flags("O2"))
        self.assertIn("-fno-inline", reference_flags("O0"))

    def test_metadata_and_activation(self):
        source = self.folder / "inline.c"
        source.write_text("static inline int declared(int value){return value+1;}\n"
                          "static __attribute__((noinline)) int kept(int value){return value+2;}\n"
                          "static int once(int value){return declared(value)+3;}\n"
                          "int main(void){return once(4)+kept(5)-15;}\n")
        records = {}
        for flag in ["-O0", "-O", "-O1", "-O2", "-O3"]:
            folder = self.folder / flag[1:]
            executable = self.folder / (flag[1:] + ".exe")
            compile_source(parse_args([str(source), flag, "-o", str(executable)]), prepared=True, artifact_dir=folder)
            execute([executable], timeout=10)
            records[flag] = json.loads((folder / "csyntax.json").read_text())
            assembly = (folder / "output.s").read_text()
            self.assertIn("kept:", assembly)
            if flag == "-O0":
                self.assertIn("once:", assembly)
            else:
                self.assertNotIn("once:", assembly)
                self.assertNotIn("declared:", assembly)
                report = folder / "allocation.json"
                execute([LEAN, "--allocator-report", folder / "csyntax.json", report], timeout=30)
                self.assertTrue(json.loads(report.read_text()))
                with self.assertRaisesRegex(CompileError, "[Ii]nvalid register allocation"):
                    execute([LEAN, "--test-invalid-allocation", folder / "csyntax.json"], timeout=30)
        data = records["-O2"]
        self.assertEqual(data["format"], "compcert4lean-prototype-v3")
        self.assertEqual(data["configuration"]["optimization"], "O2")
        facts = [entry for _, entry in data["configuration"]["functions"]]
        self.assertIn({"inline": "inline", "static": True}, facts)
        self.assertIn({"inline": "noinline", "static": True}, facts)
        self.assertIn({"inline": "none", "static": True}, facts)
        mutations = [lambda value: value["configuration"].update(optimization="O3"),
                     lambda value: value["configuration"].update(optimization=True),
                     lambda value: value["configuration"].pop("optimization"),
                     lambda value: value.update(target="x86_64-linux-sysv-O0"),
                     lambda value: value["configuration"]["functions"].pop(),
                     lambda value: value["configuration"]["functions"].append(value["configuration"]["functions"][0]),
                     lambda value: value["configuration"]["functions"][0][1].update(inline="always"),
                     lambda value: value["configuration"]["functions"][0][1].update(static="true")]
        for mutate in mutations:
            modified = copy.deepcopy(data)
            mutate(modified)
            path = self.folder / "malformed.json"
            path.write_text(json.dumps(modified))
            with self.assertRaises(CompileError):
                execute([LEAN, path, self.folder / "target.json"], timeout=30)

    def test_optimized_printer_snapshot(self):
        folder = self.folder / "printer-profile"
        folder.mkdir()
        source = folder / "source.c"
        source.write_text("int main(void){return 0;}\n")
        bridge = Bridge(self.root, folder, time.monotonic() + 30)
        try:
            bridge.request({"root": str(self.root), "source": str(source), "preprocessor": [],
                            "configuration": {"pic": False, "pie": False, "common": False, "optimization": "O2"},
                            "preprocessed": str(folder / "input.i"), "csyntax": str(folder / "source.json")})
            target = folder / "target.json"
            execute([LEAN, "--diagnose", folder / "source.json", target, folder / "passes"], timeout=30)
            for tag in range(9):
                self.assertTrue((folder / "passes" / f"rtl-{tag}.json").is_file())
            data = json.loads(target.read_text())
            data["configuration"]["optimization"] = "O0"
            target.write_text(json.dumps(data))
            with self.assertRaises(CompileError):
                bridge.request({"operation": "print", "input": str(target), "output": str(folder / "output.s")})
        finally:
            bridge.close()
        self.assertIn(b"inconsistent assembly relocation configuration", (folder / "bridge.stderr").read_bytes())


if __name__ == "__main__":
    unittest.main(verbosity=2)
