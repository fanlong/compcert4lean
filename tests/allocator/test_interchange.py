"""Allocator context and pre-expansion compatibility integration checks."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, LEAN, REPO, Bridge, CompileError, compile_source, execute, prepare, tool_environment


class AllocatorInterchangeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = REPO.parent / "CompCert"
        prepare(cls.root)
        cls.folder = Path(tempfile.mkdtemp(prefix="allocator-interchange-", dir=BUILD))
        print(f"Artifacts: {cls.folder}", flush=True)

    def test_builtin_placement(self):
        result = execute([BUILD / "bridge" / "bridge", "--test-builtin-placement"],
                         env=tool_environment(self.root), timeout=10)
        self.assertIn(b"builtin placement tests: PASS", result)

    def test_reserved_registers_and_validation(self):
        source = self.folder / "reserved.c"
        source.write_text('#pragma reserve_register R12\n#pragma reserve_register RBX\n'
                          '#pragma reserve_register R12\nint main(void){return 0;}\n')
        artifacts = self.folder / "compile"
        compile_source(parse_args([str(source), "-o", str(self.folder / "reserved")]),
                       prepared=True, artifact_dir=artifacts)
        execute([self.folder / "reserved"], timeout=10)
        data = json.loads((artifacts / "csyntax.json").read_text())
        self.assertEqual(data["allocationContext"], {"reserved": ["R12", "RBX"]})
        self.assertEqual(json.loads((artifacts / "asm.json").read_text())["allocationContext"],
                         data["allocationContext"])
        malformed = self.folder / "malformed.json"
        target = self.folder / "output.json"
        for context in [None, {}, {"reserved": ["RAX"]}, {"reserved": ["rbx"]},
                        {"reserved": ["R12", "R12"]}, {"reserved": "R12"},
                        {"reserved": ["R12"], "extra": True}]:
            modified = copy.deepcopy(data)
            modified["allocationContext"] = context
            malformed.write_text(json.dumps(modified))
            with self.assertRaises(CompileError):
                execute([LEAN, malformed, target], timeout=10)
        for version in ["compcert4lean-prototype-v1", "compcert4lean-prototype-v2"]:
            modified = copy.deepcopy(data)
            modified.pop("allocationContext")
            modified["format"] = version
            if version.endswith("v1"):
                modified.pop("configuration")
            else:
                modified["configuration"].pop("optimization")
                modified["configuration"].pop("functions")
            malformed.write_text(json.dumps(modified))
            execute([LEAN, malformed, target], timeout=10)
            self.assertNotIn("allocationContext", json.loads(target.read_text()))
        printer = self.folder / "snapshot"
        printer.mkdir()
        bridge = Bridge(self.root, printer, time.monotonic() + 30)
        try:
            bridge.request({"root": str(self.root), "source": str(source), "preprocessor": [],
                            "preprocessed": str(printer / "source.i"), "csyntax": str(printer / "source.json")})
            execute([LEAN, printer / "source.json", target], timeout=10)
            modified = json.loads(target.read_text())
            modified["allocationContext"] = {"reserved": []}
            target.write_text(json.dumps(modified))
            with self.assertRaises(CompileError):
                bridge.request({"operation": "print", "input": str(target), "output": str(printer / "output.s")})
        finally:
            bridge.close()
        self.assertIn(b"inconsistent reserved-register", (printer / "bridge.stderr").read_bytes())
        self.assertFalse((printer / "output.s").exists())


if __name__ == "__main__":
    unittest.main()
