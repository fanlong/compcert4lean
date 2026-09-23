"""C standard selection reaches preprocessing and the CompCert frontend."""

import contextlib
import io
import json
import tempfile
import time
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, Bridge, CompileError, compile_source, execute, prepare


class CStandardTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(__file__).resolve().parents[3] / "CompCert"
        prepare(cls.root)
        cls.artifacts = Path(tempfile.mkdtemp(prefix="c-standard-", dir=BUILD))
        print(f"Artifacts: {cls.artifacts}", flush=True)

    def test_default_is_c99(self):
        self.assertEqual(parse_args(["input.c"]).std, "c99")
        self.assertEqual(parse_args(["input.c", "-std", "c18"]).std, "c18")
        self.assertEqual(parse_args(["input.c", "-std=c18", "-std=c99"]).std, "c99")

    def test_supported_standards_are_forwarded(self):
        for standard, version in [(None, 199901), ("c99", 199901), ("c11", 201112), ("c18", 201710)]:
            with self.subTest(standard=standard):
                folder = self.artifacts / (standard or "default")
                folder.mkdir()
                source = folder / "standard.c"
                source.write_text(f'#if __STDC_VERSION__ != {version}L\n#error wrong standard\n#endif\n'
                                  '_Static_assert(sizeof(int) == 4, "int size");\n'
                                  '_Alignas(8) int value;\n'
                                  'int main(void){return 0;}\n')
                flags = ["-std=" + standard] if standard else []
                output = folder / "program"
                options = parse_args([str(source), *flags, "-o", str(output),
                                      "--compcert-root", str(self.root)])
                artifacts = folder / "artifacts"
                compile_source(options, prepared=True, artifact_dir=artifacts)
                execute([output], timeout=10, log=folder / "execute")
                metadata = json.loads((artifacts / "result.json").read_text())
                self.assertEqual(metadata["standard"], standard or "c99")
                request = json.loads((artifacts / "bridge-protocol.jsonl").read_text().splitlines()[0])["request"]
                self.assertEqual(request["standard"], standard or "c99")
                warnings = (artifacts / "bridge.stderr").read_text()
                self.assertEqual("C11 extension" in warnings, standard in (None, "c99"))
                source_json = json.loads((artifacts / "csyntax.json").read_text())
                self.assertNotIn("standard", source_json)
                self.assertNotIn("standard", source_json["configuration"])

    def test_invalid_standard_is_rejected(self):
        for flags in [["-std=c17"], ["-std=c23"], ["-std=gnu99"], ["-std="], ["-std"]]:
            with self.subTest(flags=flags), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                parse_args(["input.c", *flags])

    def test_bridge_rejects_invalid_standard(self):
        folder = self.artifacts / "invalid-bridge"
        folder.mkdir()
        bridge = Bridge(self.root, folder, time.monotonic() + 30)
        try:
            with self.assertRaisesRegex(CompileError, "invalid C standard"):
                bridge.request({"root": str(self.root), "standard": "c23"})
        finally:
            bridge.close()


if __name__ == "__main__":
    unittest.main()
