"""Batch preparation, per-job flags and failure reporting."""

import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
import compile_batch
from compile_c import parse_args
from prototype import BUILD, compile_source, execute


class BatchTests(unittest.TestCase):
    def test_objects_flags_link_and_failed_job(self):
        BUILD.mkdir(parents=True, exist_ok=True)
        folder = Path(tempfile.mkdtemp(prefix="batch-test-", dir=BUILD))
        print(f"Artifacts: {folder}", flush=True)
        (folder / "value.c").write_text("int value(void) { return VALUE; }\n")
        (folder / "main.c").write_text("int value(void); int main(void) { return value() != 37; }\n")
        (folder / "bad.c").write_text("#error intentional batch failure\n")
        arguments = [
            ["-O0", "-DVALUE=37", "-c", "value.c", "-o", "value.o", "--keep-temps"],
            ["-O2", "-std=c18", "-c", "main.c", "-o", "main.o"],
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
        self.assertEqual(json.loads((folder / "results/results.json").read_text()), result)

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
