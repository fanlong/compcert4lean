"""Small leaf inlining preserves explicit controls and executable behavior."""

from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, REPO, compile_source, execute, prepare


class SmallInliningTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = REPO.parent / "CompCert"
        prepare(cls.root)
        cls.folder = Path(tempfile.mkdtemp(prefix="small-inlining-", dir=BUILD))
        print(f"Artifacts: {cls.folder}", flush=True)

    def test_repeated_leaf_and_noinline(self):
        source = self.folder / "leaf.c"
        source.write_text(
            "extern int printf(const char *, ...);\n"
            "static int leaf(int value) { return value * 3 + 5; }\n"
            "static __attribute__((noinline)) int kept(int value) { return value * 7; }\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%d %d %d %d\\n\", leaf(argc), leaf(argc + 1), kept(argc), kept(argc + 1));\n"
            "  return 0;\n"
            "}\n")
        for level in ("O0", "O2"):
            artifact = self.folder / level
            executable = self.folder / (level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual(execute([executable], timeout=10), b"8 11 7 14\n")
            self.assertEqual(execute([executable, "argument"], timeout=10), b"11 14 14 21\n")
            assembly = (artifact / "output.s").read_text()
            self.assertRegex(assembly, r"\bcall\s+kept\b")
            if level == "O2":
                self.assertNotRegex(assembly, r"\bcall\s+leaf\b")
                self.assertNotRegex(assembly, r"(?m)^leaf:")
            else:
                self.assertRegex(assembly, r"\bcall\s+leaf\b")

    def test_calls_and_large_functions_remain_bounded(self):
        source = self.folder / "bounded.c"
        operations = "\n".join(f"  value = value * 33u + {index}u;" for index in range(40))
        source.write_text(
            "#include <stdio.h>\n"
            "static volatile unsigned sink;\n"
            "static unsigned large(unsigned value) {\n" + operations + "\n  return value;\n}\n"
            "static unsigned with_call(unsigned value) { sink = value; return large(value); }\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u %u %u\\n\", large(argc), large(argc + 1), with_call(argc), with_call(argc + 1));\n"
            "  return 0;\n"
            "}\n")
        outputs = []
        for level in ("O0", "O2"):
            artifact = self.folder / ("bounded-" + level)
            executable = self.folder / ("bounded-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            outputs.append([execute([executable], timeout=10), execute([executable, "argument"], timeout=10)])
            assembly = (artifact / "output.s").read_text()
            self.assertIsNotNone(re.search(r"(?m)^large:", assembly))
            self.assertIsNotNone(re.search(r"(?m)^with_call:", assembly))
        self.assertEqual(outputs[0], outputs[1])


if __name__ == "__main__":
    unittest.main(verbosity=2)
