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

    def test_leaf_with_bounded_local_stack(self):
        source = self.folder / "local-stack.c"
        source.write_text(
            "#include <stdio.h>\n"
            "static unsigned local(unsigned value) {\n"
            "  unsigned slots[4];\n"
            "  slots[0] = value; slots[1] = value * 3u + 5u;\n"
            "  slots[2] = slots[0] ^ slots[1];\n"
            "  slots[3] = value >> 3;\n"
            "  return slots[1] + slots[2] + slots[value & 3u];\n"
            "}\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u\\n\", local(argc), local(argc + 1));\n"
            "  return 0;\n"
            "}\n")
        oracle = self.folder / "local-stack-gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(6)]
        expected = [execute([oracle, *args], timeout=10) for args in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / ("local-stack-" + level)
            executable = self.folder / ("local-stack-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *args], timeout=10) for args in arguments], expected)
            assembly = (artifact / "output.s").read_text()
            if level == "O2":
                self.assertNotRegex(assembly, r"\bcall\s+local\b")
                self.assertNotRegex(assembly, r"(?m)^local:")
            else:
                self.assertRegex(assembly, r"\bcall\s+local\b")

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
