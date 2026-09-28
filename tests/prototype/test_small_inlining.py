"""Bounded inlining preserves explicit controls and executable behavior."""

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


    def test_looping_nonleaf_remains_outlined(self):
        source = self.folder / "nonleaf-loop.c"
        source.write_text(
            "extern int printf(const char *, ...);\n"
            "static __attribute__((noinline)) unsigned step(unsigned value) { return value * 33u + 7u; }\n"
            "static unsigned looped(unsigned count, unsigned value) {\n"
            "  while (count--) value = step(value);\n"
            "  return value;\n"
            "}\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u\\n\", looped(argc - 1u, 2147483647u), looped(argc + 2u, 17u));\n"
            "  return 0;\n"
            "}\n")
        oracle = self.folder / "nonleaf-loop-gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(7)]
        expected = [execute([oracle, *args], timeout=10) for args in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / ("nonleaf-loop-" + level)
            executable = self.folder / ("nonleaf-loop-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *args], timeout=10) for args in arguments], expected)
            self.assertRegex((artifact / "output.s").read_text(), r"\bcall\s+looped\b")

    def test_small_call_chains_and_recursion(self):
        source = self.folder / "nonleaf.c"
        source.write_text(
            "extern int printf(const char *, ...);\n"
            "static __attribute__((noinline)) unsigned kept(unsigned value) { return value * 7u; }\n"
            "static unsigned middle(unsigned value) { return kept(value) + 3u; }\n"
            "static unsigned outer(unsigned value) { return middle(value) ^ middle(value + 1u); }\n"
            "static unsigned descend(unsigned depth, unsigned value) {\n"
            "  if (!depth) return value;\n"
            "  return (descend(depth - 1u, value * 33u + depth) ^ (value >> 3)) + depth;\n"
            "}\n"
            "static unsigned branching(unsigned depth, unsigned value) {\n"
            "  if (!depth) return value;\n"
            "  return branching(depth - 1u, value + depth) ^ branching(depth - 1u, value * 3u);\n"
            "}\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u %u %u\\n\", outer(argc), outer((unsigned)argc + 2147483647u),\n"
            "    descend((unsigned)argc + 2u, 4294967295u), branching((unsigned)argc, 123u));\n"
            "  return 0;\n}\n")
        oracle = self.folder / "nonleaf-gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(7)]
        expected = [execute([oracle, *args], timeout=10) for args in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / ("nonleaf-" + level)
            executable = self.folder / ("nonleaf-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *args], timeout=10) for args in arguments], expected)
            assembly = (artifact / "output.s").read_text()
            self.assertRegex(assembly, r"\bcall\s+kept\b")
            if level == "O2":
                self.assertNotRegex(assembly, r"(?m)^(middle|outer):")
            else:
                self.assertRegex(assembly, r"\bcall\s+outer\b")

    def test_prior_eligibility_survives_large_callers(self):
        source = self.folder / "inline-priority.c"
        operations = "\n".join(
            f"  value = (value ^ (value >> {index % 7 + 1})) * 33u + {index + 3}u;"
            for index in range(70))
        source.write_text(
            "extern int printf(const char *, ...);\n"
            "static __attribute__((noinline)) unsigned kept(unsigned value) { return value * 7u; }\n"
            "static __inline__ unsigned requested(unsigned value) { return kept(value) + 3u; }\n"
            "static __inline__ unsigned bridge(unsigned value) { return requested(value) + 5u; }\n"
            "static unsigned once(unsigned value) { return kept(value) ^ 17u; }\n"
            "static __attribute__((noinline)) unsigned many(unsigned value) {\n"
            "  unsigned result = bridge(value);\n" + operations + "\n"
            "  return result ^ requested(value) ^ once(value + 1u);\n}\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u\\n\", many(argc), many((unsigned)argc + 2147483647u));\n"
            "  return 0;\n}\n")
        oracle = self.folder / "inline-priority-gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(7)]
        expected = [execute([oracle, *args], timeout=10) for args in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / ("inline-priority-" + level)
            executable = self.folder / ("inline-priority-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *args], timeout=10) for args in arguments], expected)
            assembly = (artifact / "output.s").read_text()
            self.assertRegex(assembly, r"\bcall\s+kept\b")
            if level == "O2":
                self.assertNotRegex(assembly, r"\bcall\s+(requested|bridge|once)\b")
            else:
                self.assertRegex(assembly, r"\bcall\s+requested\b")
                self.assertRegex(assembly, r"\bcall\s+once\b")

    def test_new_wrappers_bound_nested_expansion(self):
        source = self.folder / "nested-budget.c"
        operations = "\n".join(
            f"  value = (value ^ (value >> {index % 7 + 1})) * 33u + {index + 3}u;"
            for index in range(70))
        source.write_text(
            "extern int printf(const char *, ...);\n"
            "static __attribute__((noinline)) unsigned kept(unsigned value) { return value * 7u; }\n"
            "static __inline__ unsigned large(unsigned value) {\n" + operations + "\n"
            "  return kept(value);\n}\n"
            "static unsigned wrapper(unsigned value) { return large(value); }\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u\\n\", wrapper(argc), wrapper((unsigned)argc + 2147483647u));\n"
            "  return 0;\n}\n")
        oracle = self.folder / "nested-budget-gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(7)]
        expected = [execute([oracle, *args], timeout=10) for args in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / ("nested-budget-" + level)
            executable = self.folder / ("nested-budget-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *args], timeout=10) for args in arguments], expected)
            assembly = (artifact / "output.s").read_text()
            if level == "O2":
                self.assertNotRegex(assembly, r"\bcall\s+wrapper\b")
                self.assertRegex(assembly, r"\bcall\s+large\b")
            else:
                self.assertRegex(assembly, r"\bcall\s+wrapper\b")

    def test_repeated_nonleaf_expansions_share_budget(self):
        source = self.folder / "nonleaf-budget.c"
        operations = "\n".join(
            f"  value = (value ^ (value >> {index + 1})) * 33u + {index + 3}u;"
            for index in range(3))
        calls = "\n".join(f"  result ^= middle(value + {index}u);" for index in range(40))
        source.write_text(
            "extern int printf(const char *, ...);\n"
            "static __attribute__((noinline)) unsigned kept(unsigned value) { return value * 7u; }\n"
            "static unsigned middle(unsigned value) {\n" + operations + "\n  return kept(value) + 3u;\n}\n"
            "static __attribute__((noinline)) unsigned many(unsigned value) {\n"
            "  unsigned result = 0;\n" + calls + "\n  return result;\n}\n"
            "int main(int argc, char **argv) {\n"
            "  printf(\"%u %u\\n\", many(argc), many((unsigned)argc + 2147483647u));\n"
            "  return 0;\n}\n")
        oracle = self.folder / "nonleaf-budget-gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(6)]
        expected = [execute([oracle, *args], timeout=10) for args in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / ("nonleaf-budget-" + level)
            executable = self.folder / ("nonleaf-budget-" + level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *args], timeout=10) for args in arguments], expected)
            assembly = (artifact / "output.s").read_text()
            remaining = len(re.findall(r"\bcall\s+middle\b", assembly))
            self.assertGreater(remaining, 0)
            if level == "O2":
                self.assertLess(remaining, 40)


if __name__ == "__main__":
    unittest.main(verbosity=2)
