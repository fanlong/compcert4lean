"""Loop duplication exercises control flow, boundary counts, and diagnostics."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from compile_c import parse_args
from prototype import BUILD, LEAN, REPO, compile_source, execute, prepare


SOURCE = r"""
extern int printf(const char *, ...);
extern unsigned long strtoul(const char *, char **, int);
static unsigned values[128];
static volatile unsigned seed = 29;

static __attribute__((noinline)) unsigned arithmetic(unsigned count, unsigned gain) {
  unsigned result = seed;
  for (unsigned index = 0; index < count; ++index)
    result += values[index & 127] * gain + gain * gain;
  return result;
}

static __attribute__((noinline)) unsigned nested(unsigned count) {
  unsigned result = 0;
  for (unsigned outer = 0; outer < count; ++outer) {
    for (unsigned inner = 0; inner < 7; ++inner) {
      if ((inner + outer) % 5 == 0) continue;
      result += (inner + 3) * values[outer & 127];
      if (result & 32768) break;
    }
  }
  return result;
}

static __attribute__((noinline)) unsigned irreducible(unsigned count) {
  unsigned index = 0, result = seed;
  if (count & 1) goto alternate;
  for (; index < count; ++index) {
    result += index * 13;
  alternate:
    result ^= index * 17 + 3;
  }
  return result;
}

static __attribute__((noinline)) unsigned effect(unsigned index) {
  seed += index;
  return seed;
}

static __attribute__((noinline)) unsigned calls(unsigned count) {
  unsigned result = 0;
  for (unsigned index = 0; index < count; ++index) result += effect(index);
  return result;
}

int main(int argc, char **argv) {
  unsigned count = argc > 1 ? (unsigned)strtoul(argv[1], 0, 10) : 0;
  for (unsigned index = 0; index < 128; ++index) values[index] = index * 31 + 11;
  unsigned first = arithmetic(count, 37);
  unsigned second = nested(count);
  unsigned third = irreducible(count);
  unsigned fourth = calls(count);
  printf("%u %u %u %u\n", first, second, third, fourth);
  return 0;
}
"""


class LoopUnrollTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = REPO.parent / "CompCert"
        prepare(cls.root)
        cls.folder = Path(tempfile.mkdtemp(prefix="loop-unroll-", dir=BUILD))
        print(f"Artifacts: {cls.folder}", flush=True)

    def test_boundaries_control_flow_and_diagnostic_pipeline(self):
        source = self.folder / "loops.c"
        source.write_text(SOURCE)
        oracle = self.folder / "gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        counts = [0, 1, 2, 3, 7, 16, 31, 64, 127, 128, 129, 193]
        expected = {count: execute([oracle, str(count)], timeout=10) for count in counts}
        for level in ("O0", "O2"):
            artifact = self.folder / level
            executable = self.folder / (level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            for count in counts:
                self.assertEqual(execute([executable, str(count)], timeout=10), expected[count])
            target = artifact / "diagnostic-asm.json"
            passes = artifact / "passes"
            execute([LEAN, "--diagnose", artifact / "csyntax.json", target, passes], timeout=60)
            self.assertEqual(json.loads(target.read_text())["program"],
                             json.loads((artifact / "asm.json").read_text())["program"])
            before = json.loads((passes / "rtl-4.json").read_text())["details"]
            after = json.loads((passes / "rtl-5.json").read_text())["details"]
            before_nodes = sum(function["nodes"] for function in before)
            after_nodes = sum(function["nodes"] for function in after)
            if level == "O2":
                self.assertGreater(after_nodes, before_nodes)
            else:
                self.assertEqual(after_nodes, before_nodes)


if __name__ == "__main__":
    unittest.main(verbosity=2)
