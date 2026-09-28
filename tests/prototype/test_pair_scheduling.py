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
static volatile unsigned observed;

static __attribute__((noinline)) unsigned independent(unsigned first, unsigned second, unsigned third) {
  unsigned inverted = ~first;
  unsigned product = second * third;
  return inverted ^ product;
}

static __attribute__((noinline)) unsigned shared(unsigned first, unsigned second, unsigned third,
                                                unsigned retained, unsigned choose) {
  if (choose) retained = ~first;
  unsigned product = second * third;
  return retained ^ product;
}

static __attribute__((noinline)) unsigned dependent(unsigned first, unsigned second) {
  unsigned inverted = ~first;
  unsigned product = inverted * second;
  return inverted ^ product;
}

static __attribute__((noinline)) unsigned guarded(unsigned first, unsigned second, unsigned divisor) {
  if (!divisor) return first;
  unsigned inverted = ~first;
  unsigned quotient = second / divisor;
  return inverted ^ quotient;
}

static __attribute__((noinline)) unsigned effects(unsigned *left, unsigned *right, unsigned value) {
  unsigned first = ~value;
  *left = first;
  unsigned second = *right;
  observed = first;
  observed ^= second;
  return first * second;
}

static __attribute__((noinline)) double floating(double first, double second, double third) {
  double square = first * first;
  double product = second * third;
  return square + product;
}

int main(int argc, char **argv) {
  unsigned seed = (unsigned)argc * 2654435761u;
  unsigned result = 0;
  for (unsigned index = 0; index < 64; ++index) {
    unsigned first = seed + index;
    unsigned second = first ^ 0x80000000u;
    unsigned third = index * 13u + 1u;
    unsigned cells[2] = {first, second};
    result ^= independent(first, second, third);
    result ^= shared(first, second, third, seed, index & 1u);
    result ^= dependent(first, second);
    result ^= guarded(first, second, index & 7u);
    result ^= effects(&cells[0], &cells[index & 1u], third);
    printf("%u %u %u\n", result, cells[0], observed);
  }
  for (int index = -8; index <= 8; ++index) {
    double first = (double)index / 16.0;
    double second = (double)argc + first;
    printf("%a %a\n", floating(first, second, -0.5), floating(-0.0, first, second));
  }
  return 0;
}
"""


class PairSchedulingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        prepare(REPO.parent / "CompCert")
        cls.folder = Path(tempfile.mkdtemp(prefix="pair-scheduling-", dir=BUILD))
        print(f"Artifacts: {cls.folder}", flush=True)

    def test_independence_and_pipeline_agreement(self):
        execute(["lake", "env", "lean", "tests/prototype/PairScheduling.lean"], timeout=120)
        source = self.folder / "scheduling.c"
        source.write_text(SOURCE)
        oracle = self.folder / "gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        arguments = [["argument"] * count for count in range(10)]
        expected = [execute([oracle, *values], timeout=10) for values in arguments]
        for level in ("O0", "O2"):
            artifact = self.folder / level
            executable = self.folder / (level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            self.assertEqual([execute([executable, *values], timeout=10) for values in arguments], expected)
            target = artifact / "diagnostic-asm.json"
            execute([LEAN, "--diagnose", artifact / "csyntax.json", target, artifact / "passes"], timeout=60)
            self.assertEqual(json.loads(target.read_text())["program"],
                             json.loads((artifact / "asm.json").read_text())["program"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
