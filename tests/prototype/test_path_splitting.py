"""Path copies keep branch-assigned constants separate until simplification."""

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
static volatile unsigned sink = 19;

static __attribute__((noinline)) unsigned one_path(unsigned value) {
  unsigned gain;
  if (value & 1) {
    sink += value;
    gain = 3;
  } else {
    sink ^= value;
    gain = 13;
  }
  return value * gain + gain * gain;
}

static __attribute__((noinline)) unsigned two_paths(unsigned value) {
  unsigned gain, bias;
  if (value & 1) {
    sink += value;
    gain = 3;
  } else {
    sink ^= value;
    gain = 13;
  }
  if (value & 2) {
    sink += 11;
    bias = 5;
  } else {
    sink ^= 29;
    bias = 17;
  }
  return value * gain + gain * gain + value * bias + bias * bias;
}

static __attribute__((noinline)) unsigned three_paths(unsigned value) {
  unsigned first, second, third;
  if (value & 1) { sink += value; first = 3; }
  else { sink ^= value; first = 13; }
  if (value & 2) { sink += 11; second = 5; }
  else { sink ^= 29; second = 17; }
  if (value & 4) { sink += 31; third = 7; }
  else { sink ^= 43; third = 19; }
  return value * first + first * first + second * second + third * third;
}

int main(int argc, char **argv) {
  unsigned value = argc > 1 ? (unsigned)strtoul(argv[1], 0, 10) : 0;
  unsigned first = one_path(value);
  unsigned second = two_paths(value);
  unsigned third = three_paths(value);
  printf("%u %u %u %u\n", first, second, third, sink);
  return 0;
}
"""


class PathSplittingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        prepare(REPO.parent / "CompCert")
        cls.folder = Path(tempfile.mkdtemp(prefix="path-splitting-", dir=BUILD))
        print(f"Artifacts: {cls.folder}", flush=True)

    def test_branch_constants_and_pipeline_agreement(self):
        source = self.folder / "paths.c"
        source.write_text(SOURCE)
        oracle = self.folder / "gcc.exe"
        execute(["gcc", "-O2", source, "-o", oracle], timeout=30)
        values = [*range(20), 2147483647, 2147483648, 4294967295]
        expected = {value: execute([oracle, str(value)], timeout=10) for value in values}
        for level in ("O0", "O2"):
            artifact = self.folder / level
            executable = self.folder / (level + ".exe")
            compile_source(parse_args([str(source), "-" + level, "-o", str(executable)]),
                           prepared=True, artifact_dir=artifact)
            for value in values:
                self.assertEqual(execute([executable, str(value)], timeout=10), expected[value])
            target = artifact / "diagnostic-asm.json"
            execute([LEAN, "--diagnose", artifact / "csyntax.json", target, artifact / "passes"], timeout=60)
            self.assertEqual(json.loads(target.read_text())["program"],
                             json.loads((artifact / "asm.json").read_text())["program"])
            if level == "O2":
                assembly = (artifact / "output.s").read_text()
                for function in ("one_path", "two_paths"):
                    body = assembly.split("\n" + function + ":", 1)[1].split(".size", 1)[0]
                    self.assertNotRegex(body, r"\bimull\s+%")
                before = json.loads((artifact / "passes/rtl-3.json").read_text())["details"]
                after = json.loads((artifact / "passes/rtl-4.json").read_text())["details"]
                self.assertGreater(sum(function["nodes"] for function in after),
                                   sum(function["nodes"] for function in before))


if __name__ == "__main__":
    unittest.main(verbosity=2)
