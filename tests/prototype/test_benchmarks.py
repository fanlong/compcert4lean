"""Benchmark failures must never produce performance ratios."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from benchmarks import PIPELINES, report, workloads


class BenchmarkTests(unittest.TestCase):
    def test_workload_selection(self):
        cases = workloads()
        self.assertEqual(len(cases), 29)
        self.assertEqual(sum(case["group"] == "c" for case in cases), 24)
        self.assertEqual(next(case for case in cases if case["group"] == "spass")["check"]["args"], ["problem.dfg"])

    def test_failed_or_incomplete_samples_have_no_ratio(self):
        for verdict, samples in [("fail", [1.0] * 7), ("pass", [1.0] * 6)]:
            case = {"id": "case", **{name: {"verdict": "pass", "samples": [{"seconds": 2.0}] * 7}
                                       for name in PIPELINES}}
            case["lean"] = {"verdict": verdict, "samples": [{"seconds": value} for value in samples]}
            summary = {"cases": [case], "finished": "test"}
            with tempfile.TemporaryDirectory() as folder:
                report(Path(folder), summary)
                saved = json.loads((Path(folder) / "results.json").read_text())
                self.assertFalse(saved["success"])
                self.assertEqual(saved["cases"][0]["ratios"], {})
                self.assertIn("timing", saved["cases"][0]["reference"])
                self.assertIn("timing", saved["cases"][0]["gcc"])

    def test_startup_measurements_retained_outside_aggregate(self):
        case = {"id": "case", **{name: {"verdict": "pass", "samples": [{"seconds": 0.001}] * 7}
                                   for name in PIPELINES}}
        summary = {"cases": [case]}
        with tempfile.TemporaryDirectory() as folder:
            report(Path(folder), summary)
        self.assertEqual(case["ratios"], {"reference": 1.0, "gcc": 1.0})
        self.assertEqual(summary["aggregate"]["gcc"]["count"], 0)
        self.assertFalse(case["aggregate_eligible"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
