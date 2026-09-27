# Tests

Run these commands from the repository root after the setup in
[PROTOTYPE.md](../PROTOTYPE.md):

```sh
lake build allocatorTests coreDiagnostics
.lake/build/bin/allocatorTests
.lake/build/bin/coreDiagnostics
python3 tests/allocator/test_interchange.py
python3 tests/prototype/test_framework.py
python3 tests/prototype/test_batch.py
python3 tests/prototype/test_c_standard.py
python3 tests/prototype/test_optimization.py
python3 tests/prototype/test_small_inlining.py
python3 tests/prototype/test_loop_unroll.py
python3 tests/prototype/test_benchmarks.py
python3 scripts/smoke_test.py
python3 scripts/small_tests.py --optimization O0
python3 scripts/small_tests.py --optimization O2
python3 scripts/benchmarks.py
```

[small-tests/SUITE.md](small-tests/SUITE.md) describes the imported correctness
corpus, expected outputs, exclusions, stage deadlines and reporting.
[optimization/README.md](optimization/README.md) describes the compiler runtime
regressions. `python3 tests/prototype/verify_o2.py` combines the focused O2,
allocator, smoke, codec, build and transitive axiom checks.

Generated artifacts stay under the ignored `.lake/` directory. Historical run
reports, agent logs and archive tooling are maintained in `compcert-lean-meta`
under `investigations/compiler-validation/` and `scripts/`.
