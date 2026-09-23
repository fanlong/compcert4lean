# Initial complete baseline

Run: 2026-09-23 UTC (2026-09-22 America/Los_Angeles), Linux System V x86-64,
O0, spill allocator, one concurrent case, 300-second stage limits, ABI seed
20260922. All 140 applicable cases completed: **131 passed, nine failed, zero
timeouts, zero unavailable verdicts**, with eight justified exclusion entries.
Lean passed 131/140; pinned CompCert passed 139/140. The runner returned 1 as
required for this failure baseline.

The nine failures are:

| Cases | Observed failure |
| --- | --- |
| `regression/struct7`, `raytracer/render` | Lean executables terminate with SIGSEGV. |
| `regression/varargs1`, `regression/varargs2`, `regression/varargs3`, `abi/vararg-native`, `abi/vararg-gcc_to_native` | CompCert assembly expansion rejects the Lean-generated construct at `x86/Asmexpand.ml:475`. |
| `regression/annot1` | Lean spill allocator rejects unsupported builtin register requirements. |
| `regression/alias` | Both Lean and pinned CompCert print `Test 8: 1`; unchanged upstream output expects `Test 8: 0`. The source describes this test's wild pointer arithmetic and optimizer-dependent behavior. O0 and upstream expected bytes are preserved. |

`report.md` lists every case and exclusion. `results.json` contains the full
machine-readable report, stage outcomes, commands, flags, exact tool versions,
source hashes, generated fixture hashes and original artifact locations.
`evidence.tar.gz` preserves all command stdout/stderr and protocol logs,
generated ABI sources, failed-case preprocessed sources, interchange and
assembly, plus the guarded verification records. `evidence.json` records each
archived file's SHA-256 and the archive hash. Archive paths are relative to the
run, except the separate `verification/` subtree.

The full working run is retained at
`.lake/prototype/small-tests-iqmql520/`. Reproduce it with:

```sh
python3 scripts/guarded.py python3 scripts/small_tests.py
```

Framework verification passed: the unchanged three-program smoke command and
its integration checks, seven targeted framework/reporting tests, PIC shared
dependencies and dynamic loading, and a two-case-concurrency run of smoke/PIC
selections. The combined Lean build passed (350 jobs); codec generation checks
and bit-roundtrip checks passed. Transitive axiom checks for changed adapters
contain only `propext`, `Classical.choice`, and `Quot.sound`. Compiler passes,
validators, theorem statements, existing proofs and proof ledgers are unchanged.

The build/trust/codec evidence is the archive's
`verification/20260922T235735-9ed0927b/`; final framework/smoke/full-suite evidence
is `verification/20260923T000003-cfe50048/`. That second guarded command exits 1
because the complete suite reports the nine compiler/test failures above;
framework and smoke checks earlier in the same command passed. Both shared
compute invocations recorded admission at 26 GiB, no swap, group OOM semantics,
and complete descendant drain.

Compiler repairs for these failures are a separate task. No expected result
was replaced, failure suppressed, or reference compiler substituted for Lean.
