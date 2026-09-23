# O2 compiler and benchmark baseline

Investigation and implementation are complete. O2 correctness is **138/139**:
`abi/layout` retains its 300-second timeout and the suite retains exit status 1.
The [failure dossier](failures/cse-predecessor-sharing.md) identifies a frozen
compiler-core performance defect, with an isolated native reproducer. There
are no unresolved runtime, allocator, reference-compiler, or harness failures.

| Validation | Lean | Pinned CompCert | GCC |
| --- | ---: | ---: | ---: |
| O0 correctness | 139/139 | 139/139 | — |
| O2 correctness | 138/139; one diagnosed timeout | 139/139 | — |
| O2 benchmark workloads | 29/29 | 29/29 | 29/29 |

The nine original exclusions, including `regression/alias`, are unchanged.
Both correctness runs use ABI seed `20260922` and 300-second stage deadlines.
See the complete [O0 report](o0/report.md), [O2 report](o2/report.md),
[benchmark tables](benchmarks/report.md), and [acceptance record](acceptance.json).
The historical `tests/small-tests-baseline/` is preserved.

## Compiler behavior

No optimization option still selects O0. `-O`, `-O1`, `-O2`, and `-O3` select
one optimized profile; the last optimization option wins. O2 enables tail
calls, constant propagation, CSE, redundancy elimination, inlining, functions
called once inlining, normal if-conversion, and full floating-point constant
propagation. Size optimization, aggressive branchless mode, and debugging
remain disabled. Interchange v3 carries the normalized profile and frontend
inline/noinline/static facts; legacy v1/v2 remain O0 inputs. Switch compilation
and reachable block ordering follow the pinned x86-64 policies at both levels.

The SPASS timeout exposed repeated allocator degree computation. Caching
active interference degrees fixes it while retaining the allocation validator;
the focused invariant test and full SPASS workload pass. No frozen core
definition, theorem, proof, ledger, imported source, or expected output changed.
The owner-authorized exception and affected runtime scope are in the parent
repository's `agent-log.md`.

## Measurements

All 87 compiler/workload combinations validate their actual input, then run
one warmup and seven measured executions: **609 measured samples**. Measurement
is serial, pinned to logical CPU 0 of an AMD Ryzen 9 5900X, with compiler order
rotated each round. All compilation finishes before timing starts. The shared
guard prevents concurrent project builds. Wall time includes executable
startup; compression time sums its compression and decompression processes.
Compilation times exclude helper builds. Raw samples, standard deviation,
min/max, coefficient of variation, `.text` bytes, commands, hashes, and tool
identities are in [benchmarks/results.json](benchmarks/results.json).

Across 28 eligible rows, geometric mean Lean/CompCert time is **1.003382** and
Lean/GCC time is **1.212857**. Ratios above one mean Lean is slower. `c/integr`
is retained in the tables but excluded from both aggregates because GCC's
median is under 10 ms, a conservative startup-overhead cutoff. No measured
speedup from eliminated benchmark work is claimed. AES, SHA1, SHA3, and SipHash
discard timed results upstream; inspection of all three executables confirms
their workload loops remain. See [work observations](work-observations.json).

The 24 C programs use upstream defaults and supplied inputs. Raytracer runs
`kal.gml` and matches the supplied image. SPASS runs `problem.dfg` and must exit
successfully with `Proof found`; correctness retains the small problem. Each
compression program round-trips 1,048,576 bytes made by repeating and truncating
the vendored `LICENSE`, with input SHA-256
`8265405a9c54e94dff6ec004ab32c813ea4164bc8f0a5fd1c886ed8134e4f37b`.

The target is Linux System V x86-64, non-PIE, with the same libraries. GCC 15.2.0
uses `-O2 -m64 -march=x86-64 -mtune=generic -std=gnu99`; no native CPU tuning,
LTO, or fast-math is used. CompCert is 3.17 at
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`. Lean is 4.33.0, based on
`5f6e959e2598c66b2131b98ed3d76f8f2083dc02` plus the archived source changes.
OCaml is 4.14.2 and Yojson is 2.2.2.

## Attempts and verification

The initial O2 attempt retains both SPASS and ABI timeouts. After the allocator
repair, the second complete run has only the diagnosed ABI core timeout. The
first benchmark attempt retains three GCC compression build failures: the
upstream CompCert flag `-U__GNUC__` breaks modern glibc headers under GCC. The
runner now filters that flag only for GCC. All three pipelines for each of
those three workloads were rebuilt, revalidated, warmed up and remeasured in
a separate retry. The other 26 successful comparisons retain their original
samples and source/tool provenance; `previous_run` and per-pipeline artifact
paths identify them. No original attempt was overwritten.

| Run | Artifact directory under `.lake/prototype/` | Guard |
| --- | --- | --- |
| Original O2 | `o2-correctness-attempt-1` | `20260923T035704-aa9d0139` |
| Final O2 | `o2-correctness-attempt-2` | `20260923T041131-6c16520b` |
| Final O0 | `o0-regression-final` | `20260923T041718-974aae84` |
| Original benchmarks | `o2-benchmarks-attempt-1` | `20260923T041946-330acfc3` |
| Benchmark retry | `o2-benchmarks-final` | `20260923T042644-1072c05b` |
| Final verification | `o2-verification-vz3at0f7` | `20260923T042632-388d1621` |
| Allocator comparisons | `allocator-comparison-eytmrp1c` | `20260923T042642-c1cbb4b9` |
| Isolated core replay | native `coreDiagnostics` | `20260923T041109-4737c17b` |

Final verification passes the combined Lean build, allocator native tests,
switch/if-conversion/layout and validator tests, optimization aliases and
metadata tests, benchmark framework tests, legacy/malformed interchange,
compiler framework and smoke tests, codec generation check, and transitive
axiom audit. The only axiom dependencies are the existing approved
`propext`, `Classical.choice`, and `Quot.sound`. Every recorded guard enforces
one shared 26 GiB budget, zero swap, and complete descendant drain.

## Reproduction and archive

From the Lean repository, with the prerequisites in `PROTOTYPE.md` installed:

```sh
python3 scripts/guarded.py python3 tests/prototype/verify_o2.py
python3 scripts/guarded.py python3 tests/allocator/compare.py
python3 scripts/guarded.py python3 scripts/small_tests.py --optimization O0 --seed 20260922 --jobs 4
python3 scripts/guarded.py python3 scripts/small_tests.py --optimization O2 --seed 20260922 --jobs 4
python3 scripts/guarded.py python3 scripts/benchmarks.py --jobs 4 --cpu 0
python3 scripts/guarded.py lake build coreDiagnostics
python3 scripts/guarded.py .lake/build/bin/coreDiagnostics
```

The O2 correctness command intentionally still exits nonzero. Investigation
completion is separate from passing every test. The dossier gives the smaller
reproducer and exact core definition responsible.

`evidence.tar.gz` stores source snapshots, all complete correctness and
benchmark attempts, generated ABI fixtures, interchange, assembly, executables,
raw outputs/timings, diagnostics, check logs, and drained guard evidence.
`evidence.json` records its SHA-256 and every member's hash/size; repeated bytes
use tar hardlinks. The archive preserves original absolute paths in command
records; reproduce with the commands above in a fresh checkout. Extract with
`tar -xzf evidence.tar.gz -C <empty-directory>` to inspect `runs/`, `source/`,
`diagnostics/`, `verification/`, `reference/`, and `reports/`.
`preservation.json` records protected source and ledger hashes, the clean
upstream identity, and the unchanged corpus/historical baseline checks.
