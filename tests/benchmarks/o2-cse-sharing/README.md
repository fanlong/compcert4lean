# O2 results after the CSE predecessor-sharing repair

This follow-up fixes the `abi/layout` timeout diagnosed in the preserved
[O2 baseline](../o2-baseline/README.md). The production patch changes only
`CompCert4Lean/Backend/Kildall.lean`, in `BBlock_solver.basic_block_map`.

## Results — 2026-09-23

| Validation | Previous baseline | After repair |
| --- | ---: | ---: |
| O2 correctness, Lean | 138/139 | **139/139** |
| O2 correctness, pinned CompCert | 139/139 | **139/139** |
| O0 correctness, both compilers | 139/139 | **139/139** |
| O2 benchmark workloads, each of Lean/CompCert/GCC | 29/29 | **29/29** |
| `abi/layout` Lean compilation stage | Timeout at 300 s | **125.387 s** |
| Summed Lean benchmark compilation time | 234.355 s | **144.009 s** |
| Geometric mean executable time, Lean/CompCert | 1.003382 | **1.004218** |
| Geometric mean executable time, Lean/GCC | 1.212857 | **1.215081** |

Ratios above one mean Lean is slower. The new executable timings are about
0.42% slower than pinned CompCert and 21.51% slower than GCC on average, with
essentially the same performance profile as the baseline. This repair improves
compiler performance. The summed compilation time falls 38.6%; these are single
per-workload wall times with four concurrent build tasks, not elapsed suite
time or a repeated compilation benchmark. A separate focused run compiles
`abi/layout` in 118.556 s and also passes its output comparison.

The [complete benchmark tables](benchmarks.md) include all 29 workloads, code
sizes, compilation times, and sample variability. [results.json](results.json)
contains all 609 raw measured samples, validation and warmup records, commands,
compiler identities, output hashes, both correctness inventories, proof audits,
source hashes, and the compute guard receipt. Detailed local correctness and
verification logs are identified by their paths and hashes in that record.

Every pipeline is freshly rebuilt, validated, warmed up once, and measured
seven times. Measurements are serial on logical CPU 0 of the same AMD Ryzen 9
5900X, with compiler order rotated each round and all builds finished first.
The 28 eligible rows exclude only `c/integr`, whose GCC median remains below
10 ms. Inputs, compiler profiles, target flags, ABI seed `20260922`, nine
correctness exclusions, and 300-second stage deadlines are unchanged. The four
discarded-result crypto workloads have byte-identical executables to the
baseline in all three compilers, preserving the baseline's loop-retention
evidence.

| Native reproducer | Previous core scan | New core scan | Previous complete CSE | New complete CSE |
| --- | ---: | ---: | ---: | ---: |
| 1,000 RTL nodes | 0.181003 s | 0.000339 s | 0.396694 s | 0.004040 s |
| 2,000 RTL nodes | 0.854807 s | 0.000727 s | 1.841912 s | 0.008544 s |
| 4,000 RTL nodes | 4.025423 s | 0.001722 s | 7.576908 s | 0.019989 s |
| 40,000 RTL nodes | — | 0.019297 s | — | 0.278117 s |

The final combined `lake build`, native regression, allocator tests, runtime
helpers, optimization/framework/interchange tests, smoke tests, codec check,
and transitive axiom audits pass. The nine audited Kildall/CSE correctness
theorems use only the existing approved `propext`, `Classical.choice`, and
`Quot.sound`. Validation and benchmarks run under guard
`20260923T052914-ef0f193a`; evidence verification runs under
`20260923T054012-473b6c94`. Both enforce the shared 26 GiB budget with zero swap
and confirm complete descendant drain. The prior baseline, upstream corpus,
reference checkout, and proof ledger are unchanged.

## Repair and proof preservation

The old function rebuilt the entire predecessor map for each queried RTL node.
The repair computes it once and captures it in the basic-block classifier:

```lean
@[macro_inline] def basic_block_map {A : Type} (entrypoint : positive)
    (code : PTreeT A) (successors : A → List positive) : bbmap :=
  let preds := make_predecessors code successors
  is_basic_block_head entrypoint preds
```

`macro_inline` is necessary: Lean 4.33.0 otherwise eta-expands this
function-valued definition during native compilation, restoring the repeated
computation even with an explicit `let`. Expanding it at its use sites first
preserves sharing. The generated native solver builds the map once, captures
it in the `is_basic_block_head` closure, and reuses that closure for both the
initial block scan and propagation.

The generic `basic_block_map_preserves_classification` regression theorem
proves equality with the original definition by `rfl`, for every instruction
type, graph, successor function, and entry point. It has no axiom dependencies.
Existing production proofs and statements are byte-for-byte preserved. The
owner-authorized definition exception and proof review are recorded in the
parent repository's `agent-log.md`; no proof-ledger status changes are needed.

The native reproducer now includes 40,000 RTL nodes, exceeding the failing
fixture's 39,194-node function. The standard O2 verification runs it under a
30-second deadline, so restoring the quadratic behavior fails the regression.

## Reproduction

Run from the Lean repository with the prerequisites in `PROTOTYPE.md`:

```sh
python3 scripts/guarded.py python3 tests/prototype/verify_o2.py
python3 scripts/guarded.py python3 scripts/small_tests.py --optimization O2 --seed 20260922 --jobs 4
python3 scripts/guarded.py python3 scripts/small_tests.py --optimization O0 --seed 20260922 --jobs 4
python3 scripts/guarded.py python3 scripts/benchmarks.py --jobs 4 --cpu 0
```

For just the original failure:

```sh
python3 scripts/guarded.py python3 scripts/small_tests.py --optimization O2 --test abi/layout --seed 20260922
```
