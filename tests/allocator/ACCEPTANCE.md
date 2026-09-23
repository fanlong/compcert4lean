# Optimized allocator acceptance

Target: pinned CompCert 3.17, Linux System V x86-64, unchanged O0 compiler
passes. The prototype spill provider is replaced by the Lean `irc` provider.
Verified core definitions, the allocation validator, correctness theorem,
existing proofs and proof ledgers are unchanged. The original nine-failure
baseline and the documented `regression/alias` exclusion are preserved.

## Focused and integration checks

The final combined check on 2026-09-23 passed:

- `lake build`: 368 jobs; native allocator executable: 354 jobs.
- Adapter/allocator transitive axiom reports: only the existing approved
  `propext`, `Classical.choice`, `Quot.sound` dependencies; no new axioms or sorry.
- Codec regeneration check and unchanged three-program smoke suite, including
  corrupted-allocation rejection and the existing executable integration checks.
- Native allocator tests: **0.50 seconds**, excluding compilation. Every
  positive RTL fixture passes the existing validator.
- Both allocator interchange tests, including 19 builtin placement cases,
  reservation normalization, malformed contexts and frontend snapshot rejection.
- All seven existing framework tests, including PIC/common symbols, multiple
  files, legacy inputs, failure preservation and reporting.

Guard evidence: `.lake/prototype/guard/compute/20260923T030733-c6089277/`.
Native test output and axiom reports are in `stdout.log`; timing and framework
results are in `stderr.log`. Interchange artifacts:
`.lake/prototype/allocator-interchange-2twcj0vd/`; smoke:
`.lake/prototype/smoke-20260923T030743Z-_whrllqx/`; framework:
`.lake/prototype/framework-8bg0ndk6/`.

All eight allocator-related baseline failures passed focused regression runs:
struct7, raytracer, varargs1/2/3, both formerly failing varargs ABI cases and
annot1. Their imported sources and expected results were not changed.

## Full applicable suite

The final full run passed **139/139** cases in both Lean and pinned CompCert:
zero failures, timeouts or unavailable verdicts. It used seed `20260922`, one
concurrent case and the unchanged 300-second compilation, link and execution
deadlines. All nine documented exclusion entries remain, including `alias`.

Command: `python3 scripts/guarded.py python3 scripts/small_tests.py --seed 20260922 --jobs 1`.
Report and per-stage evidence: `.lake/prototype/small-tests-jwk0na09/`.
Guard evidence: `.lake/prototype/guard/compute/20260923T030815-87dd50de/`.
The recorded provenance includes every new allocator Lean module. All recorded
production source fingerprints still match the tested files. Both final
compute invocations record complete descendant drain.

## Lightweight comparison

Single warm compilation to assembly, including frontend/bridge execution and
excluding builds. Values are Lean / pinned CompCert. Spill/reload counts are
actual Local LTL stores/loads; moves are remaining LTL `Omove` instructions.
Stack usage is the largest local slot extent in four-byte words, excluding
source-language objects, outgoing arguments, saves and frame alignment.

| Fixture | Compile ms | Spills / reloads | Moves | Stack words |
| --- | ---: | ---: | ---: | ---: |
| Copy chain | 46.3 / 11.2 | 0/0 / 0/0 | 1 / 1 | 0 / 0 |
| Live across call | 38.2 / 11.4 | 0/0 / 0/0 | 3 / 3 | 0 / 0 |
| 24 integer values | 170.7 / 16.3 | 9/9 / 9/9 | 2 / 1 | 9 / 9 |
| 24 float values | 140.6 / 15.3 | 8/8 / 8/8 | 4 / 1 | 16 / 16 |

The pressure fixtures record 11 and 9 reload reuses respectively. Native tests
also verify reuse across extended basic blocks and its progressive reduction,
and verify that two consecutive pressure phases reuse the same stack extent.
These small measurements do not establish broad performance parity; Lean is
slower and retains additional moves on the pressure examples.

Reproduce with `python3 scripts/guarded.py python3 tests/allocator/compare.py`.
Sources, compiler commands, assemblies, CompCert LTL dumps, validator-checked
Lean allocation reports and exact times are retained in
`.lake/prototype/allocator-comparison-2d_ttcdh/`.

All executable checks use the shared 26 GiB guarded compute domain, zero swap
and group OOM termination. Guard evidence records source hashes, admission,
resource observations and descendant drain.
