# Imported correctness suite

The 438 upstream files retain their bytes and paths from
`https://github.com/AbsInt/CompCert-small-tests`, revision
`081175df374260304a5cd78dd3dfaded93dceb41`. `provenance.json` records every
upstream path and SHA-256. `README.md`, `LICENSE`, per-file notices, Makefiles,
scripts, headers, data, generators, and expected outputs are unchanged.
`scripts/import_small_tests.py CHECKOUT` reproduces the import and manifest
from a checkout of that revision using committed Git blobs.

`manifest.json` specifies 139 applicable cases and nine exclusion entries.
Every upstream C file is a case input or explicitly excluded. Exclusions cover
four other-architecture builtin files, `funct1` (a frontend-only negative
argument-count test), the Rocq export group, the two mixed struct ABI modes
that upstream `abi/Runtest` excludes on x86-64, and `regression/alias`, whose
O0 expectation depends on non-portable wild pointer arithmetic. Upstream
condition scripts are preserved: the compiled `funptr2` runs here, and
`packedstruct1` only excludes ARM. Supplemental regressions include omitted
runnable sources with supplied expected results and standalone initializer
fragments compiled to assembly.
`stringlit` and `charlit` retain their upstream “temporarily removed” annotation;
their actual outcomes are reported, with no automatic success allowance.

## Run

From `compcert4lean`, use the existing shared 26 GiB compute wrapper:

```sh
python3 scripts/small_tests.py --list
python3 scripts/guarded.py python3 scripts/small_tests.py
python3 scripts/guarded.py python3 scripts/small_tests.py --suite abi --suite pic
python3 scripts/guarded.py python3 scripts/small_tests.py --test 'regression/volatile*'
```

The target is Linux System V x86-64, O0, with the iterated register coalescing allocator and all
existing Lean compiler validators. Defaults are one case at a time and 300
seconds per source compilation, assembly/link, and execution. Use `--jobs`
(1–32), `--compile-timeout`, `--link-timeout`, and `--run-timeout` to override.
Concurrent cases share the one compute domain; there are no per-case memory
caps. `--artifacts` selects a fresh output directory. `--compcert-root` selects
the prepared CompCert 3.17 checkout at the compiler pin documented in
`PROTOTYPE.md`. The executable and bridge are prepared once per suite.

The existing `scripts/smoke_test.py` command retains its three programs,
integration checks, 120-second compile limit and 10-second run limit.

## Checks

| Group | Oracle |
| --- | --- |
| regression | Upstream stdout, assembly-only extras, or successful exit where upstream has no expected file. `NaNs` compares against the pinned CompCert interpreter. |
| supplemental | Existing upstream stdout or assembly-only standalone fragments. |
| c | Upstream stdout, with `Results/knucleotide-input.txt` and other relative data copied into the working directory. |
| compression | Compress then decompress the exact upstream `LICENSE` bytes; compare the recovered bytes and record the input hash. This fixes upstream's host-dependent choice of dictionary or executable. |
| raytracer | Feed `kal.gml` on stdin and compare generated `kal.ppm` with upstream `Results/kal.ppm`. |
| spass | Run `small_problem.dfg`; require exit zero and `Proof found` in stdout. |
| abi | Generate once with seed 20260922, upstream 500 random functions for fixed/vararg, upstream struct enumeration, and 1000 four-field layouts. Share identical files between Lean, CompCert and GCC; require upstream exit success or exact GCC layout stdout. |
| pic | Build both shared dependencies and `dylib.so`; run the executable with its local library search path and compare `main.reference`. The program exercises `dlopen` and `dlsym`. |

ABI `gcc_to_native` means a GCC caller and Lean/CompCert callee;
`native_to_gcc` reverses them. GCC compilation also uses O0. `--seed` overrides
the recorded ABI seed. No expected output is generated from Lean execution.
Each pipeline runs in a private copy of its group's inputs; the imported corpus
is hash-checked and never used as a generation or execution directory.

## Results

Every selected case runs independently through Lean and pinned CompCert.
`results.json` and `report.md` retain each pipeline's verdict, flags, commands,
timings, versions, source/fixture hashes, stdout/stderr paths and artifacts.
Compilation, assembly, linking, execution and comparison records are distinct.
The Lean compiler's records further distinguish frontend, Lean and assembly
printer rejection. Failures retain the interchange, assembly and diagnostics.

Test verdicts are pass, fail, timeout or unavailable; justified exclusions are
listed separately. Frontend/Lean rejection, assembly/link errors, failed
execution and wrong output remain failures. Missing reference/harness results
are unavailable, and never provide a fallback implementation. Any selected
applicable failure, timeout or unavailable result returns nonzero. A failure
baseline is expected to guide subsequent compiler repair, which is outside
this framework task.

The initial complete run and reproducible failure evidence are retained under
`../small-tests-baseline/` after verification; full working artifacts remain
at the recorded `.lake/prototype/small-tests-*` location.
`scripts/record_small_tests_baseline.py RUN DESTINATION` records a completed run
with its readable/JSON reports, a deterministic compressed archive of all
command logs and ABI fixtures, failure interchange/assembly, and a SHA-256
inventory. Optional repeated `--verification` directories include guarded build,
smoke, framework and containment evidence. The archive stores paths relative to
the run, so the evidence remains readable after moving or cleaning `.lake/`.
