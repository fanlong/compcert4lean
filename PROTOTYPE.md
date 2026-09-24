# Linux compiler framework

`scripts/compile_c.py` compiles each C source file through the pinned CompCert
frontend, the existing Lean `Compiler.transf_c_program`, CompCert's assembly
expansion/printer, and GCC's assembler/linker. The result is an x86-64 Linux
ELF executable, shared library, assembly source, or relocatable object. It accepts
C and assembly sources, objects, archives and shared libraries in link order.
All compiler passes and
the Lean typing/allocation validators remain in the pipeline.

## Setup

Use Linux x86-64, Python 3.10 or newer, GCC/binutils, opam, and Lean **4.33.0**
(the checked-in `lean-toolchain`). The OCaml **4.14.2** switch must be named
`compcert-3.17` and contain `ocamlfind`, `zarith`, `menhirLib`, and
**yojson.2.2.2**. The prepared sibling `../CompCert` must be at
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`, with its native OCaml objects,
`.depend.extr`, `tools/modorder`, `ccomp`, `compcert.ini`, runtime headers, and
`runtime/libcompcert.a` already built for standard Linux x86-64. The prototype
reads this checkout without modifying or rebuilding it. `--compcert-root`
selects another prepared checkout of that exact revision.
The bridge links upstream CompCert components; their licensing terms remain
those in the pinned checkout's `LICENSE`. The vendored tests retain their
separate upstream GPL-2.0-or-later license.

Install the pinned JSON dependency and build from the repository root:

```bash
opam install --switch=compcert-3.17 yojson.2.2.2
lake build
python3 scripts/smoke_test.py
```

The dependency setup is incremental. Scripts also work outside the repository
with absolute script/source/output paths. Project-specific agent execution and
compute containment are maintained in the separate `compcert-lean-meta`
repository; its contributors should follow that repository's execution rules.

`compile_c.py` and `smoke_test.py` check versions and incrementally build the
native `leanCompiler` Lake target and OCaml bridge before compiling C. Initial
helper builds are excluded from compilation deadlines. Bridge build outputs,
helper logs, and version records live under `.lake/prototype/`; native Lean
outputs stay under `.lake/build/`. No Coq extraction or upstream build is run.

## Commands

```bash
python3 scripts/compile_c.py hello.c -o hello
python3 scripts/compile_c.py hello.c -S -o hello.s
python3 scripts/compile_c.py hello.c -c -o hello.o
python3 scripts/compile_c.py hello.c -Iinclude -DNAME=value -lm -o hello
python3 scripts/compile_c.py main.c helpers.c existing.o -Llib -lhelpers -o app
python3 scripts/compile_c.py library.c -fpic -shared -o libexample.so
python3 scripts/compile_c.py first.c second.c -c
python3 scripts/compile_c.py first.o second.o -r -o combined.o
python3 scripts/smoke_test.py
python3 scripts/small_tests.py --list
python3 scripts/small_tests.py --suite regression
```

For a build with per-file flags or output paths, use
`python3 scripts/compile_batch.py jobs.json --results .lake/batch-results`.
The results directory must be new. The manifest is a nonempty JSON array:

```json
[
  {"arguments": ["-O2", "-c", "first.c", "-o", "first.o"], "cwd": "."},
  {"arguments": ["-O2", "-DVALUE=7", "-c", "second.c", "-o", "second.o"], "cwd": "."}
]
```

Each batch checks versions and incrementally builds the toolchain once, then
uses that prepared toolchain for its serial jobs. All jobs must select the same
CompCert root. Keep compiler/toolchain sources stable during the batch. A new
invocation always prepares again. Per-job flags, compiler-stage deadlines, logs and optional
`--keep-temps` artifacts are preserved. Failed jobs are reported and subsequent
jobs still run; any failure makes the batch exit nonzero. `results.json` records
preparation, per-job and total wall times separately. Independent compilation
jobs can be batched together; link only after checking that required objects
compiled successfully. The imported SPEC runners batch each Lean profile.

Accepted options include `-o`, `-S`, `-c`, `-r`, `-shared`, `-I`, `-D`, `-U`,
`-L`, `-l`, `-Wl,...`, `-O0`, `-O`/`-O1`/`-O2`/`-O3`, `-fpic`/`-fno-pic`, `-fcommon`/`-fno-common`,
`--compcert-root`, and `--keep-temps`. CompCert language flags include `-fall`,
`-fnone`, and positive/negative forms of `-fstruct-passing`, `-flongdouble`,
`-fvararg-calls`, `-funprototyped`, `-fpacked-structs`,
`-funstructured-switch`, and `-finline-asm`. Both attached and separate values
work for the single-letter value options. The last optimization option wins;
`-O`, `-O1`, `-O2`, and `-O3` select the same normalized O2 profile. Other
optimization levels and individual optimization tuning flags are rejected.
`-std=c99`, `-std=c11`, and `-std=c18` select the C standard; the default
remains C99. The choice uses CompCert's `CommonOptions.set_std` API for both
preprocessing and frontend diagnostics, and is recorded in compilation
metadata. It does not alter the Csyntax interchange format.
Input and library order is preserved, including archive placement. Each C file
has its own live bridge and Lean invocation. Default outputs are `a.out`, `<stem>.s`,
and `<stem>.o`, respectively, in the caller's working directory. Paths are
passed as argv values and may contain spaces. Include/library paths are
interpreted relative to the caller. A failed compilation preserves any
previous output and retains its diagnostic directory; `--keep-temps` also
retains successful compilations. Multi-input `-c`/`-S` writes separate outputs;
an explicit `-o`, colliding output names or overwriting an input is rejected
before preparation or compilation. Outputs are published only after all
compilation/link stages succeed. Compilation and assembly/link stage limits
default to 300 seconds, configurable with `--compile-timeout` and `--link-timeout`.

The target is System V x86-64, non-PIC/non-PIE and `-fno-common` by default.
Compilation without an optimization option remains O0. O2 enables tail calls,
constant propagation, CSE, redundancy elimination, inlining, functions-called-once
inlining, normal if-conversion, and full floating-point constant propagation.
Size optimization, aggressive branchless conversion and debugging stay disabled.
PIC and common symbols are explicit options; PIE remains unsupported. Python,
the frontend/printer bridge, Lean and reference compilation use the same profile.
Both levels use the optimized allocator and upstream switch/layout policies.

## Adapters and allocator

The OCaml bridge preprocesses and elaborates C to Csyntax with sequential
identifiers. It remains alive while Lean runs, keeping the original symbol
names, attributes, storage facts, and section/pragmas tables needed by the
assembly printer. Its actual `first_unused_ident` supplies Lean's sequential
fresh-identifier context. Composite definitions are serialized; Lean rebuilds
their environment with `Ctypes.build_composite_env` and carries the resulting
checked equality in the source program.

`compcert4lean-prototype-v3` JSON uses tagged arrays with exact arities and a
required `configuration` object containing boolean `pic`, `pie`, `common`,
`optimization` (`O0` or `O2`), `functions`, and `symbols`. Each function entry is
`[identifier, {inline, static}]`, with inline status `inline`, `noinline` or
`none` and boolean static linkage taken directly from CompCert's frontend.
The function metadata must cover exactly the source function definitions.
Each symbol entry is `[identifier, {storage, definedHere, size}]`;
storage is `default`, `extern` or `static`, and size is null or a canonical
nonnegative signed-64-bit decimal string. These facts come directly from
CompCert's `C2C.decl_atom`, and populate the existing Lean relocation context.
The assembly result echoes the configuration; the live printer rejects a
mismatch with its original snapshot, including optimization and function facts.
Legacy v1 and v2 source JSON remain accepted as O0, with their original
configuration schemas and output versions. The target suffix must match the
normalized optimization profile.
Integers and identifiers are canonical decimal strings, including integers
beyond JavaScript's exact range. Fixed-width integers use unsigned bits;
float32/float64 use their 32/64-bit representations, preserving NaN payloads
and signed zero. Rocq/OCaml strings are byte arrays. Decoders reject malformed
tags, shapes, ranges, versions, and target profiles. Lean codecs have an
explicit nesting budget of 4096. `scripts/generate_codecs.py` regenerates the
reviewable, typed `Codecs.lean` and `bridge/codecs.ml` from an explicit allowlist
of the pinned extraction interfaces; it introduces no replacements for core
definitions. The OCaml bridge and these adapters are executable integration
code outside the compiler theorem boundary.

The selected allocator is **irc**, a deterministic Lean-native implementation
of the CompCert target pipeline. It builds compact XTL indices, tracks target
register classes and constraints, performs bounded worklist coloring and emits
validator-checked LTL. Stack-backed reloads remain explicit for values that
cannot be kept in a target register; diagnostic statistics are available to
allocator tests. Reserved callee-save registers flow from the frontend through
the optional `allocationContext` interchange field. The smoke suite deliberately
corrupts a proposal's stack size and requires validator rejection.

`allocationContext` is optional in all three versions. Its only field is `reserved`,
an array of distinct canonical callee-save names: `RBX`, `RBP`, `R12`–`R15`.
Absence means no reservations. The frontend normalizes repeated pragmas; Lean
validates and echoes the context; the bridge compares it with its frontend
snapshot before checking builtin placement and expanding assembly.

See `CompCert4Lean/Allocator/README.md` for the upstream implementation checklist,
algorithm details, focused tests and documented limits. The old spill provider
and its exclusive helpers are removed. Historical validation reports are retained
in `compcert-lean-meta` under `investigations/compiler-validation/`.

## Verification and evidence

The three unchanged smoke fixtures now live in `tests/small-tests/regression/`;
the complete imported corpus, license, manifest and provenance are under
`tests/small-tests/`. The smoke runner independently compiles and executes each through
Lean and pinned CompCert, requires zero exit status and byte-for-byte upstream
stdout, and retains separate artifacts. Default limits are **120 seconds per
compilation** and **10 seconds per execution**; change them with
`--compile-timeout` and `--run-timeout`. A failed suite returns nonzero.

Each `.lake/prototype/smoke-*` directory contains `summary.json`, commands,
stdout/stderr, exact tool versions/revisions and prototype hashes, preprocessed
C, Csyntax/Asm interchange, assembly, and executables. Integration checks cover
assembly/object modes (including linking and running both), paths with spaces,
invocation outside the repository, include/define/undefine/library options,
invalid C/JSON, malformed interchange, unsupported options, linker failure,
output preservation, float/identifier bit round trips, and corrupted proposals.

The native driver uses the existing pure top-level compiler; successful smoke
tests validate this prototype's exercised paths. They do not establish complete
C codec/provider coverage or prove the frontend, serialization, native runtime,
assembly expansion, or linker. Existing compiler definitions, theorem
statements, and proofs remain unchanged.

Additional reproducible checks:

```bash
lake build
lake env lean tests/prototype/Trust.lean
lake build allocatorTests
.lake/build/bin/allocatorTests
python3 tests/allocator/test_interchange.py
python3 scripts/smoke_test.py
python3 tests/prototype/test_framework.py
python3 scripts/small_tests.py
python3 scripts/generate_codecs.py --check
```

See `tests/small-tests/SUITE.md` for selection, upstream checks, exclusions,
reproducibility and the initial correctness baseline. The suite reports compiler
failures without replacing Lean output with reference output.
See `tests/README.md` for focused regression commands.

## Optimized correctness and benchmarks

`scripts/small_tests.py --optimization O2` runs the same 139 applicable cases
and retains the nine existing exclusions; its default remains O0. The seed is
20260922 and compilation, linking and execution deadlines default to 300 seconds.
`scripts/benchmarks.py` compiles all 29 workloads independently through Lean O2,
pinned CompCert O2 and GCC O2 before any measurement. It checks the actual
workload, warms up once, and records seven serial samples per compiler on one
CPU, rotating compiler order. GCC uses GNU C99, baseline x86-64, generic tuning,
and non-PIE linking. Compression roundtrips use a deterministic 1 MiB repetition
of the vendored LICENSE; SPASS uses `problem.dfg` for timing and retains
`small_problem.dfg` in correctness. Sources and expected output bytes are unchanged.

```bash
python3 tests/prototype/verify_o2.py
python3 scripts/small_tests.py --optimization O2 --jobs 4
python3 scripts/benchmarks.py --jobs 4
```

Allocation reports and malformed-allocation checks run the selected optimized
pipeline. `.lake/build/bin/leanCompiler --diagnose input.json output.json folder`
replays that same profile through the existing diagnostic companion, recording
pass completion times and RTL function sizes. It preserves failing pass errors.

For GCC, the CompCert compression flag `-U__GNUC__` is omitted: native GCC
must retain its compiler identity for glibc's type declarations. CompCert and
Lean retain the upstream flag. `benchmarks.py --retry-from RUN --artifacts NEW`
rebuilds and remeasures all three pipelines for each failed workload on the
original CPU, retaining successful workload samples and recording their original
run identity. The original attempt stays unchanged. `--report-only RUN
--observations FILE` attaches assembly-backed work-elimination observations
without changing timing samples.
