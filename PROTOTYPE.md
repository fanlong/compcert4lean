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

In this meta-repository, use the existing shared **26 GiB** compute domain:

```bash
cd compcert4lean
python3 scripts/guarded.py --install-yojson
python3 scripts/guarded.py lake build
python3 scripts/guarded.py python3 scripts/smoke_test.py
```

The dependency setup is incremental. It installs only pinned yojson and its
dependencies, retaining opam's own package sandbox. Normal guarded commands
run under bubblewrap with a read-only host, writable Lean repository, masked
credentials, inaccessible systemd control sockets, and no network. The
supervisor uses the existing project lifecycle lock and memory service,
verifies kernel limits before admitting work, records telemetry/journals, and
waits for descendants to drain. No retired proof-ledger operation is invoked.
It requires the surrounding meta-repository's generic containment module,
user systemd manager, cgroup v2, and bubblewrap. Commands inside that admitted
domain can invoke the ordinary compiler commands below directly; otherwise
prefix them with `python3 scripts/guarded.py`. The wrapper starts in the Lean
repository. Direct scripts also work outside the repository with absolute
script/source/output paths in an appropriately contained Linux environment.

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

Accepted options include `-o`, `-S`, `-c`, `-r`, `-shared`, `-I`, `-D`, `-U`,
`-L`, `-l`, `-Wl,...`, `-O0`, `-fpic`/`-fno-pic`, `-fcommon`/`-fno-common`,
`--compcert-root`, and `--keep-temps`. CompCert language flags include `-fall`,
`-fnone`, and positive/negative forms of `-fstruct-passing`, `-flongdouble`,
`-fvararg-calls`, `-funprototyped`, `-fpacked-structs`,
`-funstructured-switch`, and `-finline-asm`. Both attached and separate values
work for the single-letter options. Other optimization levels are rejected.
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

The fixed profile is System V x86-64, optimization/inlining/debug disabled,
non-PIC/non-PIE, and `-fno-common` by default. PIC and common symbols are explicit
options; PIE remains unsupported. The same settings are used by the Lean
driver, bridge, reference compiler, and assembler/linker where applicable.
These O0 pass settings are independent of the optimized register allocator.

## Adapters and allocator

The OCaml bridge preprocesses and elaborates C to Csyntax with sequential
identifiers. It remains alive while Lean runs, keeping the original symbol
names, attributes, storage facts, and section/pragmas tables needed by the
assembly printer. Its actual `first_unused_ident` supplies Lean's sequential
fresh-identifier context. Composite definitions are serialized; Lean rebuilds
their environment with `Ctypes.build_composite_env` and carries the resulting
checked equality in the source program.

`compcert4lean-prototype-v2` JSON uses tagged arrays with exact arities and a
required `configuration` object containing boolean `pic`, `pie`, `common` and
`symbols`. Each symbol entry is `[identifier, {storage, definedHere, size}]`;
storage is `default`, `extern` or `static`, and size is null or a canonical
nonnegative signed-64-bit decimal string. These facts come directly from
CompCert's `C2C.decl_atom`, and populate the existing Lean relocation context.
The assembly result echoes the configuration; the live printer rejects a
mismatch with its original snapshot. Legacy v1 non-PIC source JSON remains
accepted, with its original default configuration and output version.
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

`allocationContext` is optional in both v1 and v2. Its only field is `reserved`,
an array of distinct canonical callee-save names: `RBX`, `RBP`, `R12`–`R15`.
Absence means no reservations. The frontend normalizes repeated pragmas; Lean
validates and echoes the context; the bridge compares it with its frontend
snapshot before checking builtin placement and expanding assembly.

See `CompCert4Lean/Allocator/README.md` for the upstream implementation checklist,
algorithm details, focused tests and documented limits. The old spill provider
and its exclusive helpers are removed; the original failure baseline is retained
under `tests/small-tests-baseline/`.

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
statements, and proofs remain unchanged. The proof ledgers are untouched.

Additional reproducible checks:

```bash
python3 scripts/guarded.py lake build
python3 scripts/guarded.py lake env lean tests/prototype/Trust.lean
python3 scripts/guarded.py lake build allocatorTests
python3 scripts/guarded.py .lake/build/bin/allocatorTests
python3 scripts/guarded.py python3 tests/allocator/test_interchange.py
python3 scripts/guarded.py python3 scripts/smoke_test.py
python3 scripts/guarded.py python3 tests/prototype/test_framework.py
python3 scripts/guarded.py python3 scripts/small_tests.py
python3 scripts/generate_codecs.py --check
```

See `tests/small-tests/SUITE.md` for selection, upstream checks, exclusions,
reproducibility and the initial correctness baseline. The suite reports compiler
failures without replacing Lean output with reference output.
Current allocator validation and pinned-compiler measurements are recorded in
`tests/allocator/ACCEPTANCE.md`.
