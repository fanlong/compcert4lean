# CompCert4Lean

CompCert4Lean is a Lean 4 port of the selected compiler core and proof
development of [CompCert](https://compcert.org/) 3.17. It includes intermediate
languages, operational semantics, compiler passes, and correctness proofs for
the path from typed CompCert C to x86-64 assembly. The project aims to check
that path's semantic-preservation proofs in Lean's kernel; proof completion is
still in progress.

The repository also provides a working C compiler driver for **Linux x86-64
(System V ABI)**. It combines CompCert's existing frontend and assembly printer
with the Lean compiler core and a Lean-native register allocator:

```text
C source
  → CompCert frontend → typed Csyntax
  → Lean compiler passes and allocation validator → assembly AST
  → CompCert assembly expansion/printer → assembly text
  → GCC assembler/linker → executable
```

The executable pipeline supports assembly, object, executable, and shared-library
output. Passing compiler tests demonstrates behavior on the exercised programs;
it does not establish a completed end-to-end verification of the driver,
frontend, serialization, native runtime, or linker. See
[PROTOTYPE.md](PROTOTYPE.md) for the implementation and trust boundary.

## Quick start: compile one C file

With the [prerequisites](#prerequisites-and-build) installed, run these commands
from the `compcert4lean` repository root to compile an existing `hello.c` and
execute it:

```bash
python3 scripts/compile_c.py hello.c -o hello
./hello
```

Replace `hello.c` with your source file and `hello` with the desired executable
name. To emit assembly or an object file instead:

```bash
python3 scripts/compile_c.py hello.c -S -o hello.s
python3 scripts/compile_c.py hello.c -c -o hello.o
```

For a complete example including the C source, see
[Compile and run one C file](#compile-and-run-one-c-file).

## Prerequisites and build

Commands below run from the `compcert4lean` repository root using Bash.

To build the Lean library and native compiler, install Lean/Lake through
[elan](https://github.com/leanprover/elan) and use the checked-in
[lean-toolchain](lean-toolchain), which pins **Lean 4.33.0**:

```bash
lake build
```

The default targets are `CompCert4Lean` and `leanCompiler`; the native compiler
is written to `.lake/build/bin/leanCompiler`. For the C command-line interface,
use `scripts/compile_c.py`, which handles the frontend and other external tools.

Compiling C and running the integration suites additionally require:

- Linux x86-64, Python **3.10+**, GCC/binutils, Git, and opam.
- An opam switch named **`compcert-3.17`**, using **OCaml 4.14.2**, with
  `ocamlfind`, `zarith`, `menhirLib`, and **`yojson.2.2.2`** installed.
- A prepared CompCert checkout at `../CompCert`, pinned to
  **`7b1f02b09954b9b916eb2a91d283c9b5355bf172`**. It must already be built for
  Linux x86-64, including `ccomp`, the native OCaml objects, `.depend.extr`,
  `tools/modorder`, `compcert.ini`, runtime headers, and `runtime/libcompcert.a`.

With that switch and upstream build prepared, install the JSON dependency if
needed:

```bash
opam install --switch=compcert-3.17 yojson.2.2.2
```

The driver checks tool versions and incrementally builds the Lean executable
and OCaml bridge. It reads the prepared CompCert checkout without rebuilding
it. Use `--compcert-root /path/to/CompCert` to select another checkout at the
same revision. See [the setup details](PROTOTYPE.md#setup) before a first run.

## Compile and run one C file

Create a small program, compile it, and run the resulting executable:

```bash
mkdir -p .lake/examples
cat > .lake/examples/hello.c <<'EOF'
#include <stdio.h>

int main(void) {
    puts("Hello from CompCert4Lean!");
    return 0;
}
EOF
python3 scripts/compile_c.py .lake/examples/hello.c -o .lake/examples/hello
.lake/examples/hello
```

To compile your own file, substitute its path for `.lake/examples/hello.c`.
Common alternatives are:

```bash
python3 scripts/compile_c.py hello.c -O2 -o hello
python3 scripts/compile_c.py hello.c -S -o hello.s
python3 scripts/compile_c.py hello.c -c -o hello.o
python3 scripts/compile_c.py hello.c -std=c11 -Iinclude -DVALUE=7 -lm -o hello
python3 scripts/compile_c.py --help
```

The defaults are **C99**, **O0**, non-PIC/non-PIE, and `-fno-common`.
`-O`, `-O1`, `-O2`, and `-O3` all select the same O2 profile. C11 and C18 are
also supported. Add `--keep-temps` to retain successful compilation artifacts;
failed compilations retain diagnostics and preserve any previous output file.

For multiple inputs, batch manifests, shared libraries, supported flags, and
timeouts, see [compiler commands](PROTOTYPE.md#commands).

## Run tests

Start with the smoke suite after preparing the toolchain:

```bash
python3 scripts/smoke_test.py
```

It compiles and runs three upstream programs independently through Lean and
CompCert, compares their output with the upstream expected bytes, and exercises
driver error handling, output modes, serialization, and allocation validation.
A failed check makes the command exit nonzero.

List or select cases from the imported correctness suite:

```bash
python3 scripts/small_tests.py --list
python3 scripts/small_tests.py --suite regression
python3 scripts/small_tests.py --test 'regression/volatile*'
```

Run the full applicable corpus under each optimization profile:

```bash
python3 scripts/small_tests.py --optimization O0
python3 scripts/small_tests.py --optimization O2
```

For focused allocator checks and the broader runtime/trust checks:

```bash
lake build allocatorTests
.lake/build/bin/allocatorTests
python3 tests/allocator/test_interchange.py
python3 tests/prototype/verify_o2.py
```

Runners print their artifact directories under `.lake/prototype/`, containing
results, commands, diagnostics, and generated outputs. The full corpus takes
longer than the smoke suite; its selection rules, exclusions, and deadlines
are documented in [SUITE.md](tests/small-tests/SUITE.md). See
[tests/README.md](tests/README.md) for the complete test command index.

## Source map

| Path | Contents |
| --- | --- |
| [CompCert4Lean.lean](CompCert4Lean.lean) | Top-level library imports |
| [CompCert4Lean/Driver/](CompCert4Lean/Driver/) | Compiler pass composition and correctness statements/proofs |
| [CompCert4Lean/Cfrontend/](CompCert4Lean/Cfrontend/), [Backend/](CompCert4Lean/Backend/) | Source/intermediate languages, semantics, transformations, and proofs |
| [CompCert4Lean/X86/](CompCert4Lean/X86/), [X86_64/](CompCert4Lean/X86_64/) | Target-specific definitions and proofs |
| [CompCert4Lean/Foundation/](CompCert4Lean/Foundation/), [Lib/](CompCert4Lean/Lib/), [Common/](CompCert4Lean/Common/), [Flocq/](CompCert4Lean/Flocq/) | Shared infrastructure, arithmetic, and floating-point development |
| [CompCert4Lean/Allocator/](CompCert4Lean/Allocator/) | Lean-native register allocation |
| [CompCert4Lean/Prototype/](CompCert4Lean/Prototype/), [bridge/](bridge/) | Native Lean entry point, interchange codecs, and OCaml integration |
| [scripts/](scripts/), [tests/](tests/) | Compiler drivers, reusable test runners, fixtures, and trust checks |

## Contributors and coding agents

Start with the source map and the documentation for the component you intend
to change. [tests/README.md](tests/README.md) lists focused checks, while
[PROTOTYPE.md](PROTOTYPE.md) explains how executable integration connects to
the formal compiler. Build and test artifacts belong under `.lake/`.

## Further reading

| Document | Use it for |
| --- | --- |
| [PROTOTYPE.md](PROTOTYPE.md) | Toolchain setup, compiler options, adapters, trust boundary, and benchmarks |
| [tests/README.md](tests/README.md) | Focused and full regression commands |
| [tests/smoke/README.md](tests/smoke/README.md) | Smoke fixtures, provenance, and expected output |
| [tests/small-tests/SUITE.md](tests/small-tests/SUITE.md) | Correctness corpus, selection, exclusions, and reporting |
| [CompCert4Lean/Allocator/README.md](CompCert4Lean/Allocator/README.md) | Allocation algorithm, validation, target limits, and focused tests |
| [tests/optimization/README.md](tests/optimization/README.md) | Runtime optimization proofs, trust audits, and recorded performance |

The OCaml bridge links upstream CompCert components, whose licensing terms
remain those of the pinned CompCert checkout. The imported small-test corpus
retains its own [license](tests/small-tests/LICENSE) and
[upstream README](tests/small-tests/README.md).
