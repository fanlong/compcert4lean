# Nine-failure investigation — 2026-09-23

**Eight failures are in the non-ledger prototype allocator; the ninth is an
optimization-sensitive test expectation. None of these nine requires a change
to the ledger compiler core based on the evidence collected.**

All nine failures reproduced on Lean repository revision
`a8c5f2ed9a2b7587738cf84dba34f1a008538706`, with the baseline's O0 configuration,
ABI seed 20260922, and pinned CompCert 3.17. A separate diagnostic allocator,
injected through the existing compiler interface, made all eight Lean-only
failures pass. It used the existing compiler passes, allocation validator,
codecs, assembly bridge, test sources, and expected outputs. Production sources
and the original baseline were not changed.

## Per-case classification and estimate

Estimates are engineering time for a developer familiar with this prototype,
including targeted regression coverage. Shared fixes are counted once, not once
per failing case. Production integration and a full-suite rerun remain future work.

| Case | Root cause | Core or glue? | Estimated fix effort |
| --- | --- | --- | --- |
| `regression/struct7` | Small structure-copy source is assigned RCX, which the memcpy expander also uses as its transfer temporary; the pointer is overwritten. | Glue: prototype register allocator. | Low–medium: 0.5–1 day for the shared memcpy repair and edge-case tests. |
| `raytracer/render` | The same small-copy register collision occurs at 24 sites across four translation units, for 16- and 24-byte copies. | Glue: same allocator defect. | Same shared 0.5–1 day; no separate raytracer/core repair demonstrated. |
| `regression/varargs1` | One `__builtin_va_start` receives RAX instead of required RDX. | Glue: prototype register allocator. | Low: 2–4 hours for the shared varargs repair and tests. |
| `regression/varargs2` | Seven `__builtin_va_start` sites have the same RAX/RDX mismatch. | Glue: same allocator defect. | Same shared 2–4 hours. |
| `regression/varargs3` | One `__builtin_va_start` has the same RAX/RDX mismatch. | Glue: same allocator defect. | Same shared 2–4 hours. |
| `abi/vararg-native` | The generated definition unit contains 587 `__builtin_va_start` sites with the same mismatch. | Glue: same allocator defect. | Same shared 2–4 hours; generated caller/callee coverage passed with the diagnostic allocator. |
| `abi/vararg-gcc_to_native` | The Lean-compiled generated callee has the same 587 bad sites; GCC's caller is not the cause. | Glue: same allocator defect. | Same shared 2–4 hours; cross-compiler calling coverage also passed. |
| `regression/annot1` | An allocator guard rejects builtins with more than four distinct register operands. The file deliberately contains 30- and 20-argument annotations. | Glue: unsupported annotation allocation. | Low: 2–4 hours to retain annotation arguments in their spill slots and test them. |
| `regression/alias` | The fixed expected output encodes an optimized result for undefined pointer arithmetic; both compilers produce a different result at O0. | Test/harness policy, neither a compiler-core defect nor an allocator defect. | Low: 1–2 hours for explicit reporting/classification; no compiler repair warranted. |

## Why these are allocator/glue problems

`CompCert4Lean/Prototype/Services.lean:137` assigns every builtin's distinct
register operands using the same scratch-register sequence. Its integer
sequence starts AX, CX, DX, SI (`Services.lean:48`); it does not implement
the builtin-specific placement rules used by upstream
`CompCert/backend/Regalloc.ml:289` and
`CompCert/x86/Machregs.v:225`.

### Structure copies and the raytracer

Upstream requires AX/DX for register-addressed memcpy operands of at most
32 bytes and DI/SI for larger copies. Small-copy expansion uses RCX to transfer
data (`CompCert/x86/Asmexpand.ml:137`). In `struct7`, the retained assembly at
`.lake/prototype/small-tests-iqmql520/regression/struct7/lean/compile-000/output.s:316`
contains:

```asm
movq 104(%rsp), %rcx
movq 0(%rcx), %rcx
movq %rcx, 0(%rax)
movq 8(%rcx), %rcx
```

The second instruction destroys the source address. The fourth dereferences
copied structure data as a pointer. The corresponding pseudo-instruction is
`EF_memcpy 24 8` with destination RAX and source RCX. This is generated for
`AA[A1.x] = AA[A2.x]` in `struct7.c:67`.

The same bad pseudo-instruction pattern appears in raytracer `eval.c` (5 sites),
`object.c` (1), `light.c` (7), and `simplify.c` (11). Giving copies their required
operand registers eliminates both failures. The raytracer then produces a
byte-identical `kal.ppm`, so the evidence extends beyond merely avoiding SIGSEGV.

### Varargs

The retained Asm interchange in all five cases puts the va-list address in RAX.
`CompCert/x86/Asmexpand.ml:475` explicitly requires RDX. RAX is also the
expander's scratch register during va-list initialization, so deleting the
assertion would not fix the defect. The error message's “unsupported construct”
wording is a generic bridge wrapper around that assertion; it does not mean
that the compiler lacks the entire varargs feature.

Loading the operand into DX in the allocator makes all five cases compile and
match their existing output checks, including the generated native/native and
GCC-to-Lean ABI tests. Their generated fixture hashes match the original seed's
fixtures.

### Annotations

`Services.lean:151` rejects more than four distinct register parameters before
allocation. `annot1` deliberately exceeds that bound in `h` and `ll`, even
though those functions are not invoked by its `main`.

Annotations allow arbitrary locations (`X86/Machregs.lean:214`). The existing
stacking pass translates a local stack-slot operand into `BA_loadstack`
(`Backend/Stacking.lean:122`). The diagnostic allocator therefore maps annotation
operands directly to their existing spill slots and exempts these annotations
from the four-register limit. Compilation, validation, and the unchanged output
test pass; generated assembly retains all 30 and 20 annotation operands.
Simply raising the limit is insufficient: the existing scratch-register
function would reuse its fourth register for every later operand.

### Why allocation validation did not prevent the crashes

The core validator checks the RTL-to-LTL value correspondence. Its builtin
transfer checks post-instruction clobbers before adding the builtin's input
equations (`Backend/Allocation.lean:1797`), as upstream does
(`CompCert/backend/Allocation.v:1095`). These checks do not certify the concrete
OCaml assembly expander's operand-placement assumptions. The assembly bridge
and expansion are outside the proved compiler pipeline's executable boundary.
The appropriate repair is to satisfy and check that boundary in the glue.

## The `alias` expectation

`alias.c:134` explicitly identifies wild pointer arithmetic across distinct
objects. `delta8` subtracts a pointer to a local object from `&g`, and `get8`
manufactures a pointer back to that local object. This is not portable defined
C pointer arithmetic. Its output is sensitive to optimization.

The fresh selected-suite run confirms that Lean and pinned CompCert produce
identical output, differing from the fixture only at `Test 8`. A separate
pinned-CompCert experiment confirms:

| Configuration | Test 8 | Matches original fixture? |
| --- | --- | --- |
| O0 | 1 | No |
| O2 | 0 | Yes |

Keep the original fixture and recorded failure. The current suite manifest now
skips this case explicitly with an optimization-sensitive/nonportable reason.
If desired later, define a separate optimized test profile when that compiler
configuration is supported.
An O0 differential result can be reported separately without claiming this is
a portable C correctness test. Do not silently change the fixture or treat this
as a reason to change compiler semantics.

## Recommended next work

1. Repair the prototype allocator's builtin placement using the pinned x86
   rules. Cover small/large memcpy, register/stack addresses, identical source
   and destination operands, va_start, and other constrained builtin operands
   and results. Give annotations stack-slot operands. Estimated combined effort:
   **1–2 developer days**, allowing for shared implementation and integration.
2. Add glue-side validation of the assembly expander's register assumptions,
   so a future allocator omission produces a precise error before assembly or
   execution. Keep the existing core validator active.
3. Rerun the targeted cases, smoke/framework checks, combined build, and full
   140-case suite after the production repair. The investigation tested nine
   selected cases; it does not claim a new full-suite 139/140 result.
4. Handle `alias` through explicit test policy/reporting. No proof-ledger work
   is indicated by these nine failures. Follow the repository's definition
   exception policy if the eventual repair edits existing Lean definitions.

## Reproduction and evidence

The retained diagnostic directory is
`.lake/prototype/failure-investigation/`. It contains:

- `baseline/results.json`: all nine original failures reproduced.
- `diagnostic-verified/results.json`: eight pass, only `alias` fails on both
  pipelines; all nine cases completed without timeout/unavailable verdicts.
- `AllocatorProbe.lean`: separately named allocator, injected into the existing
  `Driver.Compiler.transf_c_program`; no core or production adapter override.
- `diagnose.py`: runs the existing test framework, substituting the probe only
  for the Lean compilation command in diagnostic mode.
- `alias-optimization/results.json` and `alias_probe.py`: O0/O2 confirmation.

From the Lean repository, use fresh artifact names:

```sh
python3 scripts/guarded.py python3 .lake/prototype/failure-investigation/diagnose.py baseline baseline-repeat
python3 scripts/guarded.py python3 .lake/prototype/failure-investigation/diagnose.py diagnostic diagnostic-repeat
python3 scripts/guarded.py python3 .lake/prototype/failure-investigation/alias_probe.py
```

The wrapper asserts the expected diagnostic verdicts; the underlying suite
returns 1 for both runs because at least one case fails. The final diagnostic
probe has no `sorry`, axioms, or changes to existing definitions. An earlier
probe elaboration attempt failed before compilation and is preserved as
`diagnostic/`; it is not the successful evidence.

Guard evidence under `.lake/prototype/guard/compute/`:

- `20260923T002102-fb2d9a24`: baseline reproduction.
- `20260923T002244-d2abfde9`: successful allocator experiment.
- `20260923T003058-9c3c82e7`: alias optimization experiment.

All three recorded the shared 26 GiB limit, zero workload swap, group OOM
semantics, and complete descendant drain. Raw experiments remain local build
artifacts; this document records the findings independently of their retention.
