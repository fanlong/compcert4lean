# Small-test correctness report

Target: Linux System V x86-64, O0, spill allocator.

Run complete: True.

Counts: pass=131, fail=9, timeout=0, unavailable=0, excluded=8

Pipeline counts: {"lean": {"fail": 9, "pass": 131, "timeout": 0, "unavailable": 0}, "reference": {"fail": 1, "pass": 139, "timeout": 0, "unavailable": 0}}

Compiler failures remain failures. Reference/harness failures make a check unavailable.

| Case | Verdict | Lean | CompCert |
| --- | --- | --- | --- |
| regression/int32 | pass | pass | pass |
| regression/int64 | pass | pass | pass |
| regression/floats | pass | pass | pass |
| regression/floats-basics | pass | pass | pass |
| regression/floats-lit | pass | pass | pass |
| regression/expr1 | pass | pass | pass |
| regression/expr6 | pass | pass | pass |
| regression/funptr2 | pass | pass | pass |
| regression/initializers | pass | pass | pass |
| regression/initializers2 | pass | pass | pass |
| regression/initializers3 | pass | pass | pass |
| regression/volatile1 | pass | pass | pass |
| regression/volatile2 | pass | pass | pass |
| regression/volatile3 | pass | pass | pass |
| regression/volatile4 | pass | pass | pass |
| regression/funct3 | pass | pass | pass |
| regression/expr5 | pass | pass | pass |
| regression/struct7 | fail | fail | pass |
| regression/struct8 | pass | pass | pass |
| regression/struct11 | pass | pass | pass |
| regression/struct12 | pass | pass | pass |
| regression/casts1 | pass | pass | pass |
| regression/casts2 | pass | pass | pass |
| regression/char1 | pass | pass | pass |
| regression/sizeof1 | pass | pass | pass |
| regression/sizeof2 | pass | pass | pass |
| regression/binops | pass | pass | pass |
| regression/bool | pass | pass | pass |
| regression/for1 | pass | pass | pass |
| regression/for2 | pass | pass | pass |
| regression/switch | pass | pass | pass |
| regression/switch2 | pass | pass | pass |
| regression/compound | pass | pass | pass |
| regression/decl1 | pass | pass | pass |
| regression/bitfields9 | pass | pass | pass |
| regression/ptrs3 | pass | pass | pass |
| regression/telescopes | pass | pass | pass |
| regression/parsing | pass | pass | pass |
| regression/krfun | pass | pass | pass |
| regression/ifconv | pass | pass | pass |
| regression/generic | pass | pass | pass |
| regression/dollars | pass | pass | pass |
| regression/consteval | pass | pass | pass |
| regression/attribs1 | pass | pass | pass |
| regression/bitfields1 | pass | pass | pass |
| regression/bitfields2 | pass | pass | pass |
| regression/bitfields3 | pass | pass | pass |
| regression/bitfields4 | pass | pass | pass |
| regression/bitfields5 | pass | pass | pass |
| regression/bitfields6 | pass | pass | pass |
| regression/bitfields7 | pass | pass | pass |
| regression/bitfields8 | pass | pass | pass |
| regression/bitfields_uint_t | pass | pass | pass |
| regression/bitfields10 | pass | pass | pass |
| regression/builtins-common | pass | pass | pass |
| regression/builtins-x86 | pass | pass | pass |
| regression/packedstruct1 | pass | pass | pass |
| regression/packedstruct2 | pass | pass | pass |
| regression/alignas | pass | pass | pass |
| regression/varargs1 | fail | fail | pass |
| regression/varargs2 | fail | fail | pass |
| regression/varargs3 | fail | fail | pass |
| regression/sections | pass | pass | pass |
| regression/alias | fail | fail | fail |
| regression/aligned | pass | pass | pass |
| regression/switch3 | pass | pass | pass |
| regression/extern2 | pass | pass | pass |
| regression/NaNs | pass | pass | pass |
| regression/annot1 | fail | fail | pass |
| regression/commaprec | pass | pass | pass |
| regression/expr2 | pass | pass | pass |
| regression/expr3 | pass | pass | pass |
| regression/expr4 | pass | pass | pass |
| regression/extern1 | pass | pass | pass |
| regression/funct2 | pass | pass | pass |
| regression/funptr1 | pass | pass | pass |
| regression/pragmas | pass | pass | pass |
| regression/ptrs1 | pass | pass | pass |
| regression/ptrs2 | pass | pass | pass |
| regression/struct1 | pass | pass | pass |
| regression/struct2 | pass | pass | pass |
| regression/struct3 | pass | pass | pass |
| regression/struct4 | pass | pass | pass |
| regression/struct5 | pass | pass | pass |
| regression/struct6 | pass | pass | pass |
| regression/struct9 | pass | pass | pass |
| regression/struct10 | pass | pass | pass |
| regression/types1 | pass | pass | pass |
| regression/seqops | pass | pass | pass |
| regression/singlefloats | pass | pass | pass |
| regression/emptydecl | pass | pass | pass |
| regression/extasm | pass | pass | pass |
| supplemental/casts3 | pass | pass | pass |
| supplemental/charlit | pass | pass | pass |
| supplemental/compar | pass | pass | pass |
| supplemental/init1 | pass | pass | pass |
| supplemental/init2 | pass | pass | pass |
| supplemental/init3 | pass | pass | pass |
| supplemental/init4 | pass | pass | pass |
| supplemental/instrsel | pass | pass | pass |
| supplemental/stringlit | pass | pass | pass |
| c/fib | pass | pass | pass |
| c/integr | pass | pass | pass |
| c/qsort | pass | pass | pass |
| c/fft | pass | pass | pass |
| c/fftsp | pass | pass | pass |
| c/fftw | pass | pass | pass |
| c/sha1 | pass | pass | pass |
| c/sha3 | pass | pass | pass |
| c/aes | pass | pass | pass |
| c/almabench | pass | pass | pass |
| c/lists | pass | pass | pass |
| c/binarytrees | pass | pass | pass |
| c/fannkuch | pass | pass | pass |
| c/knucleotide | pass | pass | pass |
| c/mandelbrot | pass | pass | pass |
| c/nbody | pass | pass | pass |
| c/nsieve | pass | pass | pass |
| c/nsievebits | pass | pass | pass |
| c/spectral | pass | pass | pass |
| c/vmach | pass | pass | pass |
| c/bisect | pass | pass | pass |
| c/chomp | pass | pass | pass |
| c/perlin | pass | pass | pass |
| c/siphash24 | pass | pass | pass |
| compression/arcode | pass | pass | pass |
| compression/lzw | pass | pass | pass |
| compression/lzss | pass | pass | pass |
| raytracer/render | fail | fail | pass |
| spass/small_problem | pass | pass | pass |
| abi/fixed-native | pass | pass | pass |
| abi/fixed-gcc_to_native | pass | pass | pass |
| abi/fixed-native_to_gcc | pass | pass | pass |
| abi/vararg-native | fail | fail | pass |
| abi/vararg-gcc_to_native | fail | fail | pass |
| abi/vararg-native_to_gcc | pass | pass | pass |
| abi/struct-native | pass | pass | pass |
| abi/layout | pass | pass | pass |
| abi/staticlayout | pass | pass | pass |
| pic/shared | pass | pass | pass |

## Failures and unavailable checks

### regression/struct7 / lean

Category: execution_failure

```text
/home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/regression/struct7/lean/regression/program exited -11: 
```

### regression/varargs1 / lean

Category: assembly_failure

```text
CompCert bridge failed: CompCert bridge: unsupported construct for assembly expansion/printing (x86/Asmexpand.ml:475); retain asm.json

Artifacts: /home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/regression/varargs1/lean/compile-000
```

### regression/varargs2 / lean

Category: assembly_failure

```text
CompCert bridge failed: CompCert bridge: unsupported construct for assembly expansion/printing (x86/Asmexpand.ml:475); retain asm.json

Artifacts: /home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/regression/varargs2/lean/compile-000
```

### regression/varargs3 / lean

Category: assembly_failure

```text
CompCert bridge failed: CompCert bridge: unsupported construct for assembly expansion/printing (x86/Asmexpand.ml:475); retain asm.json

Artifacts: /home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/regression/varargs3/lean/compile-000
```

### regression/alias / lean

Category: incorrect_output

```text
stdout: bytes differ
```

### regression/alias / reference

Category: incorrect_output

```text
stdout: bytes differ
```

### regression/annot1 / lean

Category: lean_rejection

```text
/home/fanl/compcert-lean-meta/compcert4lean/.lake/build/bin/leanCompiler exited 1: Lean compiler: In function  context:71 :  spill allocator: unsupported builtin register requirements

Artifacts: /home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/regression/annot1/lean/compile-000
```

### raytracer/render / lean

Category: execution_failure

```text
/home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/raytracer/render/lean/raytracer/program exited -11: 
```

### abi/vararg-native / lean

Category: assembly_failure

```text
CompCert bridge failed: CompCert bridge: unsupported construct for assembly expansion/printing (x86/Asmexpand.ml:475); retain asm.json

Artifacts: /home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/abi/vararg-native/lean/compile-000
```

### abi/vararg-gcc_to_native / lean

Category: assembly_failure

```text
CompCert bridge failed: CompCert bridge: unsupported construct for assembly expansion/printing (x86/Asmexpand.ml:475); retain asm.json

Artifacts: /home/fanl/compcert-lean-meta/compcert4lean/.lake/prototype/small-tests-iqmql520/abi/vararg-gcc_to_native/lean/compile-000
```

## Justified exclusions

- regression/builtins-aarch64: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/builtins-arm: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/builtins-powerpc: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/builtins-riscV: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/funct1: Frontend-only negative test: wrong argument count; upstream FAILURES, no C-AST
- abi/struct-gcc_to_native: Upstream abi/Runtest excludes mixed struct ABI on x86-64
- abi/struct-native_to_gcc: Upstream abi/Runtest excludes mixed struct ABI on x86-64
- export: Rocq/Clight/Csyntax export validation is outside C-AST to x86-64

Commands, flags, timings, versions, hashes and artifact locations: `results.json`.
