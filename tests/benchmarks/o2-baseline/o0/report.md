# Small-test correctness report

Target: Linux System V x86-64, O0, iterated register coalescing allocator.

Run complete: True.

Counts: pass=139, fail=0, timeout=0, unavailable=0, excluded=9

Pipeline counts: {"lean": {"fail": 0, "pass": 139, "timeout": 0, "unavailable": 0}, "reference": {"fail": 0, "pass": 139, "timeout": 0, "unavailable": 0}}

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
| regression/struct7 | pass | pass | pass |
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
| regression/varargs1 | pass | pass | pass |
| regression/varargs2 | pass | pass | pass |
| regression/varargs3 | pass | pass | pass |
| regression/sections | pass | pass | pass |
| regression/aligned | pass | pass | pass |
| regression/switch3 | pass | pass | pass |
| regression/extern2 | pass | pass | pass |
| regression/NaNs | pass | pass | pass |
| regression/annot1 | pass | pass | pass |
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
| raytracer/render | pass | pass | pass |
| spass/small_problem | pass | pass | pass |
| abi/fixed-native | pass | pass | pass |
| abi/fixed-gcc_to_native | pass | pass | pass |
| abi/fixed-native_to_gcc | pass | pass | pass |
| abi/vararg-native | pass | pass | pass |
| abi/vararg-gcc_to_native | pass | pass | pass |
| abi/vararg-native_to_gcc | pass | pass | pass |
| abi/struct-native | pass | pass | pass |
| abi/layout | pass | pass | pass |
| abi/staticlayout | pass | pass | pass |
| pic/shared | pass | pass | pass |

## Failures and unavailable checks

## Justified exclusions

- regression/alias: O0 expectation depends on non-portable wild pointer arithmetic; deferred pending explicit optimization-sensitive test policy
- regression/builtins-aarch64: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/builtins-arm: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/builtins-powerpc: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/builtins-riscV: Other architecture; Linux System V x86-64 uses builtins-x86.c
- regression/funct1: Frontend-only negative test: wrong argument count; upstream FAILURES, no C-AST
- abi/struct-gcc_to_native: Upstream abi/Runtest excludes mixed struct ABI on x86-64
- abi/struct-native_to_gcc: Upstream abi/Runtest excludes mixed struct ABI on x86-64
- export: Rocq/Clight/Csyntax export validation is outside C-AST to x86-64

Commands, flags, timings, versions, hashes and artifact locations: `results.json`.
