# Register allocation

`regalloc configuration allocationContext` is the sole production allocation
oracle. The existing `Backend.Allocation` validator checks its proposals, and
the compiler uses its existing correctness theorem without modification. The
implementation is total Lean, compiled natively; errors cover exhausted bounds,
uncolorable temporaries and invalid intermediate operands. No native interface,
allocator selection switch or fallback is installed.

The implementation follows pinned CompCert 3.17
(`7b1f02b09954b9b916eb2a91d283c9b5355bf172`) for Linux System V x86-64.

| Upstream surface | Implementation |
| --- | --- |
| `Splitting.ml`, backward range inference and unification | `SplitRanges.lean`: compact indices, backward worklist, bounded union-find, entry parameters |
| `Regalloc.ml`, RTL to XTL and recursive builtin constraints | `XTL.lean`: original node correspondence, fixed locations, ABI parallel moves, two-address overlap temporaries |
| `Machregs.v`, `Conventions1.v` | `TargetConstraints.lean`: exact applicable fixed constraints, two-address rules and preferred/remaining pools; existing Lean ABI and clobber definitions are reused |
| `Regalloc.ml`, liveness and DCE | `Analyses.lean`: backward worklist, pure dead computations, dead moves and debug operands |
| `Regalloc.ml`, interference and spill costs | `Analyses.lean`: fixed and stack conflicts, classes, instruction clobbers, calls, inline assembly, parallel temporaries, costs 1/10 and unspillable temporaries |
| `IRC.ml`, iterated coalescing | `Coloring.lean`: simplify/coalesce/freeze/spill worklists, full Briggs, George including finite-cost small-use heuristic, cost/degree² priority |
| `IRC.ml`, location assignment | `Coloring.lean`: deterministic preferred-register rotation, ordered remaining registers, preferred stack-slot coalescing, lowest aligned nonoverlapping slot |
| `Regalloc.ml`, repeated spilling | `Spilling.lean`, `Allocator.lean`: original XTL rebuilt with accumulated spill decisions; at most 40 rounds; EBB reload equations, three-equation limit and age 3/1/0 schedule |
| `Regalloc.ml`, LTL emission | `LTL.lean`: redundant move removal, parallel cycles, stack-to-stack temporaries and enforced two-address placement |
| `CPragmas.ml`, reservation plumbing | `Prototype/Main.lean`, `bridge/bridge.ml`: validated optional context, normalized frontend reservations, echo and snapshot comparison |
| `Asmexpand.ml`, builtin compatibility | `bridge/bridge.ml`: recursive pinned fixed-register constraints and supported forms checked immediately before expansion, with function/instruction diagnostics |

Implementation choices differ from the mutable OCaml representation: arrays
use dense indices and ordered adjacency sets; worklists use deterministic index
order; spill priorities use exact integer cross-products. Changed neighborhoods
re-enable pending moves conservatively. Stack-slot reuse preserves the consuming
value's type, size and alignment. Parallel cycles normally use register
temporaries; if a stack-to-stack transfer needs an occupied cycle temporary,
its saved value moves to a fresh local slot first. These choices do not require
identical register assignments or assembly to upstream.

The profile does not implement 32-bit split-long calling conventions, Windows
register pools or non-x86 targets. Unspillable register exhaustion fails
explicitly. Diagnostic slot usage excludes source-language stack objects,
outgoing arguments, callee-save saves and frame alignment. The allocation
algorithm and pre-expansion compatibility checker remain executable unverified
components; acceptance by the existing validator is required. O0 compiler
passes stay disabled independently of allocation optimization.

Focused checks, all within the shared 26 GiB compute domain:

```sh
python3 scripts/guarded.py lake build allocatorTests
python3 scripts/guarded.py .lake/build/bin/allocatorTests
python3 scripts/guarded.py python3 tests/allocator/test_interchange.py
python3 scripts/guarded.py python3 tests/allocator/compare.py
```

The native executable validates every positive RTL fixture with the unchanged
validator and checks optimization witnesses, pressure, reuse, calls, reservations,
constraints, memcpy, va_start, annotations, sparse identifiers and parallel
cycles. Interchange tests cover malformed contexts, frontend snapshots and
malformed builtin placement. `--allocator-report input.json output.json` on the
native compiler is a diagnostic projection of the fixed O0 pipeline through
allocation, with validation; it does not change normal compilation. Comparison
results include local LTL spill/reload counts, remaining moves, stack words and
warm compilation time against pinned CompCert.
