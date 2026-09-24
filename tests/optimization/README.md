# Compiler runtime optimization evidence

This directory preserves the checked implementation equalities and trust audits
for `final-combined-v1`, integrated from baseline
`04d6d02d9e55ad029af85c0a1e1c0588b4b846cb`.

## Preserved proof boundary

The existing ledger-bound definitions, theorem statements and proof bodies are
unchanged. The three amended core modules retain every original source line:

| Module | Original lines preserved | Added lines |
| --- | ---: | ---: |
| `Foundation/Numbers.lean` | 5,770 | 30 |
| `Lib/Iteration.lean` | 245 | 68 |
| `Lib/Coqlib.lean` | 1,532 | 124 |

The additions implement direct natural-to-positive conversion, natural-number
fuel iteration and structural positive comparison. Kernel-checked `@[csimp]`
equalities connect these implementations to the original definitions. Iteration
retains its original fuel-minus-one allowance, early success and exhaustion
behavior. No ledger entries, original definitions or theorem statements change.
`CompositionTrust.lean` audits the replacement equalities and compiler roots.

## Other improvements and evidence

Allocator work avoids unnecessary coalescing scans, graph and array copies,
move-set traversals, repeated classification and temporary register lists.
Smaller-set union, cardinality checks and safe pointer equality reduce set work.
An ordered cache avoids repeated scans for fixed locations. Graph updates release
obsolete owners, and pairwise interference shares its invariant live set.
Metadata uses positive-key indexes. Small unchanged helpers gain inline
attributes, and independent driver version probes run concurrently.

The proof files establish their stated local equalities for arbitrary inputs.
The allocator tests also compare complete states against reference operations.
The fixed-location cache has a reviewed invariant and differential tests; these
artifacts do not claim a complete Lean invariant proof for that cache or a new
end-to-end compiler correctness theorem. Existing allocation validators remain
in place.

Run the following from the repository root:

```bash
lake build
python3 -B tests/prototype/verify_o2.py
lake env lean tests/prototype/Metadata.lean
for proof_source in tests/optimization/*.lean; do
  lake env lean "$proof_source" || exit
done
```

The recorded validation passes the combined 372-job build, all 14 established
runtime checks, all eleven proof files and 36 transitive axiom audits. The only
axiom dependencies are the existing `propext`, `Classical.choice` and
`Quot.sound`. It also passes 139 execution cases at each O0 and O2, with nine
existing exclusions per profile; 749 retained assembly comparisons; 24 generated
assembly comparisons and 72 upstream execution comparisons; and 225 mode,
diagnostic and error comparisons. Every compared output matches.

## Recorded performance

Median CPU seconds from three alternating serial pairs pinned to CPU 2:

| Input | Baseline | Optimized | Reduction |
| --- | ---: | ---: | ---: |
| LBM O0 | 0.366792 | 0.264511 | 27.89% |
| LBM O2 | 3.417167 | 1.472945 | 56.90% |
| NAB O0 | 4.036921 | 0.917044 | 77.28% |
| NAB O2 | 5.608431 | 1.672636 | 70.18% |
| SPASS O2 | 9.356748 | 4.007023 | 57.18% |
| zstd O2 | 48.698778 | 3.550551 | 92.71% |

These timings measure native Csyntax JSON to assembly JSON compilation, including
process startup and JSON processing. External frontend preparation and linking
are excluded. Eleven-pair small-input comparisons improve 20.79–25.04% over the
baseline. All 248 final timed outputs match. These measurements describe the
tested workloads, not a universal speedup guarantee.

The original source patch SHA-256 is
`a7e8760b82ff928a542be6ae6b1b467f2ddbe2a4414882ba2885b81251b94bdd`;
the saved executable SHA-256 is
`8b85625cc49d9c11c13671c1827fe29a38530585d330de46030a4c7b40303837`.
The meta-repository agent log records the retained raw evidence and integration
receipt. The eleven proof files here are byte-identical to the validated copies.
