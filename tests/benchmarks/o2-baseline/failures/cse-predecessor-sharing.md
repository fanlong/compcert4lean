# CSE predecessor-map sharing defect

Classification: compiler-core performance defect. The affected correctness
case is `abi/layout` at O2. Its failing timeout verdict is retained. This is
not a claim of incorrect generated code or a completed proof obligation.

The frozen definition is
`CompCert4Lean.Backend.Kildall.BBlock_solver.basic_block_map` in
`CompCert4Lean/Backend/Kildall.lean`, used by `BBlock_solver.fixpoint` during
`CompCert4Lean.Backend.CSE.analyze`. The Lean definition places
`make_predecessors code successors` **inside** `fun pc => ...`. Each lookup
therefore reconstructs the entire predecessor graph. The pinned source
`CompCert/backend/Kildall.v:1226` partially applies `is_basic_block_head` to
one computed predecessor map. Both versions classify the same nodes, but the
Lean version loses sharing and makes a complete basic-block-head scan
quadratic in the number of RTL nodes.

The generated native C confirms this directly: the body of
`...BBlock__solver_basic__block__map___redArg` calls
`...Kildall_make__predecessors___redArg` on every invocation. This is a core
definition issue, independent of selection, register allocation, layout,
frontend metadata, or input interchange.

The seed-20260922 layout fixture reaches `rtl-5` in 734 ms and has a 39,194-node
main function. The original full compilation times out at its unchanged
300-second deadline. Diagnostic replay reaches the same CSE input and then
stops making pass progress before `rtl-6`. The reference compiler completes
and matches the unchanged expected output. The corresponding O0 run is
recorded separately in the baseline report.

## Isolated reproducer

`tests/prototype/CSEReproducer.lean` constructs well-typed straight-line RTL
without any frontend, interchange, or runtime-provider calls. It invokes the
frozen core helper and complete core CSE pass. Its diagnostic control computes
the predecessor map once and is definitionally equal to the original function
(`rfl` is checked). The control is never used by the production compiler.

```sh
python3 scripts/guarded.py lake build coreDiagnostics
python3 scripts/guarded.py .lake/build/bin/coreDiagnostics
```

Native execution in guard `20260923T041109-4737c17b` gives:

| RTL nodes | Core head scan | Shared-map diagnostic control | Complete core CSE |
| ---: | ---: | ---: | ---: |
| 1,000 | 0.181003 s | 0.000329 s | 0.396694 s |
| 2,000 | 0.854807 s | 0.000761 s | 1.841912 s |
| 4,000 | 4.025423 s | 0.001667 s | 7.576908 s |

Every input passes `RTLtyping.type_function`. Both scans return the same single
entry block, and the complete CSE transformation succeeds on the smaller
inputs. Doubling the input costs roughly four times as much in the core scan;
the otherwise identical control scales approximately linearly. This identifies
the concrete cause of the large-case timeout instead of inferring a core
failure merely from O0/O2 disagreement or a timeout.

Reproduce the actual fixture with:

```sh
python3 scripts/guarded.py python3 scripts/small_tests.py \
  --optimization O2 --test abi/layout --seed 20260922
```

The original Csyntax JSON, preprocessed input, generated ABI fixture, commands,
timeout records, pass diagnostics, and native reproducer output are retained
in the evidence archive. The production core definition is unchanged because
the owner's exception authorizes adapters, runtime helpers and allocator
repairs only. Correcting the sharing in this frozen definition needs a
separate owner-authorized core change; no bypass or reduced O2 profile is used.
