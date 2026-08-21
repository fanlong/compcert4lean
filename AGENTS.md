# CompCert4Lean production-worker constitution

## Source and destination

- The read-only source of truth is CompCert 3.17 at commit
  `7b1f02b09954b9b916eb2a91d283c9b5355bf172`.
- Production Lean code belongs in this repository.

## Packet boundaries and ownership

- Edit only the files owned by the assigned packet.
- Preserve mapped names and canonical provider ownership.
- Keep one writer per file.
- Use package-qualified imports rooted at `CompCert4Lean`.
- Do not change scope, architecture, provider ownership, or adjacent files. If
  any such change appears necessary, return a structured escalation instead.
- The owner-ratified `DMC-001` definition-migration policy is
  dependency-selected coverage, not full public-declaration coverage for every
  mapped module.
  Do not reopen that policy; escalate only a concrete missing dependency or
  feature obligation in the assigned selected closure.

## Trust and completeness

- Production code must not use `sorry`, project axioms, `unsafe`, `partial`,
  `native_decide`, unchecked FFI, or hidden native replacements.
- When a later theorem is intentionally not yet proved, record its exact
  statement descriptor; do not add a theorem stub.
- Under `DMC-003`, proof bodies and invariant discharge belong to the later proof-grinding
  phase. Preserve exact propositions, proof-field obligations, constructor
  obligations, and proof duties. A proof-only source field may use an
  explicitly mapped companion certificate/obligation; never replace it with
  `True`, an arbitrary inhabitant, or an omitted proposition.
- Under `DMC-002`, exact source shape is the default for computational and invariant-bearing
  declarations. Use a Lean-native representation difference only when the
  packet supplies an accepted, evidence-backed exception; otherwise escalate
  the mismatch rather than treating the general policy as undecided.
- Under `DMC-004`, runtime solver operations may remain separate from proofs,
  but generic certified solver interfaces and correctness statements must
  require companion certificates containing the exact source laws. Preserve
  those propositions and their proof owners during definition migration; the
  proof terms belong to proof grinding.
- Under `DMC-005`, explicit injected selection and register-allocation oracles
  satisfy the formal definition boundary. Preserve the same oracle values
  across compiler definitions and theorem-facing relations, retain source
  validators, and do not invent a hidden default. Concrete host providers are
  a separate runnable-compiler milestone, not a definition-migration gate.
- Under `DMC-006`, preserve every Rocq-generated proof surface consumed by a
  selected source declaration, including its exact proposition and ownership,
  but do not escalate an unreferenced generic proof helper merely because Rocq
  generates it automatically. This exception never covers primary
  declarations, computational constructors, or record projections.

## Verification and handoff

- Run the packet's narrow build command.
- Return only the compact structured worker delta. Do not reproduce packet or
  Git identities, hashes, changed-file lists, command records, or one outcome
  per action; the coordinator derives those fields mechanically.
- Include declaration/surface exceptions, consulted mandatory decision IDs,
  trust concerns, discrepancies, requested context, and the proposed next
  action. Empty exception arrays are normal.
