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

## Trust and completeness

- Production code must not use `sorry`, project axioms, `unsafe`, `partial`,
  `native_decide`, unchecked FFI, or hidden native replacements.
- When a later theorem is intentionally not yet proved, record its exact
  statement descriptor; do not add a theorem stub.

## Verification and handoff

- Run the packet's narrow build command.
- Return only the compact structured worker delta. Do not reproduce packet or
  Git identities, hashes, changed-file lists, command records, or one outcome
  per action; the coordinator derives those fields mechanically.
- Include declaration/surface exceptions, consulted mandatory decision IDs,
  trust concerns, discrepancies, requested context, and the proposed next
  action. Empty exception arrays are normal.
