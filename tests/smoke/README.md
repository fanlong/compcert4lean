# Upstream smoke tests

These C sources and expected stdout files are unchanged bytes from
[CompCert-small-tests](https://github.com/AbsInt/CompCert-small-tests), commit
`081175df374260304a5cd78dd3dfaded93dceb41`. `provenance.json` records each
upstream path and SHA-256; the runner verifies these hashes before testing.

| Source | Expected stdout | Coverage |
| --- | --- | --- |
| `for2.c` | `for2.expected` | Globals, shadowing, loops, mutation, printf |
| `funct3.c` | `funct3.expected` | Internal calls, unsigned conversions, ABI |
| `switch.c` | `switch.expected` | Switches, branches, loops, repeated calls |

The upstream `LICENSE` and `README.md` are preserved as `LICENSE` and
`UPSTREAM-README.md`. Upstream distributes these tests under GPL-2.0-or-later; consult
the preserved license for its terms. Expected stdout comes from upstream's
`regression/Results/` directory, not from either compiler under test.

Run `python3 scripts/smoke_test.py` from the Lean repository. Both the Lean
pipeline and pinned CompCert must exit zero and match upstream stdout exactly.
Each run retains separate reference and Lean artifacts under
`.lake/prototype/smoke-*`, including failures. See `../../PROTOTYPE.md` for
setup, configuration, limits, and the repository's required compute wrapper.
