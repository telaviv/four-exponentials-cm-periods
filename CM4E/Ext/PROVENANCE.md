# Provenance of `CM4E/Ext/`

These 32 files (6,518 lines) are a verbatim copy of the part of the author's sibling Lean project `lean_lsg` (library
`LSG`, not yet published) that `CM4E/Final.lean` needs. They were copied from `lean_lsg` commit
`40b9ecfc3d741ca2cea9ebae752ab63af15dbc29` (2026-10-30). The only change is the renaming `LSG` → `CM4E.Ext` in module
names, namespaces and references, so that the copy cannot clash with `lean_lsg` itself. They import only Mathlib and
each other.

What they provide to this project:
* `Weierstrass/`: the Weierstrass `ζ` and `σ` functions of a `PeriodPair`, quasi-periods, Legendre's relation, the
  addition theorem, order two, and a dictionary with Mathlib's group law. `CM4E/MX.lean` uses `Weierstrass.zeta`.
* `LemniscateIndep/`: `g₂(ϖℤ[i]) = 4` from the Γ-formula for `ϖ`.
* `SchneiderLang/`, `Schneider*.lean`: the Schneider–Lang criterion and Schneider's theorem (a nonzero period of a
  lattice with algebraic `g₂, g₃` is transcendental, and so is the period divided by `π`).
* `Bridge/Lemniscatic.lean`: the statements used by `CM4E/Final.lean`.

All files carry the same author's Apache 2.0 header. Two of them say they adapt code from the author's earlier project
on the strong six exponentials theorem (same authors, Apache 2.0): `SchneiderLang/Analytic.lean` (a Schwarz lemma) and
`SchneiderLang/Arith.lean` (a Liouville inequality). A comparison with third-party Lean code found no shared content
beyond generic tactic idioms.

| directory | files | lines |
|---|---|---|
| `Weierstrass/` | 15 | 3,768 |
| `SchneiderLang/` | 8 | 1,538 |
| `LemniscateIndep/` | 4 | 628 |
| top level (`Schneider.lean`, `SchneiderMain.lean`, `SchneiderWp.lean`, `Interface.lean`) | 4 | 531 |
| `Bridge/` | 1 | 53 |

When `lean_lsg` is published, this copy can be replaced by a Lake dependency on it.
