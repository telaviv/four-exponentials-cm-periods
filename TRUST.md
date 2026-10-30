# TRUST: what the Lean certificate proves, and what it assumes

Project: `lean_mstar/` (Lean 4.35, Mathlib v4.35.0; library name `CM4E`). Paper:
`../schanuel/five_exp/pilot_thmM/paper/paper.tex`.

## 1. Axioms

Every declaration depends only on Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`
(`lake env lean Axioms.lean`). There is no `sorry`, no `axiom` declaration, and no `native_decide`.

## 2. What is assumed: explicit hypotheses, never global axioms

The main theorems are implications. Their hypotheses are named arguments.

| name | content | where stated | why it is believed |
|---|---|---|---|
| `hW : Thm11Kappa lemniscatic 4` | Waldschmidt's κ-refined hyperplane theorem (W88 §5d, (5.4)) for `G = G_m⁴ × E`, where `E` is the curve of the lattice `ϖℤ[i]` | `CM4E/Waldschmidt.lean` (statement and source discussion) | Published: W88 = Waldschmidt, CUP 1988, 375–398, §5d p. 394 (Thm 1.1 with (1.2) replaced by (5.4)). Its proof rests on W88 Thm 4.1, whose auxiliary-function step for `W ≠ 0`, `κ > 0` is completed by Lemma U (paper, Appendix A; two internal referees). Fidelity of the Lean statement to the source: `REFEREE_HYP.md` (CORRECT, no encoding bug, no falsification found). |
| `hg₂ : IsAlgebraic ℚ lemniscatic.g₂` | `g₂(ϖℤ[i])` is algebraic | argument of `main` | True: `g₂ = 4` (equivalent to the Γ-formula for `ϖ`; 50-digit check in `REFEREE_HYP.md`). `g₃ = 0` is **proved** (`CM4E.g₃_lemniscatic`). |
| `hS : Irrational (varpi / π)` | `ϖ/π ∉ ℚ` | argument of `main` | True: `π` and `ϖ` are algebraically independent (Chudnovsky 1976). |

**The single point of failure** is the κ-term in W88 Thm 4.1 / §5d. Without it, the instance used in `main` would need
`6 > 6`. An expert check of W88 §§6–7 together with Lemma U is the most valuable outside review.

## 3. What to read to trust a statement

* `CM4E/Defs.lean`: the target statements, in elementary terms (`FourExpAt t`).
* `CM4E/Waldschmidt.lean`: the hypothesis `Thm11Kappa`.
* `CM4E/Lattice.lean`: the period pair `(ϖ, iϖ)` (Mathlib's `PeriodPair`), with `ϖ` given by the Γ-formula.

## 4. Coverage: every result of the paper

✔ = proved in Lean, conditionally on §2 where stated · ◐ = partial · ✗ = not formalised yet.

| paper result | Lean | status / what is missing |
|---|---|---|
| Theorem 1(b) (4E at `cΩ/π`) | `CM4E.MainQi.main`, `CM4E.MainQi.fourExpAt_Qi` | ◐ ✔ for `Ω = ϖ`, `c ∈ ℚ(i)^×` (conditional on `hW, hg₂, hS`). Missing: general algebraic `c` (larger `K`, quotient `A''` of dimension `n/2`), `Ω_ρ` and other CM periods |
| Example `2^{ϖ/π}, 3^{ϖ/π}` | `CM4E.TwoThree.two_three` | ✔ conditional on `hW, hg₂, hS` |
| Theorem 1(a) (4E at `cΩ`; `2^ϖ, 3^ϖ`) | — | ✗ needs the `G_m^{2n} × Q''` hypothesis (vector extension `E^♮`) and the Weierstrass ζ / Legendre relation |
| Theorem MG, Cor. MG2 (K-version) | — | ✗ (only the `FourExpAt` form above) |
| Cor. MG1, Cor. MG3 | — | ✗ need the K-version of MG (`π ∉ 𝓛`), plus Chudnovsky/Baker as named hypotheses |
| Theorem MG♮, Cor. MG♮2 | — | ✗ (see Theorem 1(a)) |
| Affine MG, Cor. (i)–(iii) | — | ✗ (proof sketch in the paper) |
| General form, elliptic 4E | — | ✗ (proof sketch in the paper) |
| Theorem M (both proofs), Cor. M1–Mη | — | ✗ (needs `G = E × G_m × G_a` hypothesis; second proof needs Wüstholz) |
| Theorem MX, Prop. D, MX1, Cor. Γ | — | ◐ arithmetic of the case table ✔ (`CaseCheck.mx_no_obstruction`), Lemma L algebra ✔ (`LemmaL`); missing: `G_a × G_ℓ` hypothesis, subgroup classification, deduction |
| Theorem MX′, Cor. 15 (degree-2) | — | ✗ |
| Lemma K | — | ✗ (pure algebra) |
| MG/MG♮ case tables | `CaseCheck.mg_no_obstruction`, `CaseCheck.mgn_no_obstruction` | ✔ arithmetic layer only (the subgroup classification is not formalised) |
| Lemma U (Appendix A) | — | ✗ Not needed as a separate hypothesis: it is part of the proof of W88 Thm 4.1, which `hW` assumes |
| Consistency checks, partner lemma, §5 heuristics | — | not formalised (not theorems) |

## 5. Relation to `lean_lsg/`

The sibling project `../lean_lsg/` is formalising W88 Thm 4.1 itself (`LSG.W88.Theorem41Abelian`). Once it exists, the
plan is a bridge `Theorem41Abelian → Thm11Kappa L d₁`, i.e. the §5d deduction. That would discharge `hW` and turn the
conditional theorems into unconditional ones, modulo `hg₂` and `hS`.

## 6. Provenance

Written by AI models (Claude, Anthropic) under the direction of the author. All review so far is by AI referees
(`REFEREE_HYP.md` and the paper's referee reports); no human expert has reviewed the definitions or proofs.
