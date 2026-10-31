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
| `hW : Thm11KappaNat` | the same theorem (W88 §5d, (5.4)), for `G″ = G_m⁸ × Q″`, where `Q″ = (E_i^♮)⁴/U` is the anti-affine quotient of the paper's proof of Theorem MG♮ (`K = ℚ(i, √2)`, `n = 4`) | `CM4E/MainNat.lean` (model `gmQ`, its docstring lists the soundness facts) | Same source as above. The encoding of `G″` (coordinates, periods via Legendre `ϖη(ϖ) = π`, and the subgroup list "every nonzero subgroup of `Q″` contains the `G_a`-fibre") is a hand-written model, **not** derived in Lean. Its fidelity rests on the paper's MG♮ proof (`../schanuel/five_exp/pilot_epi2_mix/REFEREE_MGF_2.md` #1–2) and `REFEREE_HYP_NAT.md` (CORRECT, cosmetic caveats only: every soundness fact re-derived independently, `ker φ` checked exactly, Legendre/η checked numerically to 40 digits). Both hypotheses have the identical form `HyperplaneKappa G` for a `GroupModel G`. |
| `hT : Transcendental ℚ (varpi : ℂ)` | `ϖ` is transcendental | argument of `MainNat.main` | True: Schneider 1937 (periods of CM curves with algebraic invariants). |
| `hW : Thm11KappaMX` | the same theorem (W88 §5d, (5.4)), for `G″ = G_a × G_ℓ = (E_i^♮ × E_ρ^♮ × G_a²)⁴/U` of the paper's proof of Theorem MX (`K = ℚ(i, √3)`, `n = 4`, `d₀ = 1`, `d₁ = 0`, `d₂ = 9`) | `CM4E/MX.lean` (model `gmX`, soundness facts 1–6 in its docstring) | Same source. Hand-written model, **not** derived in Lean: the coordinates `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))` on `E^♮` (`LogNat`), the quasi-periods (Legendre), `lam` = `ℚ`-span of images of `Λ(G⁴)`, and `sub` = "every nonzero algebraic subgroup has an algebraic tangent vector outside `ker Ψ″`" (short proof in the docstring). Fidelity: `REFEREE_HYP_MX.md` (CORRECT, cosmetic caveats only: `LogNat` = `Λ(E^♮)`, η values and `g₂ = 0`, `g₃ = 4` checked numerically, `perX` is all of `ℚ ⊗ Ker exp` (rank 16), `sub` and Lemma K re-proved, `(d₀, d₁, d₂) = (1, 0, 9)` maximal). `ζ` is defined in Lean as the standard series, with a proof that the series converges locally uniformly. |
| `hg₂, hg₂', hg₃'` | `g₂(ϖℤ[i])`, `g₂, g₃(Ω_ρℤ[ρ])` algebraic | arguments of `MX.main` | True: `g₂ = 4`; `g₂ = 0`, `g₃ = 4` for `Ω_ρ = Γ(1/3)³/(2^{4/3}π)` (not proved in Lean). |
| `hΓ`, `hM` | `ϖΩ_ρ/π ∉ ℚ̄`, `Ω_ρ/ϖ ∉ ℚ̄` | arguments of `MX.main` | True: Wüstholz 1989 (a period of `E_i` and a quasi-period of `E_ρ`, resp. periods of non-isogenous curves, are `ℚ̄`-independent; derivations in `REFEREE_HYP_MX.md`). `hΓ` is Corollary Γ of the paper. |

**The single point of failure** is the κ-term in W88 Thm 4.1 / §5d. Without it, the instance used in `MainQi.main` would need
`6 > 6` (and `MainNat.main` would need `12 > 14 − 0`, false). An expert check of W88 §§6–7 together with Lemma U is the most valuable outside review. (`MX.main` needs `12 > 18 − 0`
without κ, also false.)
That check should explicitly cover the non-semiabelian case: `Q″` is a non-split extension of an abelian surface by
`G_a`. This is inside W88's stated scope, but it is used only by `MainNat`; `MainQi` (`G_m⁴ × E`) is semiabelian.
It should also cover `d₀ > 0`: `gmX` (`MX.main`) is the only model with a `G_a` factor (`d₀ = 1`), so it relies on the
Gel'fond (`G_a`) part of W88's proof, where the paper's Appendix A notes that the case `δ = τ` needs `b > 1`. The regimes
to check are thus: `W ≠ 0`, `κ > 0`, non-semiabelian `G₂` (`MainNat`, `MX`), and `d₀ > 0` (`MX`).
W88 scans: `../schanuel/five_exp/ref/w88_pages/`.

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
| Theorem 1(a) (4E at `cΩ`; `2^ϖ, 3^ϖ`) | `CM4E.MainNat.main`, `CM4E.MainNat.two_three_varpi` | ◐ ✔ for `Ω = ϖ`, `c ∈ ℚ(i)^×` (conditional on `hW : Thm11KappaNat`, `hg₂`, `hT`); headline `2^ϖ, 3^ϖ` ✔. Missing: general algebraic `c`, `Ω_ρ`. The Legendre relation enters through the model `gmQ`, not through a Lean proof |
| Theorem MG, Cor. MG2 (K-version) | — | ✗ (only the `FourExpAt` form above) |
| Cor. MG1, Cor. MG3 | — | ✗ need the K-version of MG (`π ∉ 𝓛`); MG1 no longer uses Chudnovsky (paper Revision 6: only `e^{bπΩ} ∈ ℚ̄`, `Ω ∉ ℚ̄𝓛`, `Ω/π ∉ ℚ̄`); MG3 needs Baker |
| Theorem MG♮, Cor. MG♮2 | — | ◐ only the `FourExpAt` form at `t = cϖ`, `c ∈ ℚ(i)` (Theorem 1(a) row) |
| Affine MG, Cor. (i)–(iii) | — | ✗ (proof sketch in the paper) |
| General form, elliptic 4E | — | ✗ (proof sketch in the paper) |
| Theorem M (both proofs), Cor. M1–Mη | — | ✗ (needs `G = E × G_m × G_a` hypothesis; second proof needs Wüstholz) |
| Theorem MX, Prop. D, MX1, Cor. Γ | `CM4E.MX.main` | ◐ ✔ Proposition D, restricted to `v ∈ Ψ(Λ(G))` (the case Theorem MX uses), in the form `z(X) + z(Y) + a ∈ Kϖ + KΩ_ρ` for `K = ℚ(i, √3)`, `β ∈ Kˣ` (conditional on `hW : Thm11KappaMX`, `hg₂, hg₂', hg₃'`, `hΓ`, `hM`), via the §5d derivation of the paper's Remark "The count" (`12 > 18 − κ`, `κ ≥ 8`). Missing: general `β ∈ ℚ̄ˣ` (larger `K`), the step `a = 0`, `z(X) ∈ ℚ(i)ϖ` (Bertrand–Masser/Wüstholz, Masser's theorem on CM periods) and Cor. MX1. Case-table arithmetic ✔ (`CaseCheck.mx_no_obstruction`), Lemma L ✔ (`LemmaL`) |
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
