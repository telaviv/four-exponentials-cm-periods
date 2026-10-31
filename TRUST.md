# TRUST: what the Lean certificate proves, and what it assumes

Project: `lean_mstar` (Lean 4.35, Mathlib v4.35.0; library `CM4E`). Paper: *Four exponentials at CM periods, and a
bilinear statement for two CM elliptic curves* (draft; snapshot in [`paper/`](paper/)). W88 below is M. Waldschmidt,
*On the transcendence methods of Gel'fond and Schneider in several variables*, in: A. Baker (ed.), New Advances in
Transcendence Theory (Durham 1986), Cambridge Univ. Press, 1988, pp. 375–398.

## 1. Axioms

Every declaration depends only on Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`
(`lake env lean Axioms.lean`). There is no `sorry`, no `axiom` declaration and no `native_decide`, in `CM4E/` or in the
vendored `CM4E/Ext/`.

## 2. The final theorems

`CM4E/Final.lean` states the results with every input proved except W88:

| theorem | statement | assumes |
|---|---|---|
| `CM4E.Final.two_three` | `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic | `hW : Thm11Kappa lemniscatic 4` |
| `CM4E.Final.fourExpAt_Qi` | `FourExpAt (cϖ/π)` for `c = (p + qi)/D ≠ 0` | `hW : Thm11Kappa lemniscatic 4` |
| `CM4E.Final.two_three_varpi` | `2^ϖ` and `3^ϖ` are not both algebraic | `hW : MainNat.Thm11KappaNat` |
| `CM4E.Final.fourExpAt_varpi` | `FourExpAt (cϖ)` for `c = D/(p + qi) ≠ 0` | `hW : MainNat.Thm11KappaNat` |
| `CM4E.Final.mx` | Theorem MX, `K`-form, for `K = ℚ(i, √3)`, `β ∈ Kˣ` | `hW : MX.Thm11KappaMX`, `hg₂'`, `hg₃'`, `hΓ`, `hM` |

`FourExpAt t` (`CM4E/Defs.lean`): for `ℚ`-linearly independent `a, b` with `e^a, e^b` algebraic, `e^{ta}` and `e^{tb}`
are not both algebraic. The determinations of `α^t, β^t` are thus tied to the chosen logarithms. The two
parametrisations `tExp p q D = ((p + qi)/D)·ϖ/π` and `tN p q D = D·ϖ/(p + qi)` both cover all of `ℚ(i)ˣ`.

Inputs that are **proved** (in `CM4E/Ext/` and `CM4E/Lattice.lean`) and discharged in `Final.lean`:
* `g₂(ϖℤ[i])` is algebraic (`Final.hg₂`; `g₂ = 4` from the Γ-formula for `ϖ`); `g₃(ϖℤ[i]) = 0` (`g₃_lemniscatic`);
* `ϖ/π ∉ ℚ` (`Final.hS`) and `ϖ` transcendental (`Final.hT`): Schneider's theorem.

## 3. What is assumed: explicit hypotheses, never global axioms

| name | content | where stated | why it is believed |
|---|---|---|---|
| `hW : Thm11Kappa lemniscatic 4` | W88 Thm 1.1 with (1.2) replaced by (5.4) (§5d, p. 394) for `G = G_m⁴ × E`, `E` the curve of `ϖℤ[i]` | `CM4E/Waldschmidt.lean` (model `gmE`) | Published. Its proof rests on W88 Thm 4.1, whose auxiliary-function step for `W ≠ 0`, `κ > 0` is completed by Lemma U (paper, Appendix A). Fidelity: [`reviews/REFEREE_HYP.md`](reviews/REFEREE_HYP.md) (CORRECT). |
| `hW : Thm11KappaNat` | the same theorem for `G″ = G_m⁸ × Q″`, `Q″ = (E_i^♮)⁴/U` from the paper's proof of Theorem MG♮ (`K = ℚ(i, √2)`, `n = 4`) | `CM4E/MainNat.lean` (model `gmQ`, soundness facts in its docstring) | Same source. The model (coordinates, periods via Legendre, the subgroup list) is hand-written, not derived in Lean. Fidelity: [`reviews/REFEREE_HYP_NAT.md`](reviews/REFEREE_HYP_NAT.md) (CORRECT, cosmetic caveats only). |
| `hW : Thm11KappaMX` | the same theorem for `G″ = G_a × G_ℓ = (E_i^♮ × E_ρ^♮ × G_a²)⁴/U` from the paper's proof of Theorem MX (`K = ℚ(i, √3)`, `n = 4`, `(d₀, d₁, d₂) = (1, 0, 9)`) | `CM4E/MX.lean` (model `gmX`, soundness facts 1–6 in its docstring) | Same source. Hand-written model. Fidelity: [`reviews/REFEREE_HYP_MX.md`](reviews/REFEREE_HYP_MX.md) (CORRECT, cosmetic caveats only). |
| `hg₂'`, `hg₃'` | `g₂`, `g₃` of `Ω_ρℤ[ρ]` are algebraic | arguments of `MX.main` | True: `g₂ = 0`, `g₃ = 4` for `Ω_ρ = Γ(1/3)³/(2^{4/3}π)` (40-digit check in `reviews/REFEREE_HYP_MX.md`); not proved in Lean. |
| `hΓ`, `hM` | `ϖΩ_ρ/π ∉ ℚ̄`, `Ω_ρ/ϖ ∉ ℚ̄` | arguments of `MX.main` | Wüstholz's analytic subgroup theorem (1989): a period of `E_i` and a quasi-period of `E_ρ`, resp. periods of non-isogenous curves, are `ℚ̄`-linearly independent (derivations in `reviews/REFEREE_HYP_MX.md`). |

All three `hW` have the same form `HyperplaneKappa G` for a `GroupModel G` (`CM4E/Waldschmidt.lean`). A model is
*sound* if its logarithms, periods and subgroup family are true of the group; soundness is checked by the reviews, not
by Lean.

Two further points about what the statements rely on:
* `MX.main` itself (not only its hypothesis `hW`) is stated with hand-coded quasi-periods (`etaLem`, `etaR`, `etaRho`)
  and the coordinate convention `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))` in `LogNat`. `ζ` is the standard series
  (`CM4E.Ext.Weierstrass.zeta`, with `ζ' = −℘` proved). The quasi-period values were checked numerically against this
  `ζ` in `reviews/REFEREE_HYP_MX.md`.
* `HyperplaneKappa gmE` also covers configurations with `κ = 5`, outside the range `2N ≥ d₁ + 2d₀ + κ` of Lemma U. By
  the argument of the paper-vs-Lean review (2026-10-30), `V` is then forced to be rational, so the conclusion holds
  trivially; this argument is not formalised. For `gmQ` and `gmX` Lemma U's
  range covers every configuration.

All three Lean proofs follow the paper's §5d derivations (paper Remarks 15, 20, 26), which apply the paper's
Theorem 11 (W88 Thm 1.1 with (5.4)).

**The single point of failure** is the κ-term in W88 Thm 4.1 / §5d. Without it, the instance used in `MainQi.main` would
need `6 > 6`, `MainNat.main` would need `12 > 14`, and `MX.main` would need `12 > 18`, all false. An expert check of
W88 §§6–7 together with Lemma U is the most valuable outside review. It should cover the regimes used here: `W ≠ 0`,
`κ > 0`, a non-semiabelian `G₂` (`MainNat`, `MX`), and `d₀ > 0` (`MX`, which relies on the Gel'fond part of W88's
proof; the paper's Appendix A notes that the case `δ = τ` needs `b > 1` there). Note also that W88's §5d proof
applies Thm 4.1 twice: to `G` itself, and again to an auxiliary subgroup given by W88 Lemma 5.1. Lemma U's condition
has been checked only for the first application, so every `hW` rests on W88 §5d as published (paper, §2, after
Theorem 11).

## 4. What to read to trust a statement

* `CM4E/Defs.lean`: the elementary definitions (`FourExpAt`, `logAlg`, `varpi`, `omegaRho`).
* `CM4E/Waldschmidt.lean`: the hypothesis form `HyperplaneKappa` and the model `gmE`.
* `CM4E/Lattice.lean`: the period pair `(ϖ, iϖ)` (Mathlib's `PeriodPair`) with `ϖ` given by the Γ-formula.
* `CM4E/Final.lean`: the final statements.

## 5. Coverage: every result of the paper

✔ = proved in Lean, conditionally on §3 · ◐ = partial · ✗ = not formalised.

| paper result | Lean | status / what is missing |
|---|---|---|
| Theorem 1(b) (4E at `cΩ/π`) | `MainQi.fourExpAt_Qi`, `Final.fourExpAt_Qi` | ◐ ✔ for `Ω = ϖ`, `c ∈ ℚ(i)ˣ`. Missing: general algebraic `c`, other CM periods |
| Example `2^{ϖ/π}, 3^{ϖ/π}` | `TwoThree.two_three`, `Final.two_three` | ✔ |
| Theorem 1(a) (4E at `cΩ`; `2^ϖ, 3^ϖ`) | `MainNat.main`, `MainNat.two_three_varpi`, `Final.fourExpAt_varpi`, `Final.two_three_varpi` | ◐ ✔ for `Ω = ϖ`, `c ∈ ℚ(i)ˣ`; `2^ϖ, 3^ϖ` ✔. Missing: general `c`, `Ω_ρ` |
| Theorem MG, Cor. MG2 (`K`-version) | — | ✗ (only the `FourExpAt` form above) |
| Cor. MG1, Cor. MG3 | — | ✗ (need the `K`-version of MG; MG3 needs Baker) |
| Theorem MG♮, Cor. MG♮2 | — | ◐ only the `FourExpAt` form at `t = cϖ`, `c ∈ ℚ(i)` |
| Affine MG; general form, elliptic 4E | — | ✗ (proof sketches in the paper) |
| Theorem M, Cor. M1–Mη | — | ✗ |
| Theorem MX, Prop. D, Cor. MX1, Cor. Γ | `MX.main`, `Final.mx` | ◐ ✔ Proposition D for `v ∈ Ψ(Λ(G))`, i.e. `z(X) + z(Y) + a ∈ Kϖ + KΩ_ρ`, for `K = ℚ(i, √3)`, `β ∈ Kˣ`, via the paper's §5d count (`12 > 18 − κ`, `κ ≥ 8`). Missing: general `β ∈ ℚ̄ˣ`, the step to `a = 0`, `z(X) ∈ ℚ(i)ϖ` (Bertrand–Masser/Wüstholz, Masser), Cor. MX1 |
| Theorem MX′, degree-two corollary | — | ✗ |
| Lemma K | — | ✗ |
| Case tables of MG, MG♮, MX (Thm 4.1 route) | `CaseCheck.*` | ✔ arithmetic layer only; not used by the theorems above, which take the §5d route |
| Step 1 of Prop. D (algebra) | `LemmaL.*` | ✔; not used by `MX.main` |
| Lemma U (Appendix A) | — | not a separate hypothesis: part of the proof of W88 Thm 4.1, which `hW` assumes |

## 6. Vendored code

`CM4E/Ext/` (32 files, 6,518 lines) is a renamed verbatim copy of the needed part of the author's sibling project
`lean_lsg`: Weierstrass `ζ`/`σ`, Legendre's relation, `g₂(ϖℤ[i]) = 4`, and Schneider's theorem. Details and source
commit: [`CM4E/Ext/PROVENANCE.md`](CM4E/Ext/PROVENANCE.md). The project depends on nothing but Mathlib.

## 7. Reviews and provenance

Written by AI models (Claude, Anthropic) under the direction of the author. All review so far is by AI referees: the
three fidelity reports in [`reviews/`](reviews/) (scripts and outputs in `reviews/checks/`) and the paper's own referee
reports. No human expert has reviewed the definitions or proofs.
