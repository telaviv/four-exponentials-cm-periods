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

`CM4E/Final.lean` states the results with every input proved except W88 (and, where listed, named classical inputs):

| theorem | statement | assumes |
|---|---|---|
| `Final.fourExpAt_varpi_all` | `FourExpAt (cϖ)` for every algebraic `c ≠ 0` (Theorem 1(a), `Ω = ϖ`) | `hW : Gen.Thm11KappaMGn Gen.latI` |
| `Final.fourExpAt_varpi_div_pi_all` | `FourExpAt (cϖ/π)` for every algebraic `c ≠ 0` (Theorem 1(b), `Ω = ϖ`) | `hW : Gen.Thm11KappaMG Gen.latI` |
| `Final.fourExpAt_omegaRho_all` | `FourExpAt (cΩ_ρ)` for every algebraic `c ≠ 0` | `hW : Gen.Thm11KappaMGn Gen.latRho`, `hg₂'`, `hg₃'` |
| `Final.fourExpAt_omegaRho_div_pi_all` | `FourExpAt (cΩ_ρ/π)` for every algebraic `c ≠ 0` | `hW : Gen.Thm11KappaMG Gen.latRho`, `hg₂'`, `hg₃'` |
| `Final.two_three_varpi`, `Final.two_three`, `Final.two_three_omegaRho` | `2^t, 3^t` not both algebraic for `t = ϖ`, `ϖ/π`, `Ω_ρ` | `hW : MainNat.Thm11KappaNat`, resp. `Thm11Kappa lemniscatic 4`, resp. `Gen.Thm11KappaMGn Gen.latRho` with `hg₂'`, `hg₃'` |
| `Final.fourExpAt_varpi`, `Final.fourExpAt_Qi` | the same for `c ∈ ℚ(i)ˣ`, from one fixed group (`K = ℚ(i, √2)`, resp. `ℚ(i)`) | `hW : MainNat.Thm11KappaNat`, resp. `Thm11Kappa lemniscatic 4` |
| `Final.mx_K` | Theorem MX, `K`-form: `z(X) + z(Y) + a ∈ ℚ̄ϖ + ℚ̄Ω_ρ`, every `β ∈ ℚ̄ˣ` | `hW : Gen.Thm11KappaMXG`, `hg₂'`, `hg₃'`, `hΓ`, `hM` |
| `Final.mx` | Theorem MX: `a = 0`, `z(X) ∈ ℚ(i)ϖ`, `z(Y) ∈ ℚ(ρ)Ω_ρ`, every `β ∈ ℚ̄ˣ` | the above (with `hM` derived) and `WuestholzMX`, `MasserCM` |
| `Final.mx1` | Corollary MX1 | the above and `LaurentZeta` |

`FourExpAt t` (`CM4E/Defs.lean`): for `ℚ`-linearly independent `a, b` with `e^a, e^b` algebraic, `e^{ta}` and `e^{tb}`
are not both algebraic. The determinations of `α^t, β^t` are thus tied to the chosen logarithms.

The general-`c` theorems use, for each `c`, a number field `K ∋ c` with an adapted basis (`Gen.exists_adapted_basis`,
proved) and the hypothesis for the group built from that `K`; this is why their `hW` quantifies over all adapted bases.
The `ℚ(i)` versions need W88 for one fixed group only, which is a weaker assumption.

Inputs that are **proved** (in `CM4E/Ext/` and `CM4E/Lattice.lean`) and discharged in `Final.lean`:
* `g₂(ϖℤ[i])` is algebraic (`Final.hg₂`; `g₂ = 4` from the Γ-formula for `ϖ`); `g₃(ϖℤ[i]) = 0` (`g₃_lemniscatic`);
* `ϖ/π ∉ ℚ` (`Final.hS`), `ϖ` and `ϖ/π` transcendental (`Final.hT`): Schneider's theorem; for `Ω_ρ`, Schneider's
  theorem is applied with `hg₂'`, `hg₃'`;
* in Corollary MX1, `u + a ≠ 0` (Schneider: `℘` is transcendental at nonzero algebraic non-periods).

## 3. What is assumed: explicit hypotheses, never global axioms

| name | content | where stated | why it is believed |
|---|---|---|---|
| `hW : Thm11Kappa lemniscatic 4` | W88 Thm 1.1 with (1.2) replaced by (5.4) (§5d, p. 394) for `G = G_m⁴ × E`, `E` the curve of `ϖℤ[i]` | `CM4E/Waldschmidt.lean` (model `gmE`) | Published. Its proof rests on W88 Thm 4.1, whose auxiliary-function step for `W ≠ 0`, `κ > 0` is completed by Lemma U (paper, Appendix A). Fidelity: [`reviews/REFEREE_HYP.md`](reviews/REFEREE_HYP.md) (CORRECT). |
| `hW : Thm11KappaNat` | the same theorem for `G″ = G_m⁸ × Q″`, `Q″ = (E_i^♮)⁴/U` (`K = ℚ(i, √2)`, `n = 4`) | `CM4E/MainNat.lean` (model `gmQ`) | Same source; hand-written model. Fidelity: [`reviews/REFEREE_HYP_NAT.md`](reviews/REFEREE_HYP_NAT.md) (CORRECT). |
| `hW : Gen.Thm11KappaMGn L` | the same theorem for `G_m^{2n} × Q″`, `Q″ = (E^♮)^n/U`, for every number field `K` with an adapted basis; `L` is a CM lattice (`latI`, `latRho`) | `CM4E/Gen/MGn.lean` (model `gmMGn`, on the frame `gmF` of `CM4E/Gen/Frame.lean`) | Same source; hand-written model (tangent space `ℂ^n/ℂ·ker φ × ℂ`). Fidelity: [`reviews/REFEREE_HYP_GEN.md`](reviews/REFEREE_HYP_GEN.md) (CORRECT; it also found the sign condition `Im α > 0`, now required). |
| `hW : Gen.Thm11KappaMG L` | the same theorem for `G_m^{2n} × A″`, `A″ = E^n/B_{ker ψ}`, every adapted `K` | `CM4E/Gen/MG.lean` (model `gmMG`) | Same; fidelity in `reviews/REFEREE_HYP_GEN.md` (CORRECT). |
| `hW : Gen.Thm11KappaMXG` | the same theorem for `G″ = G_a × G_ℓ = (E_i^♮ × E_ρ^♮ × G_a²)^n/U`, every adapted `K ∋ i` | `CM4E/Gen/MXGen.lean` (model `gmXG`) | Same; the model reviewed in [`reviews/REFEREE_HYP_MX.md`](reviews/REFEREE_HYP_MX.md) for `K = ℚ(i, √3)`, with general `K`; review of the general form: `reviews/REFEREE_HYP_MXG.md`. |
| `hg₂'`, `hg₃'` | `g₂`, `g₃` of `Ω_ρℤ[ρ]` are algebraic | arguments | True: `g₂ = 0`, `g₃ = 4` for `Ω_ρ = Γ(1/3)³/(2^{4/3}π)` (40-digit checks in `reviews/`); not proved in Lean. |
| `hΓ` | `ϖΩ_ρ/π ∉ ℚ̄` (Corollary Γ) | argument of the MX theorems | Wüstholz's analytic subgroup theorem (1989): a period of `E_i` and a quasi-period of `E_ρ` are `ℚ̄`-linearly independent. |
| `hM` | `Ω_ρ/ϖ ∉ ℚ̄` | argument of `Final.mx_K` | Wüstholz 1989; derived from `WuestholzMX` in `Gen.mx_full`. |
| `Gen.WuestholzMX` | a `ℚ̄`-linear relation `z_X + z_Y + a = xϖ + x'Ω_ρ` between elliptic logarithms of `E_i`, `E_ρ` forces `a = 0`, `z_X = xϖ`, `z_Y = x'Ω_ρ` | `CM4E/Gen/MXGen.lean` | Wüstholz 1989, applied to `E_i² × E_ρ² × G_a` (argument in the docstring). |
| `Gen.MasserCM` | an elliptic logarithm that is an algebraic multiple `xω` of the period has `x` in the CM field | `CM4E/Gen/MXGen.lean` | Masser 1975; also Wüstholz on `E²`. |
| `Gen.LaurentZeta` | `ζ(u)` is transcendental for non-torsion `u` on `E_i` with `℘(u), ℘'(u)` algebraic | `CM4E/Gen/MXGen.lean` | Laurent 1980 (`1, u, ζ(u)` are `ℚ̄`-independent). |

All `hW` have the same form `HyperplaneKappa G` for a `GroupModel G` (`CM4E/Waldschmidt.lean`). A model is
*sound* if its logarithms, periods and subgroup family are true of the group; soundness is checked by the reviews, not
by Lean.

Two further points about what the statements rely on:
* The MX theorems themselves (not only their hypothesis `hW`) are stated with hand-coded quasi-periods (`etaLem`, `etaR`, `etaRho`)
  and the coordinate convention `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))` in `LogNat`. `ζ` is the standard series
  (`CM4E.Ext.Weierstrass.zeta`, with `ζ' = −℘` proved). The quasi-period values were checked numerically against this
  `ζ` in `reviews/REFEREE_HYP_MX.md`.
* `HyperplaneKappa gmE` also covers configurations with `κ = 5`, outside the range `2N ≥ d₁ + 2d₀ + κ` of Lemma U. By
  the argument of the paper-vs-Lean review (2026-10-30), `V` is then forced to be rational, so the conclusion holds
  trivially; this argument is not formalised. The same happens for `gmMG` when `κ = 3n − 1` (every such `V` contains
  a rational toric line; `reviews/REFEREE_HYP_GEN.md`). For `gmQ`, `gmMGn` and `gmXG` Lemma U's range covers every
  configuration.

All Lean proofs follow the paper's §5d derivations (paper Remarks 15, 20, 26), which apply the paper's
Theorem 11 (W88 Thm 1.1 with (5.4)).

**The single point of failure** is the κ-term in W88 Thm 4.1 / §5d. Without it, the instance used in `MainQi.main` would
need `6 > 6`, the MG♮ instances `3n > 3n + 2`, and the MX instances `3n > 4n + 2`, all false. An expert check of
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
| Theorem 1(b) (4E at `cΩ/π`) | `Gen.fourExpAt_MG`, `Final.fourExpAt_varpi_div_pi_all`, `Final.fourExpAt_omegaRho_div_pi_all` (also `MainQi`, `Final.fourExpAt_Qi` for `c ∈ ℚ(i)`) | ✔ for `Ω ∈ {ϖ, Ω_ρ}` and every algebraic `c ≠ 0` (and any CM lattice `ωℤ[α]` given as a `CMLattice`). Missing: other CM curves (`CMLattice` instances, i.e. `η₀`, for their lattices) |
| Example `2^{ϖ/π}, 3^{ϖ/π}` | `TwoThree.two_three`, `Final.two_three` | ✔ |
| Theorem 1(a) (4E at `cΩ`; `2^ϖ, 3^ϖ`) | `Gen.fourExpAt_MGn`, `Final.fourExpAt_varpi_all`, `Final.fourExpAt_omegaRho_all`, `Final.two_three_varpi`, `Final.two_three_omegaRho` (also `MainNat` for `c ∈ ℚ(i)`) | ✔ for `Ω ∈ {ϖ, Ω_ρ}` and every algebraic `c ≠ 0`. Missing: other CM curves |
| Theorem MG, Cor. MG2 (`K`-version, `dim_K S_K ≤ 2`) | — | ✗ (only the `FourExpAt` form; the dimension statement needs `K`-linear algebra on `K𝓛` and Baker's theorem for `K`-independence) |
| Cor. MG1, Cor. MG3 | — | ✗ (need the `K`-version of MG; MG3 needs Baker) |
| Theorem MG♮ (`K`-version), Cor. MG♮2 | `Gen.fourExpAt_MGn` | ◐ Cor. MG♮2 ✔ (as above); the `K`-dimension statement ✗ |
| Affine MG; general form, elliptic 4E | — | ✗ (proof sketches in the paper) |
| Theorem M, Cor. M1–Mη | — | ✗ |
| Theorem MX, Prop. D, Cor. MX1 | `Gen.mx_K`, `Gen.mx_full`, `Gen.mx1`, `Final.mx_K`, `Final.mx`, `Final.mx1` | ✔ for every `β ∈ ℚ̄ˣ`: Prop. D for `v ∈ Ψ(Λ(G))` from W88 alone; Theorem MX and Cor. MX1 with the named inputs `WuestholzMX`, `MasserCM`, `LaurentZeta` |
| Cor. Γ | — | it is the hypothesis `hΓ` (Wüstholz); not derived |
| Theorem MX′, degree-two corollary | — | ✗ |
| Lemma K | — | ✗ |
| Case tables of MG, MG♮, MX (Thm 4.1 route) | `CaseCheck.*` | ✔ arithmetic layer only; not used by the theorems above, which take the §5d route |
| Step 1 of Prop. D (algebra) | `LemmaL.*` | ✔; not used by the MX theorems |
| Lemma U (Appendix A) | — | not a separate hypothesis: part of the proof of W88 Thm 4.1, which `hW` assumes |

## 6. Vendored code

`CM4E/Ext/` (32 files, 6,518 lines) is a renamed verbatim copy of the needed part of the author's sibling project
`lean_lsg`: Weierstrass `ζ`/`σ`, Legendre's relation, `g₂(ϖℤ[i]) = 4`, and Schneider's theorem. Details and source
commit: [`CM4E/Ext/PROVENANCE.md`](CM4E/Ext/PROVENANCE.md). The project depends on nothing but Mathlib.

## 7. Reviews and provenance

Written by AI models (Claude, Anthropic) under the direction of the author. All review so far is by AI referees: the
fidelity reports in [`reviews/`](reviews/) (scripts and outputs in `reviews/checks/`) and the paper's own referee
reports. No human expert has reviewed the definitions or proofs.
