# TRUST: what the Lean certificate proves, and what it assumes

Project: `lean_mstar` (Lean 4.35, Mathlib v4.35.0; library `CM4E`). Paper: *Four exponentials at periods of CM abelian
varieties* (draft; snapshot in [`paper/`](paper/)). It merges the earlier drafts [I] (CM elliptic curves) and [II] (CM
abelian varieties); results are cited by the merged numbering (the map is in `paper/README.md`). W88 below is M. Waldschmidt,
*On the transcendence methods of Gel'fond and Schneider in several variables*, in: A. Baker (ed.), New Advances in
Transcendence Theory (Durham 1986), Cambridge Univ. Press, 1988, pp. 375–398.

## 1. Axioms

Every declaration depends only on Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`
(`lake env lean Axioms.lean`, which also covers the imported `lean_lsg` declarations). There is no `sorry`, no `axiom`
declaration and no `native_decide`, in `CM4E/` or in the vendored `CM4E/Ext/`.

## 1a. What is unconditional, and what each result is conditional on

The sibling project `lean_lsg` (a Lake path dependency, `../lean_lsg`; see §6) proves W88 Thm 4.1 under (NR) for
`G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` (`LSG.W88.theorem41Abelian`) and, from it, the §5d statement for `G_m^{d₁} × E`, which
is verbatim our `Thm11Kappa` (`LSG.W88.thm11Kappa`), and the §5d statement for the standard model of
`G_a^{d₀} × G_m^{d₁} × E^r`, one curve repeated, for every period pair with algebraic invariants, which is verbatim our
`Bridge.HypStdCMAt` (`LSG.W88.hypStdCMAt`, `lean_lsg` commit 2d9a9b4); standard axioms only. With the proved bridges of
`CM4E/Bridge/` (`HypStdCMAt L 0 → Gen.Thm11KappaMG L`, `HypStdCMAt L 2 → Gen.Thm11KappaSMG L`,
`HypStdCMAt L 1 → Gen.Thm11KappaM L`, `HypStdCMAt L 0 → Gen.Thm11KappaMGK L` for CM lattices with integral `α`, via the
isomorphism `A'' = E^n/B_{ker ψ} ≅ E^{n/2}`; the last two also use the arithmetic of elliptic logarithms,
`CM4E/Bridge/ELog.lean`: the addition and duplication formulas make `𝓛_E` a group, and `℘(iz) = −℘(z)`,
`℘(ρz) = ρ℘(z)` give complex multiplication on it for `ϖℤ[i]`, `Ω_ρℤ[ρ]`), and with `lean_lsg`'s Theorem 4.1 for vector
extensions onto `M` (commit 0ed4c24; `CM4E/Bridge/Vec.lean`, `CM4E/Bridge/MXG.lean`, verbatim copies repackaged by
`adaptL` and the basis structure) the hypotheses `hW` fall into two tiers:

| tier | hypotheses `hW` | results |
|---|---|---|
| **unconditional** (W88 proved in `lean_lsg`) | `Thm11Kappa L d₁`; `Gen.Thm11KappaMG L`, `Gen.Thm11KappaSMG L` for every CM lattice with integral `α` and algebraic invariants; `Gen.Thm11KappaM L`, `Gen.Thm11KappaMGK L` for those on which `α` acts on `𝓛_E` (`Bridge.CMMulLogE`; proved for `latI`, `latRho`); `Gen.Thm11KappaMGn L`, `Gen.Thm11KappaMGnK L` for every CM lattice (premised on `KappaOneZero L`), `Gen.Thm11KappaMXG`, `MainNat.Thm11KappaNat`, `Gen.Thm11KappaSMGn L`, `Gen.Thm11KappaMXP` (`Bridge.*_uncond`) | `Unconditional.fourExpAt_Qi`, `Unconditional.two_three` (`2^{ϖ/π}, 3^{ϖ/π}` not both algebraic); **`Unconditional.fourExpAt_varpi_div_pi_all` (Theorem 1.1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`)**; `Unconditional.fourExpAt_omegaRho_div_pi_all` (Theorem 1.1(b) for `Ω_ρ`; only `hg₃'`); **`Unconditional.thmM_varpi` (Theorem M for `Ω = cϖ`)**, `Unconditional.thmM_omegaRho` (only `hg₃'`); `Unconditional.m1_varpi` (M1), `Unconditional.m3_varpi` (M3), `Unconditional.m3'_varpi` (M3′; only `Gen.HermiteLindemann`), `Unconditional.thmM_varpi_k`, `Unconditional.meta_varpi` (only `Gen.MasserCM`); `Unconditional.mg_K_varpi` (the `K`-form of Theorem MG); **`Unconditional.two_three_varpi` (`2^ϖ, 3^ϖ` not both algebraic), `Unconditional.fourExpAt_varpi_all` (Theorem 1.1(a) for `Ω = ϖ`, every algebraic `c ≠ 0`)**, `Unconditional.fourExpAt_varpi` (`c ∈ ℚ(i)ˣ`), `Unconditional.fourExpAt_omegaRho_all`, `Unconditional.two_three_omegaRho` (only `hg₃'`); `Unconditional.mgn_K_varpi` (the `K`-form of Theorem MG♮); `Unconditional.mx_K`, `Unconditional.mx`, `Unconditional.mx1`, `Unconditional.deg2_ii` (Theorem MX, Cor. MX1, deg2 (ii); only `hg₃'`, `hΓ` and their named inputs); **`Unconditional.thmS_varpi` (Theorem S, Thm. 1.5; only `Gen.NotLtilde`)**, `Unconditional.thmS_omegaRho` (also `hg₃'`); `Unconditional.mxP_K`, `Unconditional.deg2_i` (Proposition D′ / Theorem MX′, deg2 (i); only `hg₃'`, `hΓ` resp. `Gen.WuestholzSix`; `Ω_ρ/ϖ ∉ ℚ̄` is proved, `Unconditional.transcendental_omegaRho_div_varpi`); **`Unconditional.thmSE_varpi_omegaRho` (Theorem 4.12(1), SE, for `E_i`, `E_ρ`; only `hg₃'`)**, `Bridge.thmSE_of_nonIsog` / `Bridge.SEPaper.thmSE_paper` (SE for any two CM lattices with `k ≠ k'` on which CM acts on `𝓛_E`; no form of W88 assumed, via `LSG.W88.hypStd_of_pair`); `Unconditional.mg1_varpi_abc` (Cor. MG1; only `Gen.NotLtilde`); `Unconditional.mg3_varpi` (Cor. MG3; only `Gen.Baker3`); Theorems MG and SMG (compose `Gen.fourExpAt_MG`, `Gen.smg_false` with the bridges) |
| conditional on W88 for CM abelian varieties of dimension 2, 3 (and their vector extensions) | `AbVar.Thm11KappaX7`, `AbVar.Thm11KappaA`, `AbVar.Thm11KappaAn`, `AbVar.Thm11KappaAK`, `AbVar.Thm11KappaAnK` | Theorems 6.6 (X7), 3.7 (MG-A), 3.9 (MG♮-A), 1.2 (Theorem A), Cor. A2, Cor. X7 |

Named classical inputs (§3) are additional hypotheses in every tier where they appear. In the unconditional tier they
are exactly the following; everything else (W88 included) is proved.

| unconditional result | its only non-W88 inputs | literature |
|---|---|---|
| Cor. MG1 (`Unconditional.mg1_varpi_abc`) | `Gen.NotLtilde Gen.latI`: `ϖ ∉ 𝓛̃` and `η(ϖ) ∉ 𝓛̃`, `𝓛̃ = ℚ̄ + ℚ̄𝓛` | Wüstholz's analytic subgroup theorem: G. Wüstholz, *Algebraische Punkte auf analytischen Untergruppen algebraischer Gruppen*, Ann. of Math. 129 (1989), 501–517 (applied on `G_a × G_m^r × E` and `G_a × G_m^r × E^♮`, Lemma 4.1); A. Baker, G. Wüstholz, *Logarithmic Forms and Diophantine Geometry*, CUP 2007, Ch. 6 |
| Cor. MG3 (`Unconditional.mg3_varpi`) | `Gen.Baker3`: three `ℚ`-independent logarithms of algebraic numbers are `ℚ̄`-independent | A. Baker, *Linear forms in the logarithms of algebraic numbers I*, Mathematika 13 (1966), 204–216; Baker–Wüstholz 2007, Ch. 2 |
| (M3′) (`Unconditional.m3'_varpi`) | `Gen.HermiteLindemann` | Lindemann 1882 (Weierstrass 1885); not in Mathlib |
| Theorem M with `s ∈ ℚ(i)`, (Mη); Theorem MX, MX1 | `Gen.MasserCM` | D. Masser, *Elliptic Functions and Transcendence*, LNM 437, Springer 1975 |
| Theorem MX, MX1 | `Gen.WuestholzMX` (and `hΓ`: `ϖΩ_ρ/π ∉ ℚ̄`), MX1 also `Gen.LaurentZeta`; deg2 (ii): `Gen.WuestholzSix` | Wüstholz 1989 (analytic subgroup theorem); Laurent's theorem on `ζ` values (see §3) |
| the `Ω_ρ` statements | `hg₃'`: `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄` (`g₂ = 0` is proved, `MX.g₂_equianharmonic`) | classical (`g₃ = 4` for `Ω_ρ = Γ(1/3)³/(2^{4/3}π)`; Chowla–Selberg); see §3 for why it is not formalised |

## 2. The final theorems

`CM4E/Final.lean` states the results with every input proved except W88 (and, where listed, named classical inputs):

| theorem | statement | assumes |
|---|---|---|
| `Final.fourExpAt_varpi_all` | `FourExpAt (cϖ)` for every algebraic `c ≠ 0` (Theorem 1.1(a), `Ω = ϖ`) | `hW : Gen.Thm11KappaMGn Gen.latI` |
| `Final.fourExpAt_varpi_div_pi_all` | `FourExpAt (cϖ/π)` for every algebraic `c ≠ 0` (Theorem 1.1(b), `Ω = ϖ`) | `hW : Gen.Thm11KappaMG Gen.latI` |
| `Final.fourExpAt_omegaRho_all` | `FourExpAt (cΩ_ρ)` for every algebraic `c ≠ 0` | `hW : Gen.Thm11KappaMGn Gen.latRho`, `hg₃'` |
| `Final.fourExpAt_omegaRho_div_pi_all` | `FourExpAt (cΩ_ρ/π)` for every algebraic `c ≠ 0` | `hW : Gen.Thm11KappaMG Gen.latRho`, `hg₃'` |
| `Final.two_three_varpi`, `Final.two_three`, `Final.two_three_omegaRho` | `2^t, 3^t` not both algebraic for `t = ϖ`, `ϖ/π`, `Ω_ρ` | `hW : MainNat.Thm11KappaNat`, resp. `Thm11Kappa lemniscatic 4`, resp. `Gen.Thm11KappaMGn Gen.latRho` with `hg₃'` |
| `Final.fourExpAt_varpi`, `Final.fourExpAt_Qi` | the same for `c ∈ ℚ(i)ˣ`, from one fixed group (`K = ℚ(i, √2)`, resp. `ℚ(i)`) | `hW : MainNat.Thm11KappaNat`, resp. `Thm11Kappa lemniscatic 4` |
| `Final.mx_K` | Theorem MX, `K`-form: `z(X) + z(Y) + a ∈ ℚ̄ϖ + ℚ̄Ω_ρ`, every `β ∈ ℚ̄ˣ` | `hW : Gen.Thm11KappaMXG`, `hg₃'`, `hΓ`, `hM` |
| `Final.mx` | Theorem MX: `a = 0`, `z(X) ∈ ℚ(i)ϖ`, `z(Y) ∈ ℚ(ρ)Ω_ρ`, every `β ∈ ℚ̄ˣ` | the above (with `hM` derived) and `WuestholzMX`, `MasserCM` |
| `Final.mx1` | Corollary MX1 | the above and `LaurentZeta` |
| `Final.thmS_varpi`, `Final.thmS_omegaRho` | Theorem S, Thm. 1.5: for `t ∈ ℚ̄ˣΩ ∪ ℚ̄ˣ/Ω ∪ ℚ̄ˣΩ/π ∪ ℚ̄ˣπ/Ω` and `ℚ̄`-independent `y₁, y₂`, not all of `y₁, y₂, ty₁, ty₂` lie in `𝓛̃ = ℚ̄ + ℚ̄𝓛` (`Ω = ϖ`, `Ω_ρ`) | `hW : Gen.Thm11KappaSMG L`, `Gen.Thm11KappaSMGn L`, `Gen.NotLtilde L` (and `hg₃'` for `Ω_ρ`) |
| `Final.mg1_varpi` | Corollary MG1: one of `e^{π²}`, `e^{πϖ}`, `e^{π²/ϖ}` is transcendental | `hW : Gen.Thm11KappaSMG Gen.latI`, `Gen.NotLtilde Gen.latI` (`π` transcendental is proved: `Gen.transcendental_pi`, from the vendored Schneider–Lang criterion) |
| `Final.mg3_varpi` | Corollary MG3 (`α^{ϖ/π}` transcendental when `e^{π²}`, `e^{cπϖ}` are algebraic) | `hW : Gen.Thm11KappaSMG Gen.latI`, `Gen.Baker3` |
| `Final.mg_K_varpi` | Theorem MG, `K`-form (`Ω = ϖ`): for `s = cϖ/π` and `K = span_ℚ θ ∋ i, c`, no `x₁, x₂ ∈ K𝓛` with `sx_j ∈ K𝓛 + K𝓛_E` and `2πi, x₁, x₂` `K`-independent (`dim_K S_K ≤ 2`) | `hW : Gen.Thm11KappaMGK Gen.latI` |
| `Final.mgn_K_varpi` | Theorem MG♮, `K`-form (`Ω = ϖ`): the same with `s = 1/(cϖ)`, `sx_j ∈ K𝓛 + K·(fibre values)`, `[K : ℚ] ≥ 4` | `hW : Gen.Thm11KappaMGnK Gen.latI` |
| `Final.thmM_varpi`, `Final.thmM_omegaRho` | Theorem M: `iπu = Ωℓ` with `u ∈ ℚ̄𝓛_E`, `ℓ ∈ 𝓛̃`, `Ω = cϖ` resp. `cΩ_ρ` (`c ∈ ℚ̄ˣ`) forces `u = sΩ`, `ℓ = s·iπ`, `s ∈ ℚ̄` | `hW : Gen.Thm11KappaM L` (and `hg₃'` for `Ω_ρ`) |
| `Final.thmM_varpi_k` | Theorem M on `E_i` with `s ∈ ℚ(i)` for `u ∈ 𝓛_E` | `hW : Gen.Thm11KappaM Gen.latI`, `Gen.MasserCM` |
| `Final.m1_varpi`, `Final.m3_varpi` | (M1) `℘(cϖ/π) ∉ ℚ̄`; (M3) if `e^{π²} ∈ ℚ̄` then `℘(cπϖ) ∉ ℚ̄` (`c ∈ ℚ̄ˣ`) | `hW : Gen.Thm11KappaM Gen.latI` |
| `Final.m3'_varpi` | (M3′) for `e^z ∈ ℚ̄ ∖ {0, 1}`, one of `e^{iπz}`, `℘(ϖz)` is transcendental | `hW : Gen.Thm11KappaM Gen.latI`, `Gen.HermiteLindemann` |
| `Final.meta_varpi` | (Mη) `η(ϖ)u ∉ 𝓛̃` for `u ∈ 𝓛_{E_i} ∖ ℚ(i)ϖ` | `hW : Gen.Thm11KappaM Gen.latI`, `Gen.MasserCM` |
| `Final.mxP_K` | Proposition D′ (Theorem MX′, `K`-form): `(z(X) + w(Y) + a)·βΩ_ρ = (w(X) + z(Y) + c)·ϖ` forces `z(X) + w(Y) + a ∈ ℚ̄ϖ + ℚ̄η_ρ`, every `β ∈ ℚ̄ˣ` | `hW : Gen.Thm11KappaMXP`, `hg₃'`, `hΓ`, `hM` |
| `Final.deg2_i` | `π, ϖ, Ω_ρ, ϖΩ_ρ` are `ℚ̄`-linearly independent | `hW : Gen.Thm11KappaMXP`, `hg₃'`, `hΓ`, `Gen.WuestholzSix` |
| `Final.deg2_ii` | `1, ϖ, Ω_ρ, ϖΩ_ρ/π` are `ℚ̄`-linearly independent | `hW : Gen.Thm11KappaMXG`, `hg₃'`, `hΓ`, `Gen.WuestholzSix` |

`FourExpAt t` (`CM4E/Defs.lean`): for `ℚ`-linearly independent `a, b` with `e^a, e^b` algebraic, `e^{ta}` and `e^{tb}`
are not both algebraic. The determinations of `α^t, β^t` are thus tied to the chosen logarithms.

The general-`c` theorems use, for each `c`, a number field `K ∋ c` with an adapted basis (`Gen.exists_adapted_basis`,
proved) and the hypothesis for the group built from that `K`; this is why their `hW` quantifies over all adapted bases.
The `ℚ(i)` versions need W88 for one fixed group only, which is a weaker assumption.

Inputs that are **proved** (in `CM4E/Ext/` and `CM4E/Lattice.lean`) and discharged in `Final.lean`:
* `g₂(ϖℤ[i])` is algebraic (`Final.hg₂`; `g₂ = 4` from the Γ-formula for `ϖ`); `g₃(ϖℤ[i]) = 0` (`g₃_lemniscatic`);
* `ϖ/π ∉ ℚ` (`Final.hS`), `ϖ` and `ϖ/π` transcendental (`Final.hT`): Schneider's theorem; for `Ω_ρ`, Schneider's
  theorem is applied with `hg₃'`;
* in Corollary MX1, `u + a ≠ 0` (Schneider: `℘` is transcendental at nonzero algebraic non-periods).

## 3. What is assumed: explicit hypotheses, never global axioms

| name | content | where stated | why it is believed |
|---|---|---|---|
| `hW : Thm11Kappa lemniscatic 4` | W88 Thm 1.1 with (1.2) replaced by (5.4) (§5d, p. 394) for `G = G_m⁴ × E`, `E` the curve of `ϖℤ[i]` | `CM4E/Waldschmidt.lean` (model `gmE`) | Published. Its proof rests on W88 Thm 4.1, whose auxiliary-function step for `W ≠ 0`, `κ > 0` is completed by Lemma U (paper, Appendix A). Fidelity: [`reviews/REFEREE_HYP.md`](reviews/REFEREE_HYP.md) (CORRECT). |
| `hW : Thm11KappaNat` | the same theorem for `G″ = G_m⁸ × Q″`, `Q″ = (E_i^♮)⁴/U` (`K = ℚ(i, √2)`, `n = 4`) | `CM4E/MainNat.lean` (model `gmQ`) | Same source; hand-written model. Fidelity: [`reviews/REFEREE_HYP_NAT.md`](reviews/REFEREE_HYP_NAT.md) (CORRECT). |
| `hW : Gen.Thm11KappaMGn L` | the same theorem for `G_m^{2n} × Q″`, `Q″ = (E^♮)^n/U`, for every number field `K` with an adapted basis; `L` is a CM lattice (`latI`, `latRho`); premised on `Gen.KappaOneZero L` (`κ₁ = 0`, needed by `lean_lsg`'s vector-extension design; proved for both instances, `Gen.kappaOneZero_latI`, `Gen.kappaOneZero_latRho`, so no headline statement changes) | `CM4E/Gen/MGn.lean` (model `gmMGn`, on the frame `gmF` of `CM4E/Gen/Frame.lean`) | Same source; hand-written model (tangent space `ℂ^n/ℂ·ker φ × ℂ`). Fidelity: [`reviews/REFEREE_HYP_GEN.md`](reviews/REFEREE_HYP_GEN.md) (CORRECT; it also found the sign condition `Im α > 0`, now required). |
| `hW : Gen.Thm11KappaMG L` | the same theorem for `G_m^{2n} × A″`, `A″ = E^n/B_{ker ψ}`, every adapted `K` | `CM4E/Gen/MG.lean` (model `gmMG`) | Same; fidelity in `reviews/REFEREE_HYP_GEN.md` (CORRECT). |
| `hW : Gen.Thm11KappaMXG` | the same theorem for `G″ = G_a × G_ℓ = (E_i^♮ × E_ρ^♮ × G_a²)^n/U`, every adapted `K ∋ i` | `CM4E/Gen/MXGen.lean` (model `gmXG`) | Same; the model reviewed in [`reviews/REFEREE_HYP_MX.md`](reviews/REFEREE_HYP_MX.md) for `K = ℚ(i, √3)`, with general `K`; review of the general form: `reviews/REFEREE_HYP_MXG.md`. |
| `hW : Gen.Thm11KappaSMG L`, `Gen.Thm11KappaSMGn L` | the same theorem for `G_a² × G_m^{2n} × A″` and `G_a × G_m^{2n} × Q″` (Theorem 4.2, SMG and SMG♮), every adapted `K`; `SMGn` is premised on `Gen.KappaOneZero L` (its periods use `η₀ = η(ω)`, true iff `κ₁ = 0`; proved for `latI`, `latRho`, so Theorem S is unchanged) | `CM4E/Gen/SMG.lean` (models `gmSMG`, `gmSMGn`, on the frame `gmF2` of `CM4E/Gen/Frame2.lean`) | Same source; review: [`reviews/REFEREE_HYP_SMG.md`](reviews/REFEREE_HYP_SMG.md) (CORRECT). The paper proves SMG via W88 Thm 4.1; Lean uses the §5d route with the uniform exclusion "no nonzero algebraic subgroup inside `ker Ψ″`". |
| `hW : Gen.Thm11KappaMXP` | the same theorem for the twisted group of Theorem MX′, `G″ = G^n/U'`, `G = E_i^♮ × E_ρ^♮ × G_a²` (the push-out of `(E_i^n × E_ρ^n)^♮` along `θᵀ`, an extension of `E_i^n × E_ρ^n` by `G_a²`), every adapted `K ∋ i` with `r ≥ 3` | `CM4E/Gen/MXP.lean` (model `gmXP`) | Same source; review: [`reviews/REFEREE_HYP_MXP.md`](reviews/REFEREE_HYP_MXP.md) (CORRECT). |
| `hW : Gen.Thm11KappaM L` | the same theorem for `A″ × G_m^n × G_a` (Theorem M; `G_a` a direct factor, so `d₀ = 1`), every adapted `K` | `CM4E/Gen/ThmM.lean` (model `gmM`, on the frame `gmFM` of `CM4E/Gen/FrameM.lean`) | Same source; review: [`reviews/REFEREE_HYP_M.md`](reviews/REFEREE_HYP_M.md) (CORRECT). The paper's first proof uses Roy–Waldschmidt; Lean writes out its reduction and applies W88 §5d to a hyperplane. |
| `hW : Gen.Thm11KappaMGK L`, `Gen.Thm11KappaMGnK L` | the same theorem for `G_m^{2n} × A″` and `G_m^{2n} × Q″` with elliptic logarithms (resp. logarithms of `(E^♮)^n`) among the data; `MGnK` is premised on `Gen.KappaOneZero L` (`ζ(αz) = ᾱζ(z)`, i.e. `κ₁ = 0`; proved for `ϖℤ[i]` and `Ω_ρℤ[ρ]` as `Gen.kappaOneZero_latI`, `Gen.kappaOneZero_latRho`) | `CM4E/Gen/MGK.lean`, `CM4E/Gen/MGnK.lean` (models `gmMGK`, `gmMGnK`, on `gmF2`) | Same source; review: [`reviews/REFEREE_HYP_MGK.md`](reviews/REFEREE_HYP_MGK.md) (CORRECT; the `κ₁ = 0` premise was added after it). |
| `hg₃'` | `g₃` of `Ω_ρℤ[ρ]` is algebraic (`g₂ = 0` is proved: `MX.g₂_equianharmonic`, by `(ρl)⁻⁴ = ρ⁻¹l⁻⁴`; `Final.hg₂'`) | arguments | True: `g₃ = 4` for `Ω_ρ = Γ(1/3)³/(2^{4/3}π)` (40-digit checks in `reviews/`). Not proved in Lean: it is the evaluation of the real period, `Ω_ρ/2 = g^{-1/2} ∫₀¹ dt/√(1 − t⁶)` with `g³ = g₃/4`, plus `∫₀¹ dt/√(1 − t⁶) = B(1/6, 1/2)/6` and Legendre duplication at `1/6`; the analogous `g₂ = 4` for `ϖℤ[i]` took ~600 lines (`CM4E/Ext/LemniscateIndep/`), and the square-lattice steps (`℘(iz) = −℘(z)`, the sign of `e`) would have to be redone for the hexagonal lattice. |
| `hΓ` | `ϖΩ_ρ/π ∉ ℚ̄` (Corollary Γ) | argument of the MX theorems | Wüstholz's analytic subgroup theorem (1989): a period of `E_i` and a quasi-period of `E_ρ` are `ℚ̄`-linearly independent. |
| `hM` | `Ω_ρ/ϖ ∉ ℚ̄` | argument of `Final.mx_K` | Wüstholz 1989; derived from `WuestholzMX` in `Gen.mx_full`. |
| `Gen.WuestholzMX` | a `ℚ̄`-linear relation `z_X + z_Y + a = xϖ + x'Ω_ρ` between elliptic logarithms of `E_i`, `E_ρ` forces `a = 0`, `z_X = xϖ`, `z_Y = x'Ω_ρ` | `CM4E/Gen/MXGen.lean` | Wüstholz 1989, applied to `E_i² × E_ρ² × G_a` (argument in the docstring). |
| `Gen.MasserCM` | an elliptic logarithm that is an algebraic multiple `xω` of the period has `x` in the CM field | `CM4E/Gen/MXGen.lean` | Masser 1975; also Wüstholz on `E²`. |
| `Gen.LaurentZeta` | `ζ(u)` is transcendental for non-torsion `u` on `E_i` with `℘(u), ℘'(u)` algebraic | `CM4E/Gen/MXGen.lean` | Laurent 1980 (`1, u, ζ(u)` are `ℚ̄`-independent). |
| `Gen.NotLtilde L` | `ω ∉ 𝓛̃` and `η₀ ∉ 𝓛̃` | `CM4E/Gen/SMG.lean` | Lemma 4.1 (Wüstholz's analytic subgroup theorem). |
| `Gen.WuestholzSix` | `1, π, ϖ, η_i, Ω_ρ, η_ρ` are `ℚ̄`-linearly independent | `CM4E/Gen/Deg2.lean` | Wüstholz 1989 on `E_i^♮ × E_ρ^♮ × G_m × G_a` (subgroup argument in `reviews/REFEREE_HYP_MXP.md`). It implies `hΓ`, so `hΓ` is redundant in `deg2_i`, `deg2_ii`. |
| `Gen.HermiteLindemann` | `e^z` is transcendental for algebraic `z ≠ 0` | `CM4E/Gen/ThmMCor.lean` | Hermite–Lindemann (1882). Not in Mathlib; it could be derived from the vendored Schneider–Lang criterion as `transcendental_pi` is. |
| `Gen.Baker3` | three `ℚ`-independent logarithms of algebraic numbers are `ℚ̄`-independent | `CM4E/Gen/MG13.lean` | Baker 1966. |

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
  a rational toric line; `reviews/REFEREE_HYP_GEN.md`). For `gmMGK` the only out-of-range value is again `κ = 3n − 1`, with the same trivial conclusion
  (`reviews/REFEREE_HYP_MGK.md`). For `gmM` the out-of-range values `κ = 2n − 1, 2n` again force
  a rational toric line into `V` (`reviews/REFEREE_HYP_M.md`). For `gmQ`, `gmMGn`, `gmMGnK`, `gmXG` and `gmXP` Lemma U's range
  covers every configuration.

All Lean proofs follow the paper's §5d derivations (paper Remarks 3.3, 3.6, 5.2), which apply the paper's
Theorem 2.5 (W88 Thm 1.1 with (5.4)).

**The single point of failure** is the κ-term in W88 Thm 4.1 / §5d. Without it, the instance used in `MainQi.main` would
need `6 > 6`, the MG♮ instances `3n > 3n + 2`, the MX instances `3n > 4n + 2`, the MX′ instances `3n > 4n + 4` and the
Theorem M instances `n + 1 > 2n`, all false. An expert check of
W88 §§6–7 together with Lemma U is the most valuable outside review. It should cover the regimes used here: `W ≠ 0`,
`κ > 0`, a non-semiabelian `G₂` (`MainNat`, `MX`), and `d₀ > 0` (`MX`, SMG♮ and Theorem M with `d₀ = 1`, SMG with `d₀ = 2`, which rely on the Gel'fond part of W88's
proof; the paper's Appendix A notes that the case `δ = τ` needs `b > 1` there). Note also that W88's §5d proof
applies Thm 4.1 twice: to `G` itself, and again to an auxiliary subgroup given by W88 Lemma 5.1. Lemma U's condition
has been checked only for the first application, so every `hW` rests on W88 §5d as published (paper, §2.4, after
Theorem 2.5).

## 4. What to read to trust a statement

* `CM4E/Defs.lean`: the elementary definitions (`FourExpAt`, `logAlg`, `varpi`, `omegaRho`).
* `CM4E/Waldschmidt.lean`: the hypothesis form `HyperplaneKappa` and the model `gmE`.
* `CM4E/Lattice.lean`: the period pair `(ϖ, iϖ)` (Mathlib's `PeriodPair`) with `ϖ` given by the Γ-formula.
* `CM4E/Final.lean`: the final statements.

## 5. Coverage: every result of the paper

✔ = proved in Lean, conditionally on §3 · ◐ = partial · ✗ = not formalised.

| paper result | Lean | status / what is missing |
|---|---|---|
| Theorem 1.1(b) (4E at `cΩ/π`) | `Gen.fourExpAt_MG`, `Final.fourExpAt_varpi_div_pi_all`, `Final.fourExpAt_omegaRho_div_pi_all` (also `MainQi`, `Final.fourExpAt_Qi` for `c ∈ ℚ(i)`) | ✔ for `Ω ∈ {ϖ, Ω_ρ}` and every algebraic `c ≠ 0` (and any CM lattice `ωℤ[α]` given as a `CMLattice`). Missing: other CM curves (`CMLattice` instances, i.e. `η₀`, for their lattices) |
| Example `2^{ϖ/π}, 3^{ϖ/π}` | `TwoThree.two_three`, `Final.two_three` | ✔ |
| Theorem 1.1(a) (4E at `cΩ`; `2^ϖ, 3^ϖ`) | `Gen.fourExpAt_MGn`, `Final.fourExpAt_varpi_all`, `Final.fourExpAt_omegaRho_all`, `Final.two_three_varpi`, `Final.two_three_omegaRho` (also `MainNat` for `c ∈ ℚ(i)`) | ✔ for `Ω ∈ {ϖ, Ω_ρ}` and every algebraic `c ≠ 0`. Missing: other CM curves |
| Theorem MG, Cor. MG2 (`K`-version, `dim_K S_K ≤ 2`) | `Gen.mg_K`, `Final.mg_K_varpi` | ✔ for `K ∋ i, c` (any `CMLattice`); the paper's reduction from arbitrary `K ⊇ k` to this case (Baker's theorem) is not formalised |
| Cor. MG1, Cor. MG3 | `Gen.mg1`, `Gen.mg3`, `Final.mg1_varpi`, `Final.mg3_varpi` | ✔ for any `CMLattice` (via Theorem SMG, Thm. 4.2, whose data may lie in `𝓛̃`); MG1 uses `NotLtilde` (and the proved transcendence of `π`), MG3 uses Baker |
| Theorem MG♮ (`K`-version), Cor. MG♮2 | `Gen.mgn_K`, `Final.mgn_K_varpi`, `Gen.fourExpAt_MGn` | ✔ for `K ∋ c`, `[K : ℚ] ≥ 4`, lattices with `κ₁ = 0` (premise `KappaOneZero`, proved for `ϖℤ[i]` and `Ω_ρℤ[ρ]`; `s = 1/(cω) ∈ ℚ̄ˣη*/π`); Baker reduction not formalised |
| Affine MG; general form, elliptic 4E | — | ✗ (proof sketches in the paper) |
| Theorem 4.12(1) (SE: strong elliptic 4E at `cΩ'/Ω`) | `AbVar.thmSE`, `Bridge.thmSE_of_nonIsog`, `Bridge.SEPaper.thmSE_paper`, `Unconditional.thmSE_varpi_omegaRho` | ✔ for any two CM lattices with `k ≠ k'` (assuming `Bridge.CMMulLogE`, proved for `ϖℤ[i]`, `Ω_ρℤ[ρ]`); Cor. 4.13 (SE4) and SE♮ not formalised; model `gmSE` reviewed in [`reviews/REFEREE_HYP_SE.md`](reviews/REFEREE_HYP_SE.md) (no FATAL/MAJOR; the Lean theorems assume no form of W88) |
| Theorem 4.12(3) (SE₀: strong elliptic 4E at `cη/Ω`, e.g. `℘_i(π/ϖ²), ℘_i(πu/ϖ²)`) | `AbVar.thmSE0`, `Bridge.thmSE0_of_cm`, `Bridge.thmSE0_paper`, `Bridge.thmSE0_varpi` (no hypotheses), `Bridge.transcendental_pi_div_varpi_sq` | ✔ for CM lattices with `κ₁ = 0` (i.e. `j ∈ {0, 1728}`) and `CMMulLogE`; the `ϖ` instance is unconditional (via `lean_lsg`'s `hypStdVecCM`); `Bridge.thmSE0_varpi_Ltilde` is the Cor. 4.13 case `t = cπ/ϖ²` with the extra hypothesis `ϖ ∉ ℚ̄u₁ + ℚ̄u₂`; review [`reviews/REFEREE_HYP_SE0.md`](reviews/REFEREE_HYP_SE0.md) (no FATAL/MAJOR) |
| Theorem M | `Gen.thmM`, `Gen.thmM_I_k`, `Final.thmM_varpi`, `Final.thmM_omegaRho`, `Final.thmM_varpi_k` | ✔ (first proof, `K`-structure explicit, W88 §5d instead of Roy–Waldschmidt); `s ∈ k` on `E_i` via `MasserCM` (on `E_ρ` not written out) |
| Cor. M (M1), (M3), (M3′), (Mη) | `Gen.m1`, `Gen.m3`, `Gen.m3'`, `Gen.meta_I`, `Final.m1_varpi`, `Final.m3_varpi`, `Final.m3'_varpi`, `Final.meta_varpi` | ✔ (M1, M3, M3′ for any `CMLattice`; M3′ with `HermiteLindemann`; Mη on `E_i` with `MasserCM`). (M2) ✗: needs Gel'fond–Schneider |
| Theorem MX, Prop. D, Cor. MX1 | `Gen.mx_K`, `Gen.mx_full`, `Gen.mx1`, `Final.mx_K`, `Final.mx`, `Final.mx1` | ✔ for every `β ∈ ℚ̄ˣ`: Prop. D for `v ∈ Ψ(Λ(G))` from W88 alone; Theorem MX and Cor. MX1 with the named inputs `WuestholzMX`, `MasserCM`, `LaurentZeta` |
| Cor. Γ | — | it is the hypothesis `hΓ` (Wüstholz); not derived |
| Theorem MX′, Prop. D′ | `Gen.mxP_K`, `Final.mxP_K` | ◐ Prop. D′ (`K`-form, first coordinate, one `v`) ✔ for every `β ∈ ℚ̄ˣ`; the remaining Masser/Wüstholz step of Theorem MX′ is not written out |
| Degree-two corollary (ii): `1, ϖ, Ω_ρ, ϖΩ_ρ/π` `ℚ̄`-independent | `Gen.deg2_ii`, `Final.deg2_ii` | ✔ via Theorem MX (`K`-form) and `WuestholzSix` |
| Degree-two corollary (i): `π, ϖ, Ω_ρ, ϖΩ_ρ` `ℚ̄`-independent | `Gen.deg2_i`, `Final.deg2_i` | ✔ via Prop. D′ and `WuestholzSix`. The paper's proof divides by the `π`-coefficient and misses the case `c₀ = 0`; Lean treats it (one-line fix in `reviews/REFEREE_HYP_MXP.md`) |
| Lemma K | — | ✗ (not needed: the models' subgroup conditions are argued in the reviews) |
| Case tables of MG, MG♮, MX (Thm 4.1 route) | `CaseCheck.*` | ✔ arithmetic layer only; not used by the theorems above, which take the §5d route |
| Step 1 of Proposition 5.1 (Prop. D) (algebra) | `LemmaL.*` | ✔; not used by the MX theorems |
| Lemma U (Appendix A) | — | not a separate hypothesis: part of the proof of W88 Thm 4.1, which `hW` assumes |

## 6. Vendored code and the `lean_lsg` dependency

Since 2026-10-31 the project requires `lean_lsg` as a Lake **path** dependency (`../lean_lsg`, with its own path
dependency `../schanuel/six_exp/lean`); only `CM4E/Unconditional.lean` imports it. This reverses the earlier
self-containment (the project no longer builds from its own directory alone); the published form will use a git
dependency. The vendored `CM4E/Ext/` below predates the dependency and duplicates part of `lean_lsg`.


`CM4E/Ext/` (32 files, 6,518 lines) is a renamed verbatim copy of the needed part of the author's sibling project
`lean_lsg`: Weierstrass `ζ`/`σ`, Legendre's relation, `g₂(ϖℤ[i]) = 4`, and Schneider's theorem. Details and source
commit: [`CM4E/Ext/PROVENANCE.md`](CM4E/Ext/PROVENANCE.md). The project depends on nothing but Mathlib.

## 7. Reviews and provenance

Written by AI models (Claude, Anthropic) under the direction of the author. All review so far is by AI referees: the
fidelity reports in [`reviews/`](reviews/) (scripts and outputs in `reviews/checks/`) and the paper's own referee
reports. No human expert has reviewed the definitions or proofs.

## 8. The CM abelian-variety results (§§3.3, 6, 7.2 of the paper; formerly paper [II])

| result | Lean | status |
|---|---|---|
| Theorem S, Theorems SMG, SMG♮ | `Gen.thmS`, `Gen.smg_false`, `Gen.smgn_false`, `Final.thmS_varpi`, `Final.thmS_omegaRho` | ✔ for CM lattices given as `CMLattice` (`ϖℤ[i]`, `Ω_ρℤ[ρ]`); SMG/SMG♮ with second rows in `𝓛̃` (elliptic logarithms / fibre values in the second row are not formalised) |
| Theorem A, MG-A (families `cP/π`, `cπ/P`) | `AbVar.fourExpAt_A` (generic), `AbVar.fourExpAt_beta5`, `AbVar.fourExpAt_beta7`, `AbVar.fourExpAt_pi_div_beta5`, `AbVar.two_three_beta5` | ✔ for the first-kind eigen-periods `P = (1 − ζ_N)B(1/N, 1/N)` of `y⁵ = x(1 − x)` and `y⁷ = x(1 − x)` (`FourExpAt (cB/π)`, `FourExpAt (cπ/B(1/5,1/5))`; `2^t, 3^t` at `t = Γ(1/5)²/(πΓ(2/5))`); other eigen-periods need their own period data (an instance of the generic model) |
| Theorem A, MG♮-A (families `cP`, `c/P`) | `AbVar.fourExpAt_An` (generic), `AbVar.fourExpAt_beta5'`, `AbVar.two_three_beta5'` | ✔ for `y⁵ = x(1 − x)`: `FourExpAt (cB(1/5, 1/5))`, and **`2^t, 3^t` are not both algebraic at `t = Γ(1/5)²/Γ(2/5)`** (the paper's example); the relation `B(1/5,1/5)B(4/5,4/5) ∈ πℚ̄ˣ` is proved (`AbVar.beta5_mul`) |
| `K`-dimension forms of MG-A, MG♮-A | `AbVar.mgA_K`, `AbVar.mgAn_K` | ✔ for every number field `K ⊇ ℚ(ζ_N, i, c)` (the range for which the paper states them); logarithms of `A` (`A^♮`) enter as parameters `LA`, `LAn`, as for X7 |
| Cor. A2: one of `e^{aπ²}, e^{bπP}, e^{cπ²/P}` is transcendental | `AbVar.corA2` (generic), `AbVar.corA2_beta5` | ✔ by the paper's route (MG-A `K`-form at `s = P/π`, `LA = ∅`), with `π` transcendental (proved) and the named input `NotLtildeA` (`P ∉ ℚ̄ + ℚ̄𝓛`); instance `B(1/5,1/5)` |
| Theorem X7 (`y⁷ = x(1 − x)` with `E` of CM by `ℚ(√−7)`) | `AbVar.propX7_K`, `AbVar.propX7`, `AbVar.thmX7`, `AbVar.thmX7_torsion` | ✔ Proposition X (first coordinate, `K`-form) and the full conclusion of Theorem X7 (`q₁ = q₂ = 0`, all points torsion), the torsion step being the named input `TorsionX7`; logarithms of `A` enter as `LA` (below) |
| Cor. X7 (c): `1, B(2/7,2/7), B(3/7,3/7), B(3/7,3/7)/B(1/7,1/7)` are `ℚ̄`-independent | `AbVar.x7c` | ✔ (only periods; `LA = ∅`) |
| Cor. X7 (a), (b) | `AbVar.x7a_full`, `AbVar.x7b` (for `LA`); `AbVar.x7a_AJ`, `AbVar.x7b_AJ` (literal: Abel–Jacobi integrals `∫_O^Q dx/y^{7−s}` along lifts of `C¹` paths avoiding the branch points) | ✔ with `LA = LAJ`, the `ℚ`-span of the Abel–Jacobi triples (`AbVar.LAJ`); (a) in full (`ℚ̄`, including `z₁(v) ≠ 0`), (b) for `ℚ̄ˣ` as in the paper; endpoints at the branch points `(0,0), (1,0), ∞` are not covered |
| Theorem X (general first-kind relations), Prop. 15 | `AbVar.XSetup.propX15`, `AbVar.XSetup.thmXA` (generic); `AbVar.thmX7_of_gen` (level seven as an instance, (R) from `AbVar.relation_R`) | ◐ for any four pairwise distinct first-kind slots of simple CM abelian varieties with a relation `P_aP_b = μP_cP_d` (hypothesis, as in the paper): Prop. 15 as the set equality `V ∩ Ψ(Λ_K(G)) = Kw + Kw'` (for `[K : ℚ] ≥ 5`, never restrictive), with (Ch) proved from Dedekind's independence of characters (`AbVar.ch_span`); Theorem X without the torsion clause (at level seven: `thmX7_torsion`); conditional on `AbVar.Thm11KappaXA` (W88 for the block groups) |

**The CM-abelian models** (`CM4E/AbVar/`). The group `G''` of each proof is written, up to isogeny, as a product of
copies of `A` (and `E`, `G_a`, `G_m`) in explicit eigen-coordinates; the paper's quotient `A^n/B_{ker ψ}` is isogenous to
`A^r` via CM quotient maps adapted to the slot, so no quotient appears in Lean. The models and their hypotheses:

| name | group | where | review |
|---|---|---|---|
| `AbVar.Thm11KappaX7 LA` | `A^{3r} × E^{3r} × G_a²`, `A = Jac(y⁷ = x(1 − x))`, `E` with lattice `B(1/7,2/7)ℤ[α]`, `α = (−1+√−7)/2`; frame `gmFX` (`d₂ = dim G''`, conservative) | `CM4E/AbVar/X7.lean`, `FrameX.lean` | [`reviews/REFEREE_HYP_X7.md`](reviews/REFEREE_HYP_X7.md) (CORRECT WITH NOTES): period triple checked on one explicit cycle to `10⁻⁶⁰`, CM action, `g₂, g₃` of `E` algebraic (`j = −3375`) |
| `AbVar.Thm11KappaXA S` | `∏_j A_j^{r_j} × G_a²`, one block per slot (`r_j = n/[F_j : ℚ]`), slot forms `Σ_i b_j i z_{s_j}`, frame `gmFX` | `CM4E/AbVar/XGen.lean` | [`reviews/REFEREE_HYP_XA.md`](reviews/REFEREE_HYP_XA.md) (CORRECT WITH NOTES): sound for faithful records (primitive `α`, one cycle, `LA` of logarithms) and pairwise distinct slots; for non-distinct slots the model is unsound, but `WuestholzXA` is then false; `Distinct` follows from `WuestholzXA` (`XSetup.distinct_of_wuestholz`); non-isogeny of different records is a convention |
| `AbVar.Thm11KappaA N g κ P s₀` | `G_m^{2n} × A^r` (first-kind slot `s₀`), frame `gmF` | `CM4E/AbVar/ThmA.lean` | [`reviews/REFEREE_HYP_A.md`](reviews/REFEREE_HYP_A.md) (CORRECT WITH NOTES): instances `N = 5, 7` checked on one cycle to `10⁻⁶⁰`, Jacobians simple of type `{1,2}`, `{1,2,3}`. Since 2026-10-31 it is W88 §5d only for *toric-injective* hyperplanes (`HyperplaneKappaOn … (TorInj …)`: no nonzero period of `A^r` alone lies in `V`), which is weaker (`HyperplaneKappa.on`); the proof uses only `V''`, toric-injective by `perA_inj` (this needs every `κ s` prime to `N`, a new hypothesis `hκN` of `fourExpAt_A`, `mgA_K`, `corA2`, true for a CM type) |
| `AbVar.Thm11KappaAK …`, `AbVar.Thm11KappaAnK …` | the groups of `Thm11KappaA`, `Thm11KappaAn` on the frame `gmF2` (uniform subgroup condition), with the logarithms `[ζ^e]v` (`v ∈ LA`), resp. `[ζ^e](v, w)` (`(v, w) ∈ LAn`) added | `CM4E/AbVar/MGAK.lean` | [`reviews/REFEREE_HYP_AK.md`](reviews/REFEREE_HYP_AK.md) (CORRECT WITH NOTES): sound when `LA` (`LAn`) consists of full, coherent coordinate tuples of logarithms of `A` (`A^♮`) in the normalisation of `P` (`P̄`); unconditional for `LA = ∅`. `Thm11KappaAK` is narrowed to toric-injective hyperplanes (`HyperplaneKappaOn … (TorInj …)`) exactly as `Thm11KappaA`; `Thm11KappaAnK` is unchanged |
| `AbVar.Thm11KappaAn N g κ P P̄` | `G_m^{2n} × Q''`, `Q'' = (A^♮)^r/W'` (second-kind slot `ζ ↦ ζ^{N−1}`), frame `gmF` | `CM4E/AbVar/ThmAn.lean` | [`reviews/REFEREE_HYP_AN.md`](reviews/REFEREE_HYP_AN.md) (CORRECT WITH NOTES): `Q''` is isomorphic to the paper's `(A^♮)^n/U`; `P̄ = ∫_γ dx/y` over the same cycle to `10⁻⁷⁰`; the subgroup argument uses (F1)–(F4) (Mazur–Messing), a soundness fact |

The generic hypotheses `Thm11KappaA`, `Thm11KappaAn` are W88 instances only when their parameters come from a real CM
abelian variety (in particular `φ(N) = 2g`, and for `Thm11KappaAn` the embedding `ζ ↦ ζ^{N−1}` must be a second-kind
slot); they are claimed for the stated instances. Named classical inputs (explicit hypotheses):

| name | content | why it is believed |
|---|---|---|
| `AbVar.ChowlaSelberg7` | `g₂, g₃` of `E7 = B(1/7,2/7) ℤ[α]` are algebraic (premises of `Thm11KappaX7`, as in the `Thm11Kappa` convention) | Chowla–Selberg (Gross 1978); `j = −3375`, checked to 120 digits in `reviews/checks/hypx7/` |
| `AbVar.WuestholzBeta7` | `1, P₁, P₂, P₃, Ω` (`P_j = (1 − ζ₇^j)B(j/7,j/7)`, `Ω = B(1/7,2/7)`) are `ℚ̄`-linearly independent | Wüstholz 1989 on `G_a × A × E` (distinct eigen-slots); [`reviews/REFEREE_INPUTS_X7.md`](reviews/REFEREE_INPUTS_X7.md): TRUE AS STATED (PARI `lindep` at 600 digits finds nothing) |
| `AbVar.WuestholzX7 LA` | slot splitting of `z₁(v) + u + q = cP₁ + c'Ω` and `z₃(v') + z₂(v) + q = cP₃ + c'P₂` | Wüstholz 1989 on `G_a × A² × E²`, `G_a × A³`; same review: TRUE for every `LA ⊂ LA_A` |
| `AbVar.WuestholzXA S` | `1, P_a, P_b, P_c, P_d` are `ℚ̄`-linearly independent (distinct first-kind slots) | Wüstholz 1989 on `G_a × ∏_A A`; [`reviews/REFEREE_INPUTS_XA.md`](reviews/REFEREE_INPUTS_XA.md): CORRECT; at level seven it is `WuestholzBeta7` by `rfl` |
| `AbVar.WuestholzSplitXA S` | slot splitting of `x + x' + q = cP_a + c'P_d` (and `c, b`) for `x, x' ∈ ℚ̄z(Λ)` | Wüstholz 1989 on `G_a × A_a^{N+1} × A_d^{N'+1}` (paper's proof of Theorem X); same review: CORRECT WITH NOTES (false for `LA` not made of logarithms, then `thmXA` is vacuous); implies `WuestholzX7` |
| `AbVar.WuestholzA5`, `AbVar.WuestholzA7` | `P/π ∉ ℚ̄` for `P = (1 − ζ_N)B(1/N, 1/N)`, `N = 5, 7` | Wüstholz on `G_m × A`; `reviews/REFEREE_HYP_A.md`: CORRECT |
| `AbVar.NotLtildeA P` | `P ∉ 𝓛̃ = ℚ̄ + ℚ̄𝓛` (implies `P/π ∉ ℚ̄`) | Wüstholz on `G_a × G_m^m × A`; `reviews/REFEREE_HYP_AK.md`: true for first-kind eigen-periods (PSLQ at 400 digits finds no relation for `B(1/5,1/5)`) |
| `AbVar.TorsionX7 LA` | the torsion step: a logarithm of `A` with a slot coordinate in `ℚ̄P_{s+1}` is in `Fγ`; an elliptic logarithm in `ℚ̄Ω` is in `ℚ(α)Ω` | Wüstholz on `A²` with `End⁰(A) = F`; Masser 1975; [`reviews/REFEREE_TORSION_X7.md`](reviews/REFEREE_TORSION_X7.md): TRUE for every subset of the intended set (and its `ℚ`-span), but **not** for its `ℚ̄`-span or rescaled triples |
| `AbVar.WuestholzB5` | `P̄/π ∉ ℚ̄` for the second-kind period `P̄ = (1 − ζ₅⁴)B(4/5, 4/5)` | Wüstholz on `G_m × A^♮`; by `B(1/5,1/5)B(4/5,4/5) ∈ πℚ̄ˣ` it is equivalent to the transcendence of `B(1/5, 1/5)` (Schneider 1941); `reviews/REFEREE_HYP_AN.md`: CORRECT |

The classical facts that the Beta expressions are the periods of the stated cycles (Weil, Rohrlich's appendix to Gross
1978) and that `B(1/7,2/7)ℤ[α]` is the lattice of a curve with algebraic invariants (Chowla–Selberg; for `Thm11KappaX7` it is the named input `ChowlaSelberg7`) are **soundness
facts** of the models, checked numerically in the reviews, not Lean hypotheses and not proved in Lean.

**The parameter `LA`.** Lean has no Jacobians, so the logarithms of `A` enter `thmX7` as a set `LA ⊂ ℂ³`. The intended
instantiation is any subset of `LA_A = {(z₁(v), z₂(v), z₃(v)) : exp_A(v) ∈ A(ℚ̄)}`, where `z_s(v) = ∫_v dx/y^{7−s}` are the
Abel–Jacobi eigen-coordinates in which the period triple `perT = (P₁, P₂, P₃)` of the cycle `γ` is written (coherent
triples of one point). `thmX7` is proved for every `LA`; for a set not of this form the hypotheses `Thm11KappaX7 LA` and
`WuestholzX7 LA` can be false (e.g. `WuestholzX7 {(1, 0, 0)}` is false), and the theorem is then vacuous rather than
wrong. `x7c` uses `LA = ∅`, for which `Thm11KappaX7` needs no such reading.

**What is still missing** for the abelian-variety part: the first-kind relations themselves beyond level seven (Deligne's
theorem in the form stated by Koblitz–Ogus; Theorem X takes (R) as a hypothesis, as the paper does); the torsion clause
of the generic Theorem X; period data for other Beta values (each a new instance and review);
Cor. X7 (a), (b) for endpoints at the branch points (improper integrals); the reduction of Theorems MG-A, MG♮-A to
simple CM abelian varieties of primitive type for non-cyclotomic CM fields.