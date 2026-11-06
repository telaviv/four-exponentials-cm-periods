# Referee report: Theorem SE(3) = SE₀ (`gmStdVec` copy, `gmFX0`, `gmESV`/`gmSE0`, `Thm11KappaSE0`, `thmSE0`, the SE₀ bridge, the `ϖ` wrappers)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope.**
* In full:
  - `CM4E/Bridge/StdVec.lean`: `gmStdVec`, `hypStdVec_cm`;
  - `CM4E/AbVar/FrameX0.lean`: `gmFX0`, `genX0`, `frameX0_false`;
  - `CM4E/AbVar/SE0.lean`: `FibE`, `QbarLFib`, `genV`, `lamESV`, `perESV`, `gmESV`, `logNat_of_logE`, `logNat_mul`,
    `vLiftB` and its lemmas, `gmSE0`, `Thm11KappaSE0`, `thmSE0`;
  - `CM4E/Bridge/SE0.lean`: `phiV`, `rowM`, `eta_lattice`, `zeta_omega`, `conj_div_mem`, `hyperplaneKappa_gmESV`,
    `uniform_SE0`, `thm11KappaSE0_uncond`, `transcendental_eta_div_omega`, `thmSE0_of_cm`, `thmSE0_paper`,
    `transcendental_pi_div_varpi_sq`, `thmSE0_varpi`, `thmSE0_varpi_Ltilde`.
* For context:
  - `CM4E/AbVar/{FrameX1,SE}.lean` (`TX`, `PsiX`, `algX`, `eLiftB`, `LtildeE`, `aSE1`, `aSE2`);
  - `CM4E/MX.lean` (`LogNat`), `CM4E/Gen/{CMLattice,MGn,MGnK,Instances,ThmM}.lean`, `CM4E/Bridge/{Vec,ELog}.lean`;
  - in `lean_lsg`: `LSG/W88/StdVec.lean` (`MStarCopy.gmStdVec`, `hypStdVecCM`), `LSG/W88/StatementVec.lean` (`TanV`,
    `LamV`, `PerV`, `SubgroupDataV`, `perTanId`), `LSG/CM/{Rot,Kappa}.lean` (`CMData`, `cmData_of_zeta`),
    `LSG/W88/V5dMGnIso.lean` (`CMLat.cmD`), `INTERFACE.md` (last section).
* Paper:
  - the first draft of Theorem SE §1 (Theorem `thm:SE`(3), Cor. `cor:SE4`, Lemma `lem:SE0`,
    the proof of (SE♮, SE₀));
  - the merged draft §4.3 (l. 1595–1625: Theorem 4.12, its Status line, Cor. 4.13) and the
    definitions of `η*`, `ζ*`, `κ₁` (l. 122–128, §`sec:Euniv` l. 642–650).
* Baselines, whose findings are not repeated here:
  - `REFEREE_HYP_SE` (sibling: `G_a` in `d₀`, the `gmFX1` count, `LtildeE`, transport pattern);
  - `REFEREE_BRIDGE_STD` (transport), `REFEREE_HYP_M` #1 / `REFEREE_HYP_SMG` #14 (`G_a` of weight 0).

**Process.** No project file other than this report and `reviews/checks/hypse0/` was edited, no git command was run, and
`lake build` was not run. The scratch files are:
* `reviews/checks/hypse0/AxSE0.lean` and `AxSE0.out`:
  - the kernel check of the `gmStdVec` copy (two `Iff.rfl` examples, see #1);
  - `#check` of the five public statements and `#print` of `FibE`, `QbarLFib`, `Thm11KappaSE0`;
  - the axiom audit of 13 declarations.
* `reviews/checks/hypse0/KappaUnit.lean` and `KappaUnit.out`: the referee lemma `kappaOneZero_unit`, proved with
  standard axioms only. `KappaOneZero L` forces `L.p = −1` and `L.q ∈ {−1, 0, 1}`, i.e. `ℤ + ℤα ∈ {ℤ[i], ℤ[ρ]}` (#13).
  - It is stated for `lean_lsg`'s `MStarCopy.CMLattice`/`MStarCopy.KappaOneZero`, because the concurrent build had
    removed `CM4E.Gen.Frame.olean` at the time.
  - By `AxSE0.lean`, `KappaOneZero L ↔ MStarCopy.KappaOneZero (adaptL L)` holds by `Iff.rfl`, and `adaptL` copies `p`,
    `q`, `α`. So the lemma applies verbatim to `CM4E.Gen.CMLattice`.
* `reviews/checks/hypse0/EtaRfl.lean` and `EtaRfl.out`: `@CM4E.Ext.Weierstrass.eta = @LSG.Weierstrass.eta := rfl`
  compiles, and `#print` shows `η(ω) = ζ(ω₁/2 + ω) − ζ(ω₁/2)`.

The oleans of the four new files (12:42–12:54) are newer than their sources (12:36–12:53). `AxSE0.lean` ran in 42 s,
before the concurrent build started rebuilding.

## Verdicts

* **Item 1 (the `gmStdVec` copy): CORRECT.**
  - The body (from `noncomputable def gmStdVec` to the `sub` field) is textually identical to
    `LSG.W88.MStarCopy.gmStdVec`; `diff` reports no difference. The only change is the ambient `GroupModel`.
  - The kernel accepts both directions of the match:
    - `hypStdVec_cm`'s body is the term `LSG.W88.hypStdVecCM (adaptL L) …`, of type
      `MStarCopy.HyperplaneKappa (MStarCopy.gmStdVec …)`, checked against `CM4E.Waldschmidt.HyperplaneKappa
      (CM4E.Bridge.gmStdVec …)`;
    - the referee example `HyperplaneKappa (Bridge.gmStdVec d0 d1 (fun _ => L.pp) M) ↔ MStarCopy.HyperplaneKappa
      (MStarCopy.gmStdVec d0 d1 (fun _ => (adaptL L).pp) M) := Iff.rfl` compiles for all `d0 d1 m r M`;
    - `KappaOneZero L ↔ MStarCopy.KappaOneZero (adaptL L)` also holds by `Iff.rfl`.
  - The premises of `hypStdVecCM` are satisfied at both call sites:
    - `r = 1` (`le_rfl`), with `M = rowM (aSE2 0 γ)` (entries `0` or `γ_i`, algebraic by `hb.alg`);
    - `M₁ = (1)` in `transcendental_eta_div_omega`.
* **Item 2 (`gmFX0`, `frameX0_false`): CORRECT.**
  - `G'' = G_a × G₂`, where `G₂` is the push-out of `(E^{3r})^♮` along the nonzero row `(0, 0, γ)`.
    - This extension of `E^{3r}` by `G_a` is non-split: a retraction to the fibre would be a nonzero element of
      `Hom((E^{3r})^♮, G_a) = 0`.
    - So `d₀ = 1`, `d₁ = 0`, `d₂ = 3r + 1` are the maximal decomposition. `gmFX0` uses exactly these values, matching
      `gmStdVec 1 0` (`d₂ = m + r = 3r + 1`) and the paper (`d₀ = 1`, `d₂ = 3n/2 + 1`).
  - The count is right: `m = 3n`, `κ ≥ n`, `d − 1 − t = (dim Q + 2) − 1 − dim Q = 1`. (5.4) is
    `3n > 2(dim Q + 1) − κ`, which follows from `dim Q + 1 < 2n`.
  - In `thmSE0`, `dim Q = 3r` and `n = 2r`, so `hcount` reads `3r + 1 < 4r`, i.e. `r ≥ 2`. That is what
    `exists_adapted_basis` supplies, and it matches the paper's "margin `n − 2` for `n ≥ 4`".
  - The conclusion is as in `frameX1_false`: an algebraic `x ∈ ker(Ψ''₂ − σΨ''₁)` with `Ψ''(x) ≠ 0` makes `σ`
    algebraic.
* **Item 3 (model soundness of `gmESV`/`gmSE0`, the uniform condition): CORRECT.**
  - **No counterexample exists in Lean:** `thm11KappaSE0_uncond` proves `Thm11KappaSE0 L` for every `CMLattice`, with
    standard axioms. So the model question reduces to the transport (checked by Lean) and to `gmStdVec`, which `lean_lsg`
    proves.
  - The CM action on the fibre is conjugate-linear, `(u, w) ↦ (αu, ᾱw)`, which is right when `κ₁ = 0` (#5).
  - The block-3 lift is correct: `Σ γ_i[(a_i + qb_i) − b_iᾱ] w = Σ γ_i(a_i + b_iα) w = xw`, because `q − ᾱ = α` (#6).
  - Periods are `(λ e_j, 0, cM_j η(λ))` and the `ℚ̄`-structure is all coordinates algebraic. Both match `PerV` and
    `AlgVecV` under `phiV` (#7).
  - `uniform_SE0` handles subgroups that mix the three `E`-blocks correctly (#8):
    - for `κ₁ = 0`, `T(B^♮)` contains both `(λ, 0)` and `(0, η(λ))` for every lattice point `λ ∈ t`;
    - the two algebraic vectors `x₁ = (λ/Ω, 0, 0)` and `x₂ = (0, 0, Σγ_j conj(λ_{b3 j}/Ω))` read blocks 1, 2 and 3
      separately.
* **Item 4 (faithfulness): CORRECT WITH NOTES.**
  - `FibE` is `Fib_E`, and `QbarLFib` is `ℚ̄𝓛_E + ℚ̄·Fib_E` (#9, #10).
  - `t`, the independence hypothesis and the conclusion match Theorem 4.12(3) (#11).
  - `thmSE0_paper` is Theorem 4.12(3) verbatim (arbitrary nonzero period `Ω`, `η = η(Ω)`), for the curves it covers
    (#12).
  - **Main note (#13):** `KappaOneZero` forces `α` to be a unit (referee lemma `kappaOneZero_unit`). So the general
    theorems cover exactly the curves with `j ∈ {0, 1728}`, i.e. `E_i`, `E_ρ` and their `ℚ̄`-twists, not every CM curve.
    The docstrings say "`κ₁ = 0` (true for `ϖℤ[i]` and `Ω_ρℤ[ρ]`)" but never say that it holds *only* for these.
  - `thmSE0_varpi` is the correct `ϖ` instance: `η₀ = π/ϖ`, `t = cπ/ϖ²`, no hypotheses (#14).
  - `thmSE0_varpi_Ltilde` is Cor. 4.13 at `t = cπ/ϖ²`, under the extra hypothesis `ϖ ∉ ℚ̄u₁ + ℚ̄u₂`, which the paper
    derives from Lemma SE0 (`η ∉ 𝓛̃_E`). The docstring states the extra hypothesis (#15).
* **Item 5 (`transcendental_eta_div_omega`, `transcendental_pi_div_varpi_sq`): CORRECT.**
  - The statements are right and true (`η₀/Ω = 2πi/((α − ᾱ)Ω²)`, and `π`, `Ω` are algebraically independent by
    Chudnovsky).
  - The proof is W88 §5d on `E^♮` with `V = W = ℂ(1, β)`, which is sound. There is no circularity: `hypStdVecCM` takes
    only `κ₁ = 0`, algebraic invariants, `r ≤ 1` and `AlgMat M` (#16).
* **Item 6 (axioms): CORRECT.**
  - `thmSE0_varpi`, `thmSE0_paper` and `transcendental_pi_div_varpi_sq` depend only on `propext`, `Classical.choice`
    and `Quot.sound`. So do the 10 further declarations audited (#17).
  - The four new files contain no `sorry`, `axiom`, `admit` or `native_decide`.

**No FATAL or MAJOR issue was found.** `Bridge.thmSE0_varpi` (Theorem 4.12(3) for `E_i`, with no hypotheses) and
`Bridge.transcendental_pi_div_varpi_sq` are Lean theorems over Mathlib, and so is `Bridge.thmSE0_paper`. The residual
hypotheses of `thmSE0_paper` are:
* `κ₁ = 0`, i.e. `j ∈ {0, 1728}`;
* algebraic invariants;
* `CMMulLogE`.

As in `REFEREE_HYP_SE`, correctness reduces to the faithfulness of the statements (item 4), not to the soundness of any
model.

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | 1, verbatim copy | `diff` of the two `def` blocks: identical. Kernel checks: (a) `hypStdVec_cm := LSG.W88.hypStdVecCM (adaptL L) hκ …` elaborates against the `CM4E` statement; (b) `Iff.rfl` between `CM4E.Waldschmidt.HyperplaneKappa (Bridge.gmStdVec …)` and `MStarCopy.HyperplaneKappa (MStarCopy.gmStdVec … (adaptL L).pp …)` for arbitrary `d0 d1 m r M` (`AxSE0.lean`); (c) `KappaOneZero L ↔ MStarCopy.KappaOneZero (adaptL L)` by `Iff.rfl`. `adaptL` is the field-by-field repackaging of `CMLattice` (`Bridge/Vec.lean:37`). This is the same check as `REFEREE_HYP_SE` #9 did for `hypStd_of_pair` |
| 2 | OK | 1, premises | `hypStdVecCM` needs `κ₁ = 0`, algebraic `g₂`, `g₃`, `r ≤ 1` and `AlgMat M`. In `hyperplaneKappa_gmESV`, `r = 1` (`rowM`), and `hM` comes from `hcM`, which `thm11KappaSE0_uncond` discharges with `forall_blocks` (zero on `b1`, `b2`, and `γ_i` on `b3`, algebraic by `hb.alg`). In `transcendental_eta_div_omega`, `M₁ = (1)` |
| 3 | OK | 2, `d₀`/`d₂` | `G₂ = (E^{3r})^♮ ⊔_{(0,0,γ)} G_a` is a non-split extension: a splitting would give a surjection `G₂ → G_a`, and composing gives a nonzero map `(E^{3r})^♮ → G_a`, but `Hom(B^♮, G_a) = 0`. So `Hom(G'', G_a) = ℚ̄` (the `G_a` factor) and `Hom(G'', G_m) = 0`, which gives `d₀ = 1`, `d₁ = 0`, `d₂ = 3r + 1`. Even a split `G₂` would only make the model's hypothesis weaker (one `G_a` counted in `d₂`). `hd` in the transport is an equality, `0 + 2(m + 1) ≤ 0 + 2(m + 1)` |
| 4 | OK | 2, count | `m = 3·card ι = 6r` (the `3n` lifts are `ℚ`-independent: their `Ψ''₁`-values `θ_h·(Ω, u₁, u₂)` are `K`-independent, `hind`). `κ ≥ n` from the `n` period lifts (`hpp`). `W = ker Ψ''` (dimension `dim Q`, `ℚ̄`-rational through the unit vectors, `T`), `V = ker(Ψ''₂ − σΨ''₁)` a hyperplane, `d − 1 − t = 1`. Premise: `6r > 2(3r + 1) − κ`, which holds since `κ ≥ 2r ≥ 4`. `frameX0_false` checks it with `omega` from `hcount : dim Q + 1 < 2n` |
| 5 | OK | 3, CM on the fibre (`logNat_mul`) | Lattice case: `α(a + bα) = a' + b'α` gives `ᾱ(a + bᾱ) = a' + b'ᾱ` by conjugation, so `ᾱw − etaL a' b' = ᾱ(w − etaL a b) ∈ ℚ̄`. Non-lattice case: `αu ∉ Λ` (`α` is a unit), `℘(αu)`, `℘'(αu) ∈ ℚ̄` (`CMMulLogE`), and `ᾱw − ζ(αu) = ᾱ(w − ζ(u))` (`κ₁ = 0`). This is right: `End(E)` acts on `H^1_dR^∨` by the identity character on `z` and the conjugate character on `w` (paper l. 643–646). For `κ₁ ≠ 0` it would be false for the Weierstrass `ζ`, but `κ₁ = 0` is a hypothesis everywhere it is used |
| 6 | OK | 3, block-3 lift (`vLiftB`) | `x = Σ_i (a_i + b_iα)γ_i` (`coordsA`). The lift is `Σ_i (a_i + qb_i)·genV(u, w) − b_i·genV(αu, ᾱw)`. Fibre: `Σ γ_i((a_i + qb_i) − b_iᾱ)w = Σ γ_i(a_i + b_iα)w = xw`, because `ᾱ = q − α`. Base: `Σ(a_i + b_iᾱ)u e_{b3 i}`, which no `μ` reads. `PsiX_vlift3` proves `Ψ'' = (0, xw)`. It lies in `lam` by `logNat_mul`, and for `(u, w) = (Ω, η₀)` in `span per` through the generators `(1, 0)` and `(0, 1)` of `perESV` (`etaL 0 1 = ᾱη₀`) |
| 7 | OK | 3, periods, `ℚ̄`-structure, transport | `phiV (z, s₁, s₂) = ((s₁), (), z, (s₂))` is a linear isomorphism. `algX algVF` (all coordinates algebraic) maps onto `AlgVecV`. `genV j u w ↦ (0, (), u e_j, (cM_j w))`, which is in `LamV` because `cM_j w − Σ_k cM_k ζ(u e_j)_k = cM_j(w − ζ(u)) ∈ ℚ̄` (`logNat_zeta`: `LogNat` with `etaL` is `Λ(E^♮)` when `κ₁ = 0`). The algebraic `(0, c₁, c₂)` lie in `LamV`. Closure: `lamVSub` is an additive subgroup of `LamV`. Periods: `genV j λ (etaL a b) ↦ (0, (), λe_j, (cM_j η(λ)))` lies in `PerV`, by `eta_lattice` (`η(aΩ + bαΩ) = (a + bᾱ)η₀`, through `CMData.eta_eq_conj` and `eta_one_eq`) |
| 8 | OK | 3, uniform condition (`uniform_SE0`), mixing | A `SubgroupDataV` is `Γ + T(B̃)` (the torus part is trivial). (i) If `Γ ≠ 0`, it has an algebraic `w = (a, s) ≠ 0` (`gam_rat`), and `Ψ''(0, a, s) = (a, s) ≠ 0`. This covers the diagonal lines in `G_a × G_a^{fib}`. (ii) If `Γ = 0`, then `t ≠ 0`, and there is a lattice point `λ ≠ 0` in `t` (`span_lat_eq`). `T(B^♮)` contains `(λ, 0)` and `(0, η(λ))` (`LSG.CM.fst_mem`, `snd_mem`), since `t` is `α`-stable and `η(αλ) = ᾱη(λ)`. Hence `T(B̃)` contains `x₁ = (λ/Ω, 0, 0)` and `x₂ = (0, 0, Σγ_j conj(λ_{b3 j}/Ω))`, both algebraic. `Ψ''(x₁) = (μ₁(λ), μ₂(λ))/Ω` reads `λ_{b1}`, `λ_{b2}`. `Ψ''(x₂) = (0, Σγ_j conj(λ_{b3 j}/Ω))` reads `λ_{b3}`, through the lattice vector `Ω·conj(λ_{b3}/Ω)` (`conj_div_mem`, `ᾱ = α⁻¹`). If all vanish, `lattice_eq_zero` (`k`-independence of `γ`) kills each block, so `λ = 0`. **Mixing the blocks cannot defeat this:** an abelian `B ⊂ E^{3r}` that is a graph between blocks still has its lattice vectors read block by block, because `x₁` keeps the full `λ` and `x₂` the full `λ_{b3}`. This is exactly where SE₀ differs from SE (`REFEREE_HYP_SE` #7): there the cancellation was inside `μ₂` between two blocks; here block 3 is read only through the fibre, and the fibre component `η(λ)` of `T(B^♮)` is separable from `λ` when `κ₁ = 0` |
| 9 | OK | 4, `FibE` | `FibE L = {w : ∃u, LogNat L.pp (etaL L) u w}`. That is `u = aΩ + bαΩ` with `w − (a + bᾱ)η₀ ∈ ℚ̄`, or `u ∉ Λ`, `℘(u)`, `℘'(u) ∈ ℚ̄` and `w − ζ(u) ∈ ℚ̄`. With `κ₁ = 0`, `(a + bᾱ)η₀ = η(u)` (`eta_lattice`) and `ζ = ζ*`, so this is the paper's `Fib_E = {w(X) : X ∈ Λ(E^♮)}` (`(u, ζ*(u) + t)`, and `(λ, η*(λ) + t)` on the lattice; paper l. 646–648). It contains `ℚ̄` (`algebraic_mem_FibE`), `η₀` (`eta_mem_FibE`) and `ζ(u)` for `u ∈ 𝓛_E ∖ Λ`. Remark: any `ℚ̄`-rational renormalisation `w ↦ aw + bu` of the fibre coordinate leaves `ℚ̄𝓛_E + ℚ̄Fib_E` unchanged, so the target set does not depend on the coordinate |
| 10 | OK | 4, `QbarLFib` | Finite sums `Σβ_k v_k + Σβ'_k w_k` with `β`, `β'` algebraic, `LogE v_k` and `w_k ∈ FibE` (`N`, `N' = 0` allowed). As a set this is `ℚ̄𝓛_E + ℚ̄·Fib_E`. `LogE` includes the lattice, as the paper's `𝓛_E` does. `LtildeE_subset_QbarLFib` (`ℚ̄ ⊂ Fib_E`) is correct |
| 11 | OK | 4, `t`, `hind`, conclusion | `thmSE0`/`thmSE0_of_cm`: `t = c·η₀/Ω` with `Ω = L.ω` and `η₀ = η(Ω)` (`zeta_omega`, `eta_one_eq`); `c` algebraic and nonzero; `u_j ∈ LtildeE` (`ℚ̄ + ℚ̄𝓛_E`). `hind` is the `ℚ̄`-independence of `Ω, u₁, u₂`. The conclusion `¬(tu₁ ∈ QbarLFib ∧ tu₂ ∈ QbarLFib)` is the paper's "not both". In the proof, the data lifts put `u_j`'s `𝓛`-part in block 1, `β₀` in `G_a`, `tu_j`'s `𝓛`-part in block 2 and its `Fib`-part in block 3. The period lift puts `θ_hΩ` in block 1 and `θ_h c(Ω, η₀)` in block 3. So `Ψ'' = θ_h(Ω, tΩ)` and `θ_h(u_j, tu_j)`, as in the paper's `w = (Ω, cη)`, `v_j = (y_j, ty_j)` |
| 12 | OK | 4, `thmSE0_paper` | Here `Ω ∈ Λ ∖ 0` is arbitrary and `η = Ext.Weierstrass.eta L.pp Ω = ζ(ω₁/2 + Ω) − ζ(ω₁/2)`, the genuine quasi-period (and `= LSG.Weierstrass.eta` by `rfl`, `EtaRfl.lean`). With `Ω = sω`, `s = a + bα`, we get `η(Ω) = s̄η₀`, so `t = (cs̄/s)·η₀/ω`, and `hind` transfers through `a₀ ↦ a₀/s`. Since `κ₁ = 0`, `η*(Ω) = η(Ω)`, so this is Theorem 4.12(3) word for word, for the curves `E_L` (see #13). The paper's parenthetical `t ∈ ℚ̄^×π/Ω²` is a consequence (Legendre), not a hypothesis. Every curve over `ℚ̄` with `j ∈ {0, 1728}` *is* some `E_{L.pp}`: take `Λ = ω(ℤ + ℤα)` with `α = i` or `ρ` and `η₀ = η(ω)`, and Legendre gives the `legendre` field. So for these curves no generality is lost |
| 13 | MINOR (docs/scope) | 4, `κ₁ = 0` restriction | `KappaOneZero L` (`ζ(αz) = ᾱζ(z)` as functions) gives `CMData` (`cmData_of_zeta`): `αΛ = Λ` and `ᾱ = α⁻¹`. The referee lemma `kappaOneZero_unit` (`KappaUnit.lean`, standard axioms) derives `L.p = −1` and `L.q ∈ {−1, 0, 1}`, i.e. `α ∈ {e^{2πi/3}, i, e^{πi/3}}`. **So `thmSE0_of_cm`/`thmSE0_paper` cover exactly the curves with `j ∈ {0, 1728}`.** The paper's Theorem 4.12(3) is for every CM curve, with `η = η*(Ω) = η(Ω) − κ₁Ω`. For `κ₁ ≠ 0`, `t = cη*/Ω = cη/Ω − cκ₁` is not a `ℚ̄^×`-multiple of the Lean `t`, so Lean says nothing there. The docstrings (`AbVar/SE0.lean` l. 20–22, `Gen/MGn.lean` l. 58, `Bridge/SE0.lean` l. 438–442) say "`κ₁ = 0` (true for `ϖℤ[i]` and `Ω_ρℤ[ρ]`)" / "true when `α` is a unit", which a reader may take as a mild condition. Fix: say "`κ₁ = 0`, which forces `α` to be a unit, so `E_L` has `j ∈ {0, 1728}`". Optionally promote `kappaOneZero_unit`. In `TRUST.md`, the SE₀ row should say "for `j ∈ {0, 1728}`". Extending to general CM needs the `ζ*` fibre coordinate in `LogNat`/`etaL` and in `lean_lsg`'s `LamV` |
| 14 | OK | 4, `thmSE0_varpi` | `latI = (lemniscatic, ω = ϖ, α = i, η₀ = π/ϖ)`, with `ϖ = Γ(1/4)²/(2√(2π)) = 2.622…`, the real period of `y² = 4x³ − 4x`. `η(ϖ) = π/ϖ` agrees with the classical `2ζ(ϖ/2) = π/ϖ` and with the `legendre` field (`ϖ·η₀·2i = 2πi`). So `t = cη₀/ϖ = cπ/ϖ²`, the rewrite `e` is right, and the hypotheses `κ₁ = 0`, `g₂`, `g₃` and `CMMulLogE` are all discharged (`kappaOneZero_latI`, `Final.hg₂`, `g₃_lemniscatic_isAlgebraic`, `cmMulLogE_latI`). It is Theorem 4.12(3) for `E_i` with `Ω = ϖ`; other periods are covered by `thmSE0_paper`. There is no `E_ρ` wrapper; it would need `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`, the project's standing residual hypothesis. Optional: add `thmSE0_omegaRho` with `hg₃'` |
| 15 | MINOR (docs) | 4, `thmSE0_varpi_Ltilde` vs Cor. 4.13 | This is Cor. 4.13 at `t = cπ/ϖ²` with the independence of `ϖ, u₁, u₂` assumed. The Corollary assumes only that `u₁, u₂` are independent, and excludes `ϖ ∈ ℚ̄u₁ + ℚ̄u₂` by Lemma SE0 (`η ∉ 𝓛̃_E`): if `ϖ` were in that span, `tϖ = cπ/ϖ` would lie in `𝓛̃_E`. Lean has only `η₀/Ω ∉ ℚ̄` (#16). The `1/t` case (`ϖ²/π`) and the `℘`-sentence (Masser) are not formalised. The docstring states the extra hypothesis accurately. The module docstring l. 36–37 says "the corresponding case of Corollary SE4 … under the independence of `ϖ, u₁, u₂`", which is accurate too. Optional fix that removes the hypothesis: prove `π/ϖ ∉ LtildeE lemniscatic` from `LSG.W88.hypStdVecCM_eOne` (`G_a × E^♮ × E^N`), the paper's proof of Lemma SE0 (third clause), with the same adapted-basis lifting as `thmSE0`. Do not cite `thmSE0_varpi_Ltilde` as the full Cor. 4.13 |
| 16 | OK | 5, `transcendental_eta_div_omega` | The statement: `κ₁ = 0` and algebraic invariants imply `η₀/Ω` transcendental. It is true: `η₀/Ω = 2πi/((α − ᾱ)Ω²)`, and `π`, `Ω` are algebraically independent (Chudnovsky). Proof: `gmStdVec 0 0 (fun _ : Fin 1 => L.pp) (1)` is `E^♮`; `V = W = ℂ(1, β)` is `ℚ̄`-rational if `β ∈ ℚ̄`; `y = (Ω, η₀) = Ω(1, β) ∈ V`; `y ∈ LamV` since `η₀ − ζ(Ω) = 0` (`zeta_omega`). Then `m = 1` and `d − 1 − t = 0`, so (5.4) reads `1 > 0`. The conclusion is a nonzero `H.tan ⊂ V`. If `Γ ≠ 0`, `Γ ⊂ 0 × ℂ` gives `(0, s)` with `s ≠ 0`, not in `V`. If `Γ = 0`, then `(λ, 0) ∈ T(B^♮)` with `λ ≠ 0`, so `λβ = 0`, so `β = 0`, so `η₀ = 0`, contradicting Legendre. Sound. **No circularity:** `hypStdVecCM`'s signature has no transcendence input, and its axioms are standard. `transcendental_pi_div_varpi_sq` is the instance `latI`, with `η₀/ω = (π/ϖ)/ϖ` (`div_div`, `sq`). It is the part of Lemma SE0 that the proof uses (`t ∉ ℚ̄`), and the docstring says so |
| 17 | OK | 6, axioms | see `AxSE0.out`. `thmSE0_varpi`, `thmSE0_paper` and `transcendental_pi_div_varpi_sq` depend on `[propext, Classical.choice, Quot.sound]`. So do `thmSE0_varpi_Ltilde`, `thmSE0_of_cm`, `transcendental_eta_div_omega`, `thm11KappaSE0_uncond`, `uniform_SE0`, `hyperplaneKappa_gmESV`, `hypStdVec_cm`, `AbVar.thmSE0`, `AbVar.frameX0_false` and `LSG.W88.hypStdVecCM`. `grep` finds no `sorry`/`axiom`/`admit`/`native_decide` in the four new files |
| 18 | MINOR (docs) | `TRUST.md` l. 163; `Waldschmidt.lean` l. 12–14; paper Status line | `TRUST.md`'s Theorem 4.12 row still says "SE♮, SE₀ not formalised". The instance list in `Waldschmidt.lean` omits `AbVar.Thm11KappaSE0` (and `Thm11KappaSE`, `REFEREE_HYP_SE` #17). The paper's Status line (l. 1612–1614) lists (3) as `\LabC{}` only. Fix: add a TRUST row "Theorem 4.12(3) (SE₀): `Bridge.thmSE0_paper` unconditional for `j ∈ {0, 1728}` (κ₁ = 0, algebraic invariants, `CMMulLogE`); `Bridge.thmSE0_varpi`: no hypotheses; Cor. 4.13 only at `cπ/ϖ²` with `ϖ ∉ ℚ̄u₁ + ℚ̄u₂` assumed; via `lean_lsg` `hypStdVecCM`". Extend the instance list. The paper owner may upgrade the Status of (3) for `E_i` to Lean-checked (with the scope of #13) |
| 19 | COSMETIC | `Bridge/SE0.lean` l. 26 | "`T(B^♮) = t × t̄` for `κ₁ = 0`" is loose: `T(B^♮) = {(x, y) : x ∈ t, y ∈ span_ℂ{η(λ) : λ ∈ t ∩ Λ}}`, and the second factor is `η₀·conj(t ∩ Λ/Ω)⊗ℂ`, not `t̄`. Suggest "`T(B^♮) ⊇ (t ∩ Λ, 0)` and `(0, η(t ∩ Λ))`". The proof uses only those two facts |

## Details

### 1. Why the blocks of one curve cannot cancel (#8)

The worry: all three blocks are `E`, so `Hom(E, E) = 𝒪 ≠ 0`, and abelian subvarieties `B ⊂ E^{3r}` mixing the blocks
exist, such as the antidiagonal between block 2 and block 3. In Theorem SE with `E ~ E'` this killed the hypothesis
(`REFEREE_HYP_SE` #7). Here it does not, for two reasons:
* `μ₁` and `μ₂` read blocks 1 and 2 only, and block 3 enters `Ψ''` only through the fibre `s₂ = Σγ_j w_{b3 j}`.
* For a lattice point `λ ∈ t = T(B)`, `T(B^♮)` contains `(λ, η(λ))` and `(αλ, ᾱη(λ))`, hence `(0, (α − ᾱ)η(λ))`. Both
  the pure base vector `(λ, 0)` and the pure fibre vector `(0, η(λ))` therefore lie in `T(B^♮)`.

The two test vectors `x₁`, `x₂` thus separate "base of blocks 1, 2" from "fibre of block 3". The antidiagonal
`{(0, P, −P)}` has `x₁ = (0, λ, −λ)/Ω` with `Ψ''(x₁) = (0, μ₂(0, λ)/Ω) ≠ 0`, so it is not in `V` unless `μ₂` kills it,
which `k`-independence of `γ` forbids.

This is a Lean theorem (`uniform_SE0`), so no counterexample to `Thm11KappaSE0` exists. The paper's sentence "(this also
covers the mixed subgroups between the three `E`-factors when `X = E`)" is confirmed.

### 2. `κ₁ = 0` means `j ∈ {0, 1728}` (#13) [Proved, `KappaUnit.lean`]

The lemma is stated in `LSG.W88.MStarCopy`, which equals the `CM4E` notions through `adaptL` by `Iff.rfl`:
```lean
theorem kappaOneZero_unit (L : CMLattice) (hκ : KappaOneZero L) :
    L.p = -1 ∧ ∃ b : ℤ, (L.q : ℚ) = b ∧ (b = -1 ∨ b = 0 ∨ b = 1)
```
* `cmD` gives `ᾱ = α⁻¹`, i.e. `|α| = 1`.
* The imaginary part of `α² = p + qα` gives `q = 2 Re α`, and the real part then gives `p = −|α|² = −1`.
* `α·ω₂ ∈ Λ` gives `q ∈ ℤ`.
* `Im α > 0` gives `|Re α| < 1`, hence `|q| < 2`.

So `ℤ + ℤα` is `ℤ[i]` (`q = 0`) or `ℤ[ρ]` (`q = ±1`). The general Lean theorem is therefore a statement about `E_i`,
`E_ρ` and their `ℚ̄`-forms. That is still more than the `ϖ` wrapper: it covers `E_ρ` (with `hg₃` as a hypothesis) and
arbitrary periods. It is not the paper's "every CM curve".

### 3. What a full Cor. 4.13 at `π/ϖ²` would need (#15)

`thmSE0_varpi_Ltilde` + Lemma SE0(iii) (`π/ϖ ∉ ℚ̄ + ℚ̄𝓛_{E_i}`) ⇒ Cor. 4.13 at `t = cπ/ϖ²` for all `ℚ̄`-independent
`u₁, u₂ ∈ 𝓛̃_{E_i}`. The paper proves Lemma SE0(iii) by W88 on `G_a × E^r × E^♮`, i.e. the push-out of
`G_a × (E^♮)^{r+1}` along `e_last`. `lean_lsg` already proves `hypStdVecCM_eOne` for `G_a^{d₀} × E^♮ × E^m`, and the
`INTERFACE.md` example shows that it transfers to `lean_mstar` by `Iff.rfl`, as in #1. The lifting of
`ℚ̄`-coefficients to `ℚ`-combinations through an adapted basis is the machinery of `thmSE0` (`eLiftB`, `vLiftB`). This
is the natural next lemma.

## Suggested fixes (all documentation, plus two optional lemmas)

1. Scope of `κ₁ = 0` (#13): in `AbVar/SE0.lean` (module docstring l. 20–22, `thmSE0`), `Bridge/SE0.lean` (`thmSE0_of_cm`,
   `thmSE0_paper`) and `Gen/MGn.lean` l. 58, say that `KappaOneZero` forces `α` to be a unit, so `j(E_L) ∈ {0, 1728}`.
   Optionally promote `kappaOneZero_unit` from `reviews/checks/hypse0/KappaUnit.lean`.
2. `TRUST.md` and `Waldschmidt.lean` (#18): add the SE₀ row with its scope and residual hypotheses, and add
   `Thm11KappaSE0` (and `Thm11KappaSE`) to the instance list. The paper's Status line for (3) can cite the Lean
   theorems, restricted to `j ∈ {0, 1728}`.
3. Do not cite `thmSE0_varpi_Ltilde` as Cor. 4.13 itself (#15). Optional: prove `π/ϖ ∉ LtildeE lemniscatic` from
   `hypStdVecCM_eOne` and drop the extra hypothesis.
4. Optional: an `E_ρ` wrapper `thmSE0_omegaRho` with the hypothesis `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄` (#14).
5. Cosmetic (#19): reword "`T(B^♮) = t × t̄`".
