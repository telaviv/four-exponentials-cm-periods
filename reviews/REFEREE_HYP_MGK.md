# Referee report: `frame2_false_K`, the models `gmMGK` / `gmMGnK`, and the `K`-forms of Theorems MG and MG♮

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope (commit 144388f).**
* Read in full:
  - `CM4E/Gen/Frame2.lean`: `frame2_false_K`, and `frame2_false`, which is now a wrapper;
  - `CM4E/Gen/MGK.lean` and `CM4E/Gen/MGnK.lean`;
  - the `K`-form section of `CM4E/Final.lean` (`mg_K_varpi`, `mgn_K_varpi`).
* Read for context:
  - `CM4E/Waldschmidt.lean`;
  - `CM4E/Gen/Frame.lean` (`TF`, `tor1`, `tor2`, `qv`, `algF`, `perGen`, `gmF`);
  - `CM4E/Gen/MG.lean`, `MGn.lean`, `CMLattice.lean`, `Instances.lean`, `ThmM.lean` (`LogE`), `SMG.lean` (`torLift*`);
  - `CM4E/MX.lean` (`LogNat`) and the quasi-period files in `CM4E/Ext/Weierstrass/`;
  - TRUST.md.
* Paper: notation (l. 55–72); §`sec:MG`: thm:MG (l. 349–393), Remark rem:MG5d (l. 421–449), the fibre-values definition
  (l. 507–511), thm:MGn (l. 513–553), Remark rem:MGn5d (l. 568ff).
* Baseline: `REFEREE_HYP_GEN.md` (for `gmMG` and `gmMGn`) and `REFEREE_HYP_M.md` (for `LogE` and the elliptic-log
  generators).

**Process.** I edited no Lean file and ran no git command. My scratch files are in `reviews/checks/hypmgk/`:
* `AxMGK.lean` and `AxMGK.out`. These contain:
  - the axiom audit;
  - `#check` of the two `Final` wrappers;
  - `#print` of the models, the hypotheses, `KLog`, `KLogE`, `KFib`, `LogNat` and `LogE`;
  - `example`s checking that `d₁ = 2n` and `d₂ = finrank Qm` / `finrank Qn`;
  - `example`s checking that `(gmMGK L b).per = (gmMG L b).per` and `(gmMGnK L b).per = (gmMGn L b).per` (both `rfl`);
  - an `example` checking that `etaL latI m n = (m − n i)π/ϖ`.
  
  I ran it after the concurrent `lake build` finished. All oleans were newer than their sources, and every `example`
  compiled.
* `check.py` and `check.out`: numerics (mpmath, 50 digits) for κ₁, the `η₀`/`etaL` values, a κ₁ ≠ 0 control, and the
  count / Lemma U table.

**Axioms.** `frame2_false_K`, `frame2_false`, `mg_K`, `mgn_K`, `Final.mg_K_varpi` and `Final.mgn_K_varpi` depend only on
`propext`, `Classical.choice` and `Quot.sound`.

## Verdicts

* **Item 1 (`frame2_false_K`): CORRECT.** `K`-independence enters only through the rank `m = 3n`. In a `ℚ`-relation
  among the `3n` lifts, the coefficients of `2πi, y₀, y₁` in the first `Ψ''`-coordinate are `θᵀg_k` with `g_k` rational,
  and these lie in `K = span_ℚ θ`. The rest of the count (`κ ≥ n`, `d − 1 − t ∈ {0, 1}`, (5.4) from `d₂ < n`) and the
  exclusion step do not use independence. This matches the paper (l. 372–376 and l. 429–430).
* **Item 2 (`gmMGK`): CORRECT.** Enlarging `lam` by the images `[u e_i]` of elliptic logarithms keeps `lam ⊂ Λ(G'')`.
  The uniform `sub` holds for every connected subgroup. `per`, `alg`, `d₁` and `d₂` are those of `gmMG`, which is
  checked by `rfl`.
* **Item 3 (`gmMGnK`): CORRECT WITH NOTES.** For κ₁ = 0 the generators `([u e_i], θ_i w)` are images of logarithms of
  algebraic points of `(E^♮)^n`, so the model is sound. The κ₁ = 0 caveat is right and sufficient, and it holds for
  `latI` and `latRho` (κ₁ = 0 to 50 digits; it follows from `ζ(iz) = −iζ(z)` and `ζ(ρz) = ρ̄ζ(z)`). Every nonzero
  connected subgroup of `Q''` contains the fibre. Note: the caveat lives only in docstrings. `Thm11KappaMGnK` and
  `mgn_K` are stated for every `CMLattice`, and for κ₁ ≠ 0 the hypothesis is not a W88 instance, while `KFib` is not
  the paper's set of fibre values (#5, MINOR, latent).
* **Item 4 (statement fidelity; `Final` wrappers): CORRECT WITH NOTES.**
  - `mg_K` is Theorem MG for every `K ⊇ k(i, c)`.
  - `mgn_K` is Theorem MG♮ for every `K` with `[K : ℚ] ≥ 4` that contains Lean's `c`, which is the same as `i·c_paper ∈ K`.
  - In both cases this is exactly the case the paper's proofs reduce to.
  - Lean's `s = 1/(cω)` and the paper's `s = c'η*/π` agree up to `ℚ̄ˣ`, with an explicit dictionary.
  - `KLog` and `KLogE` match `K𝓛` and `K𝓛_E`. `KFib` matches the paper's fibre values when κ₁ = 0.
  - The wrappers discharge exactly `g₂`, `g₃` and the transcendence facts.
  - Notes: the Baker reduction to general `K` is not formalised (it is stated honestly in TRUST.md). The TRUST Lemma U
    list omits the two new models.

**No FATAL or MAJOR issue found.**

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `frame2_false_K` rank | `hli` uses `hind3` only with coefficients `dotL θ (rational)`, which lie in `span_ℚ θ = K` (`dot_rat_mem_span`). `K`-independence is enough. `frame2_false` (`ℚ̄`-independence) is a correct wrapper, since `K ⊂ ℚ̄` |
| 2 | OK | `frame2_false_K` count | `m = 3n`, `κ ≥ n`, `d₁ = 2n`, `d − 1 − t ∈ {0, 1}`. (5.4) is `3n > 2n + 2d₂ − κ`, which follows from `κ ≥ n` and `d₂ < n`. MGK: `d₂ = n/2`. MGnK: `d₂ = n/2 + 1 < n` for `n ≥ 4`. The exclusion uses `s ∉ ℚ̄` |
| 3 | OK | `gmMGK` vs `gmMG` | `lamMGK ⊇ lamGen perQm`, because `[ωe_j]` and `[αωe_j]` are `LogE` lattice points. The new `[u e_i]` with `u ∈ 𝓛_E` are images of `(0, …, u, …, 0) ∈ Λ(E^n)` under the `ℚ̄`-rational quotient `E^n → A''`. `per` and `d₂` are unchanged (`rfl`). The uniform `sub` contains every connected subgroup (§2) |
| 4 | OK | uniform `sub`, general fact | For `G'' = G^n/U` with `U` the largest connected subgroup having `T_U ⊂ ker Φ`, no nonzero connected `H ⊂ G''` has `T_H ⊂ ker Ψ''`: the preimage of `H` is connected and lies in `U`. `H` is defined over `ℚ̄`, so some algebraic vector of `T_H` has `Ψ'' ≠ 0`. So the soundness of the uniform `sub` *is* the paper's maximality of `U`. It is checked case by case below anyway |
| 5 | MINOR (latent) | `Thm11KappaMGnK`, `mgn_K`, `KFib` for κ₁ ≠ 0 | `LogNat L.pp (etaL L)` mixes two coordinate systems when κ₁ ≠ 0. Its lattice disjunct uses `etaL = η*` (forced by `legendre`, `check.out` [C]), which gives the periods in the conjugate-eigen coordinate `w*`. Its non-lattice disjunct uses the standard `ζ`, i.e. the coordinate `w = w* + κ₁z`. So either the periods or the `ζ`-generators are not logarithms, `gmMGnK` is unsound, and `KFib ≠` the paper's `K·(ζ*(u) + ℚ̄, η*(λ) + ℚ̄)`. Not reached: the only wrapper is `latI` (κ₁ = 0). Docstrings say so (`MGnK.lean:13, 22–26, 57`; TRUST l. 68, 127). Fix below |
| 6 | OK | κ₁ for the instances | κ₁ = `(η(αω) − ᾱη(ω))/((α − ᾱ)ω)`: `latI` −5·10⁻⁵², `latRho` 0. Controls: `ℤ[√−2]` 1.0575, `ℤ[(1+√−7)/2]` 0.9344. `η₀` (Lean) = `η(ω)` and `etaL m n = η(mω + nαω)` to 10⁻⁵⁰ for `latI` (`check.out` [A], [B]). Also a direct `ζ`-series check, to 4–5 digits |
| 7 | OK | `gmMGnK` generators | For κ₁ = 0, `w` is the conjugate-eigen coordinate (`[i]` acts as `(z, w) ↦ (iz, −iw)`, because `ζ(iz) = −iζ(z)`; likewise for `ρ`). `(u e_i, w e_i) ∈ Λ((E^♮)^n)` by `LogNat` (lattice: `(λ, η(λ)) +` fibre point `(0, a)`; otherwise `exp = (℘(u), ℘'(u), a)`). Its image under `T((E^♮)^n) → T(Q'')`, `(z, w) ↦ ([z], θᵀw)`, is `([u e_i], θ_i w)`. That is `lamMGnK` |
| 8 | OK | subgroups of `Q''` | Every nonzero connected `H ⊂ Q''` contains the fibre `F`. If `H` maps to 0 in `A''`, then `H ⊂ F ≅ G_a`, so `H = F`. Otherwise `H` contains the image of `B^♮_{S'}` with `S' ⊋ ker φ`, whose tangent space contains `([0], φ(s)) ≠ 0`. So `T_H ∩ T_F ≠ 0`, and `(H ∩ F)° = F`. Hence `(0, (0, 1)) ∈ T_H` is algebraic with `Ψ'' = (0, 1)` |
| 9 | OK | `d`-values, `per`, `alg` of both models | Identical to `gmMG` and `gmMGn` (REFEREE_HYP_GEN #4–#8; `rfl` checks in `AxMGK.lean`). `d₀ = 0`. `d₂ = n/2`, resp. `n/2 + 1`, exactly. `per = ℚ ⊗ Ker exp` |
| 10 | OK | Lemma U range | gmMGK: `2N = 5n − 2`, so the condition is `κ ≤ 3n − 2`. It fails only at `κ = 3n − 1`, where `V` contains a rational toric line and the conclusion holds outright (same `per` as `gmMG`; with the uniform `sub`, an algebraic `l` with `Ψ''l ≠ 0` suffices). gmMGnK: `2N = 5n`, always in range. In the applications `κ = n` exactly (a period has `Ψ''₁ ∈ 2πiK`, so by `K`-independence the data coefficients vanish) |
| 11 | OK | `mg_K` vs thm:MG | Lean proves "no `x₁, x₂ ∈ S_K` with `2πi, x₁, x₂` `K`-independent" for every `K = span_ℚ θ ⊇ k(i, c)`. Since `2πi ∈ S_K` there, this is `dim_K S_K ≤ 2`. `s = cω/π`, `c ∈ K`, covers `s = cΩ/π` for every period `Ω = mω`. This is the paper's post-reduction case (l. 358–359) |
| 12 | OK | `mgn_K` vs thm:MGn | `η*/π = 2i/((α − ᾱ)ω)` (Legendre), so `s_paper = c'η*/π = 1/(c_L ω)` with `c_L = (α − ᾱ)/(2ic')`. Hence `c_L ∈ K ⇔ ic' ∈ K`, which is exactly what the paper's proof uses (l. 536, "using `ic ∈ K`"). `2πi ∈ S` because `s·2πi = η₀(α − ᾱ)/c_L ∈ K·η₀`. `[K : ℚ] ≥ 4` (`hr : 2 ≤ r`) matches "`n ≥ 4`" |
| 13 | OK | `KLog`, `KLogE`, `KFib` | `KLog` is the `K`-span of `{ℓ : e^ℓ ∈ ℚ̄}` (`e^ℓ ≠ 0` always). `KLogE` is the `K`-span of `LogE`, which equals `𝓛_E` (`℘ ∈ ℚ̄ ⇒ ℘' ∈ ℚ̄`; lattice points included). For κ₁ = 0, `KFib` is `K·{η*(λ) + ℚ̄, ζ*(u) + ℚ̄ (u ∈ 𝓛_E ∖ Λ)}`, as at paper l. 510–511 |
| 14 | OK | `Final` wrappers | `mg_K_varpi` discharges `hg₂ := Final.hg₂`, `hg₃ := g₃_lemniscatic_isAlgebraic` and `hT := transcendental_varpi_div_pi`. `mgn_K_varpi` discharges `hg₂`, `hg₃` and `hT := Final.hT` (`ϖ ∉ ℚ̄`). Every other premise is part of the statement (`hb`, `c ∈ K`, `c ≠ 0`, `I ∈ K` / `2 ≤ r`, the data, independence) or is `hW` (`#check` in `AxMGK.out`) |
| 15 | NOTE | Baker reduction | Not formalised. TRUST l. 125 and l. 127 say so. The reduction is valid: `K𝓛 ≅ K ⊗_ℚ 𝓛` (Baker), so `K`-independence in `K𝓛` passes to `K' ⊇ K`, and `S_K ⊂ S_{K'}` |
| 16 | NIT | `MGnK.lean:88–90` | The docstring of `mgn_K` itself does not repeat "κ₁ = 0". The module docstring and the hypothesis docstring do |
| 17 | MINOR (docs) | TRUST.md l. 89–94 | The Lemma U list omits `gmMGK` (out of range only at `κ = 3n − 1`, where the conclusion is trivially true, as for `gmMG`) and `gmMGnK` (always in range) |
| 18 | COSMETIC | `MGK.lean:20–22` | "differs from `gmMG` only in…": add that `lamMGK` contains `gmMG`'s generators (periods as `LogE` lattice points), so the model is a pure enlargement. Add the one-line reason of #4 for the uniform `sub` in both docstrings |
| 19 | TRUST NOTE (inherited) | W88 §5d | Same regimes as `gmMG` (abelian `G₂`, `W ≠ 0`, `κ = n`) and `gmMGn` (non-semiabelian `G₂ = Q''`, every even `n ≥ 4`). There is no new failure point. The `exp(z, w) = (℘, ℘', w − ζ)` convention for `E^♮` is inherited from REFEREE_HYP_MX |

## Details

### 1. `frame2_false_K` [Proved by Lean; reading checked]

The only place where independence of `2πi, y₀, y₁` is used is `hli` (`Frame2.lean:192–215`).
* Apply the first coordinate of `Ψ''` to a `ℚ`-relation `Σ g_{k,h} g0(k, h) = 0`.
* By `hΨ1`, `Ψ''₁(g0(k, h)) = θ_h·(2πi, y₀, y₁)_k`. So `Σ_k (Σ_h g_{k,h}θ_h)·(2πi, y₀, y₁)_k = 0`.
* The coefficients `θᵀg_k` (`g_k ∈ ℚ^n`) lie in `span_ℚ θ = K` (`dot_rat_mem_span`, l. 157–162).
* So `hind3` (`K`-independence) gives `θᵀg_k = 0`, and `ℚ`-independence of `θ` gives `g_k = 0` (`dot_rat_eq_zero`).

The rest of the proof does not use independence:
* `κ ≥ n` comes from the `n` period lifts in `per`.
* `V'' = ker(Ψ''₂ − sΨ''₁)` is a hyperplane (`phiG_surjective`).
* `W = span wGen2 = ker Ψ''` is `ℚ̄`-rational, so `d − 1 − t ∈ {0, 1}`.
* (5.4) follows from `d₂ < n`.
* The exclusion uses only `s ∉ ℚ̄`.

This is the paper's rank argument "first coordinates `D θ_h·2πi, θ_hx_j` are `ℚ`-independent" (l. 429–430), which needs
exactly `K`-independence. `frame2_false` derives `K`-independence from `ℚ̄`-independence (`K ⊂ ℚ̄`), so the earlier users
(SMG, MG13) are unaffected.

### 2. `gmMGK` [Proved, modulo standard facts on CM abelian varieties]

Here `G'' = G_m^{2n} × A''`, `A'' = E^n/B_{ker ψ}`, and `Ψ''((x, y), [z]) = (θᵀx, θᵀy + θᵀz)` (`gmF2` with `μ = 0`,
`λ = lamM`). This is the same `Ψ''` as `gmF`/`gmMG`.

* **`lam`.**
  - `tor1`/`tor2` slots with `e^x ∈ ℚ̄` are logarithms in `G_m^{2n}`.
  - `qv [u e_i]` with `u ∈ 𝓛_E` (`LogE L.pp u`) is the image of `(0, …, u, …, 0) ∈ Λ(E^n)`. Its exponential is the image
    of an algebraic point of `E^n` under the `ℚ̄`-rational quotient map, so it lies in `A''(ℚ̄)`. This is the same fact as
    `eSlot` in REFEREE_HYP_M §3.
  - `Λ(G'')` is a `ℚ`-space (division points of algebraic points are algebraic), so `span_ℚ lamMGK ⊂ Λ(G'')`.
  - The old generators `qv '' perQm` are the case `u = ω`, `αω` (lattice points), so `lam(gmMG) ⊂ lam(gmMGK)`.
* **`per`, `alg`, `d₁`, `d₂`.**
  - `per` is literally `gmMG`'s (`rfl`): `2πi` toric slots plus `[ωe_j]` and `[αωe_j]`, which equals `ℚ ⊗ Ker exp_{G''}`,
    of dimension `3n`.
  - `alg = algF algQm` is the `ℚ̄`-structure.
  - `d₁ = 2n`, and `d₂ = finrank Qm = n/2` exactly (REFEREE_HYP_GEN #7, REFEREE_HYP_M #6). `d₀ = 0`.
* **`sub` (uniform).** Connected subgroups are products `T_L × B` (Goursat; torus versus abelian variety).
  - If `T_L ≠ 0`, a rational `l = (l₁, l₂) ≠ 0` gives `Ψ''(l, 0) = (θᵀl₁, θᵀl₂) ≠ 0`, by `ℚ`-independence of `θ`.
  - If `B ≠ 0`, it comes from a `k`-subspace `S' ⊋ ker ψ`. For `s ∈ S' ∖ ker ψ` (algebraic), `Ψ''(0, [s]) = (0, ψ(s)) ≠ 0`.
  
  Both vectors lie in `T_{T_L × B}`. The switch from `gmMG`'s product-form `sub` to the uniform one is therefore
  harmless: both families contain every connected subgroup, and that is all soundness needs.
* **General principle (#4).** By construction, `U` is the largest connected subgroup of `G^n` with `T_U ⊂ ker Φ`, and
  `Ψ''` is induced by `Φ`. So a connected `H ⊂ G''` with `T_H ⊂ ker Ψ''` has connected preimage `H̃` (since `U` is
  connected) with `T_{H̃} ⊂ ker Φ`, hence `H̃ ⊂ U` and `H = 0`. A `ℚ̄`-subgroup with `T_H ⊄ ker Ψ''` has an algebraic
  spanning vector outside `ker Ψ''`. So the uniform `sub` is sound exactly when the paper's maximality claim for `U`
  holds. This makes the case checks above (and §3) consequences of the paper's group analysis.
* **Falsification attempt.** For `T_H ⊂ ker Ψ'' = {θᵀx = 0, θᵀy + θᵀz = 0}`, products force each factor into
  `ker Ψ''`. A rational `l` forces `l = 0`, and `B` forces `ψ|_{S'} = 0`, so `B = 0`. A diagonal between `G_m^{2n}` and
  `A''` would be the graph of a homomorphism between a subtorus and an abelian subvariety, which is 0. **None exists.**

### 3. `gmMGnK` and the κ₁ caveat [Proved for κ₁ = 0; Numerical for the instances]

**Coordinates.** `LogNat` uses `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))`. Its periods are `(λ, η(λ))`, where `η` is the
quasi-period of the standard `ζ`. Write `η = η* + κ₁·id` with `η*(aλ) = āη*(λ)`.

* The model's `Q''`-coordinates (`MGn.lean`; REFEREE_HYP_GEN #4) are `([z], θᵀw*)`, in the conjugate-eigen fibre
  coordinate `w* = w − κ₁z`.
* `perQn` uses `θ_jη₀` and `θ_jᾱη₀` with `η₀ = η*(ω)`. Lean's `legendre` field and `Im α > 0` force this for every
  lattice (`check.out` [C]: for `ℤ[√−2]`, `η₀ = 2.2214 = η(1) − κ₁`, while `η(1) = 3.2789`).

**When κ₁ = 0** (`ζ = ζ*`, `w = w*`):
* `LogNat`'s lattice disjunct is `(λ, η*(λ) + a) = (λ, η(λ)) + (0, a)`: a period plus the algebraic fibre point `(O, a)`.
* Its other disjunct is `(u, ζ(u) + a)` with `exp = (℘(u), ℘'(u), a)` algebraic.
* `[i]` (resp. `[ρ]`) acts on `T(E^♮)` as `diag(α, ᾱ)`: `exp(iz, −iw) = (−℘, i℘', −i(w − ζ))` is algebraic in
  `exp(z, w)`, since `ζ(iz) = −iζ(z)`. So `w` is the conjugate-eigen coordinate.
* Hence `(u e_i, w e_i) ∈ Λ((E^♮)^n)`, and its image `([u e_i], θᵀ(w e_i)) = ([u e_i], θ_i w)` lies in `Λ(Q'')`, since
  `U` is defined over `ℚ̄` (θ algebraic). These are exactly the `lamMGnK` generators.
* `fLift` and the period lifts `qh` are `ℚ`-combinations of them, the latter via `LogNat ω η₀`, lattice disjunct with
  `w − etaL 1 0 = 0`.

**When κ₁ ≠ 0** (#5):
* The lattice disjunct (`η*`) is right in `w*`-coordinates. The non-lattice disjunct (`ζ`) is right in `w`-coordinates.
  No single coordinate system makes both families logarithms.
* In `w*`-coordinates, the generator `([u e_i], θ_i ζ(u))` is off by `θ_iκ₁u`, which is not a logarithm, since its
  exponential is a fibre point with transcendental coordinate.
* So `gmMGnK L` is unsound, and `KFib` differs from the paper's fibre values `ζ*(u) + ℚ̄`.
* There is also a deeper obstruction: the Lean statement with `ζ` in place of `ζ*` is a different statement.
  - The natural group for it uses the form `θᵀw_std`, and the largest subgroup in its kernel is only a fibre hyperplane
    (`ψ(S) = φ(S) = 0 ⇒ S = 0`).
  - So `d₂ = n + 1`, and the count `3n > 3n + 2` fails.
  - Restricting the docstrings to κ₁ = 0 is therefore necessary, not cosmetic.
* **Sufficiency.** With κ₁ = 0, `η₀ = η(ω)` (from Legendre with `Im α > 0`), and the model is sound for every adapted
  basis. Nothing else is needed: `g₂, g₃ ∈ ℚ̄` is a premise, and the orientation is in the structure.

**The instances.**
* For `ϖℤ[i]` and `Ω_ρℤ[ρ]`, `αL = L` gives `ζ(αz) = α⁻¹ζ(z) = ᾱζ(z)`, hence `η(αλ) = ᾱη(λ)`, i.e. κ₁ = 0.
* Numerically (`check.out` [A], [B]):
  - κ₁(latI) = −5·10⁻⁵² and κ₁(latRho) = 0;
  - `|η₀ − η(ω)| ≤ 1.4·10⁻⁵²` for both lattices;
  - `|etaL m n − η(mω + nαω)| ≤ 10⁻⁵⁰` for `latI`;
  - a direct `ζ`-lattice-sum check of `η(ϖ) = π/ϖ` and `η(iϖ) = −iπ/ϖ`, to 4–5 digits.
* Controls: κ₁ = 1.0575 for `ℤ[√−2]` and 0.9344 for `ℤ[(1+√−7)/2]`. So the caveat really excludes lattices.

**Subgroups of `Q''` (#8).** Confirmed: every nonzero connected `H ⊂ Q''` contains `F`. So `(0, (0, 1)) ∈ T_H` is an
`algQn` vector with `Ψ'' = (0, 0 + 1) ≠ 0`. With the torus case as in §2 and Goursat (no common subquotient of a torus
and a subgroup of `Q''`), every connected subgroup of `G''` satisfies the uniform `sub`.

**Falsification attempt.** A connected subgroup inside `ker Ψ'' = {θᵀx = 0, θᵀy + σ = 0}` would be `T_L × H`.
* If `H ≠ 0`, its fibre vector gives `(0, 1)`.
* If `H = 0`, `L` rational forces `l = 0`.
* **None exists.**

A non-logarithm in `lam` exists only for κ₁ ≠ 0 (above).

### 4. Statement fidelity and wrappers

**MG.**
* Paper: for every `K ⊇ k`, `dim_K S_K ≤ 2`, where `S_K = {x ∈ K𝓛 : sx ∈ K𝓛 + K𝓛_E}` and `s = cΩ/π`. The proof
  enlarges `K` to contain `k(i, c)`.
* Lean (`mg_K`): for `K = span_ℚ θ ∋ i, c` (`K ⊇ k` is automatic from `IsAdaptedFieldBasis`), there are no
  `x₁, x₂ ∈ KLog` with `sx_j ∈ KLog + KLogE` and `2πi, x₁, x₂` `K`-independent.
* `2πi ∈ S_K` (`s·2πi = 2icω ∈ Kω ⊂ KLogE`). So "no such `x₁, x₂`" is equivalent to `dim_K S_K ≤ 2`: if the dimension
  were ≥ 3, extend `{2πi}`.
* Every number field `K ⊂ ℂ` with `K ⊇ k(i, c)` has an adapted basis (any `k`-basis `b`).
* `Ω = mω` with `m ∈ k` is covered by `c ↦ cm ∈ K`.

**MG♮.**
* By Legendre, `η*/π = 2i/((α − ᾱ)ω)`. So the paper's `s = c'η*/π` equals Lean's `1/(c_Lω)` with
  `c_L = (α − ᾱ)/(2ic') ∈ ℚ̄ˣ`. The two families `{s}` coincide as `c'` and `c_L` range over `ℚ̄ˣ`.
* Field condition: `c_L ∈ K ⇔ ic' ∈ K`, because `α − ᾱ ∈ k ⊂ K`. The paper's proof needs exactly `ic' ∈ K` (l. 536),
  so Lean's hypothesis is no stronger than the paper's normalisation `K ⊇ k(i, c')`.
* `2πi ∈ S` because `s·2πi = η₀(α − ᾱ)/c_L` and `η₀` is a fibre value.
* `KFib` equals the paper's `K·(fibre values)` for κ₁ = 0 (#13).
* `hr : 2 ≤ r` is "`n ≥ 4`".

**Wrappers (`Final.lean:297–320`).**
* Only `Ω = ϖ` is wrapped. That suffices for every curve with `j = 1728` (`c` absorbs `ℚ̄ˣ`).
* The discharged premises are exactly `g₂` (`Final.hg₂`), `g₃` (`g₃_lemniscatic_isAlgebraic`), and Schneider:
  - `ϖ/π ∉ ℚ̄` for MG;
  - `ϖ ∉ ℚ̄` for MG♮.
* No `Ω_ρ` wrapper exists, and none is claimed. `Gen.mg_K` and `Gen.mgn_K` cover `latRho` given `hg₂'` and `hg₃'`.

**Baker reduction (#15).** This is the only gap between "every `K ⊇ k`" and the Lean statements. It is honestly listed in
TRUST.md and is mathematically correct.

## Suggested fixes

1. **Make the κ₁ = 0 caveat a Lean premise (#5).** Define in `MGnK.lean`:
   ```lean
   def KappaOneZero (L : CMLattice) : Prop :=
     CM4E.Ext.Weierstrass.eta L.pp (L.α * L.ω) = starRingEnd ℂ L.α * CM4E.Ext.Weierstrass.eta L.pp L.ω
   ```
   and use it as follows:
   * Make `Thm11KappaMGnK L := KappaOneZero L → IsAlgebraic … → …`. The hypothesis is then a sound W88 instance for
     *every* `CMLattice`: for κ₁ ≠ 0 it is vacuous.
   * Add `(hκ : KappaOneZero L)` to `mgn_K`.
   * Discharge `hκ` for `latI` in `mgn_K_varpi`. Two routes:
     - Prove `ζ(iz) = −iζ(z)` like `zeta_neg`, via the `Equiv` `l ↦ il` on `lemniscatic.lattice`, and then
       `eta (iϖ) = −i·eta ϖ` from `zeta_add`.
     - Or leave `hκ` as a named classical input.
   
   With `Im α > 0`, `KappaOneZero` plus Ext's `legendre_of_im_pos` even proves `eta L.pp L.ω = L.η₀`, so the
   `Instances.lean` soundness fact becomes a theorem.

   Minimal alternative: keep the docstrings, add "κ₁ = 0" to the `mgn_K` docstring (#16), and state in the TRUST row
   that `Thm11KappaMGnK L` is *not* a W88 instance for κ₁ ≠ 0.
2. **TRUST.md l. 89–94 (#17).** Add: "For `gmMGK` (same `per` as `gmMG`) the out-of-range value `κ = 3n − 1` again forces
   a rational toric line into `V`; `gmMGnK` is always in range (`2N = 5n`)."
3. **Docstrings (#18).**
   * `MGK.lean:20–22`: "`lamMGK` contains `gmMG`'s generators (periods are `LogE` lattice points)".
   * In `Frame2.lean`'s `gmF2` docstring, add the one-line reason of #4: "the uniform `sub` is sound because `U` is the
     largest connected subgroup with `T_U ⊂ ker Φ`; the preimage of a connected `H` with `T_H ⊂ ker Ψ''` lies in `U`".

## Falsification attempts (none succeeded for the instances)

* **Connected subgroup in `ker Ψ''`.** Products force each factor in. The torus factor is excluded by `ℚ`-independence,
  the abelian factor by `ψ ≠ 0` on `S' ⊋ ker ψ`, and `Q''`-subgroups by containing the fibre. There are no diagonals
  (Goursat). The general argument is #4.
* **Non-logarithm in `lam`.** For `gmMGK`: none, since `LogE` points are images of `E^n(ℚ̄)` points. For `gmMGnK`: none
  when κ₁ = 0. For κ₁ ≠ 0, the `ζ`-generators (or the `η*`-periods) are non-logarithms (#5), but no theorem applies the
  hypothesis there.
* **`K`-independence too weak for the rank.** No: the coefficients are `θᵀ(rational) ∈ K`.
* **Inflated `κ` or undercounted `d₂`.** `per` and `d₂` are identical to the reviewed models (`rfl`), and `κ = n` exactly
  in the applications.
* **Lemma U.** In range except for `gmMGK` at `κ = 3n − 1`, where the conclusion is trivial.
* **Wrong `s` or field in MG♮.** The dictionary `c_L = (α − ᾱ)/(2ic')` matches both `s` and the field condition `ic' ∈ K`.
* **Hidden premises in wrappers.** The `#check` output shows exactly the statement premises plus `hW`.

## Verdict lines

* Item 1 (`frame2_false_K`, count with `K`-independence only): **CORRECT**.
* Item 2 (`gmMGK`: enlarged `lam` with elliptic logarithms, uniform `sub`, vs `gmMG`): **CORRECT** (cosmetic docstring
  notes only).
* Item 3 (`gmMGnK`: generators `([u e_i], θ_i w)`, κ₁ = 0 caveat, fibre-containment of subgroups): **CORRECT WITH NOTES**.
  The model is sound for κ₁ = 0, the caveat is right and sufficient, and κ₁ = 0 holds for `latI` and `latRho`. The caveat
  is docstring-only, so `Thm11KappaMGnK`/`mgn_K` for κ₁ ≠ 0 lattices are not W88 instances and not the paper's statement
  (MINOR, latent; fix: a `KappaOneZero` premise).
* Item 4 (statement fidelity of `mg_K`/`mgn_K` vs thm:MG/thm:MGn; `KLog`, `KLogE`, `KFib`; `Final` wrappers):
  **CORRECT WITH NOTES** (exactly the paper's post-reduction case, `s` agrees up to `ℚ̄ˣ` with matching field condition,
  wrappers discharge only `g₂`, `g₃` and Schneider; the Baker reduction is not formalised, as TRUST says; the TRUST Lemma U
  list omits the new models).
