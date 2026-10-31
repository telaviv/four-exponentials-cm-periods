# Referee report: the twisted model `gmXP`, `Thm11KappaMXP`, Proposition D′ (`mxP_K`) and Corollary deg2 (i)

Referee: adversarial AI reviewer (Claude), 2026-10-30.

**Scope.**
* In full: `CM4E/Gen/MXP.lean`, `CM4E/Gen/Deg2.lean` (`WuestholzSix`, `deg2_i`,
  `transcendental_omegaRho_div_varpi_of_six`), and the wrappers `Final.mxP_K` and `Final.deg2_i`.
* For context: `CM4E/Waldschmidt.lean`, `CM4E/MX.lean`, `CM4E/Lattice.lean`, `CM4E/Gen/Basis.lean`,
  `BasisExists.lean` (statement of `exists_adapted_basis`), `CMLattice.lean` (`coordsA`), the `MXGen.lean` docstring and
  helpers, and `Ext/Weierstrass/ZetaDef.lean`.
* Paper: §`sec:MXP` (Theorem MX′, Proposition D′, l. 868–907), §`sec:deg2` (Cor. deg2, l. 917–960), Lemma K, and
  Theorem `thm:W88k` with the Lemma U list (l. 243–252).
* Format and baseline: `reviews/REFEREE_HYP_MXG.md`.

**Process.** No project file other than this report and `reviews/checks/hypmxp/` was edited, and no git command was
run. The scratch files are:
* `reviews/checks/hypmxp/check_mxp.py` and `check_mxp.out`: numerics (mpmath, 60–200 digits) and sympy identities;
* `reviews/checks/hypmxp/AxMXP.lean` and `AxMXP.out`: the axiom audit.

## Verdicts

* **Item 1 (`gmXP`, `Thm11KappaMXP`, `exists_adapted_basis_three`): CORRECT.** The model is sound for every adapted
  basis, so `Thm11KappaMXP` is a true consequence of W88 §5d, (5.4). Soundness needs only that `θ` is algebraic and
  `ℚ`-independent: neither `ρ ∈ K` nor `r ≥ 3` is needed. Only cosmetic docstring issues were found.
* **Item 2 (`mxP_K` vs. the paper): CORRECT WITH NOTES.** It is a faithful *weakening* of Prop. D′: one element
  `v ∈ Ψ'(Λ(G))`, first coordinate only, and `ℚ̄` in place of `K`. The variables are paired as in thm:MXP. The count
  and the exclusion are those of the paper's sketch. One MINOR note on the paper: its sketch does not say that the
  `m = 3n` independence uses `η_ρ/ϖ ∉ K` (Cor. Γ). Lean makes this explicit.
* **Item 3 (`deg2_i`, `WuestholzSix`, wrappers): CORRECT WITH NOTES.**
  - The gap in the paper is **confirmed**: its proof of cor:deg2(i) omits the case `c₀ = 0`, `c₃ ≠ 0`. The gap is
    MINOR, because that case follows in one line from the six-independence alone, without D′ (#9).
  - Lean's treatment of the case through D′ is correct.
  - `WuestholzSix` is a true consequence of Wüstholz's theorem.
  - The `LogNat` inputs are correct: the quasi-periods were checked numerically against the Lean `ζ` series.
  - The wrappers discharge exactly `hg₂`, `hg₃`.

**Axioms.** I ran `lake env lean reviews/checks/hypmxp/AxMXP.lean` (20 s; oleans newer than the sources). Six
declarations use only `propext`, `Classical.choice`, `Quot.sound`: `Gen.exists_adapted_basis_three`, `Gen.mxP_K`,
`Final.mxP_K`, `Gen.deg2_i`, `Final.deg2_i` and `Gen.transcendental_omegaRho_div_varpi_of_six`. `CM4E/` contains no
`sorry`, `axiom` or `native_decide`.

**No FATAL or MAJOR issue was found.**

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `alg`, `lam` | `algXP` is the quotient `ℚ̄`-structure of `G'' = G^n/U'`. `gPI`, `gPR`, `gPA` are the images of copy-`h` logarithms, so `span_ℚ lamGenP ⊂ Λ(G'')` |
| 2 | OK | `per` (incl. `HP2`) | `GP1`, `GP2`, `HP1`, `HP2` are images of genuine periods `(λ, η(λ))`; `η(ρΩ_ρ) = ρ̄η_ρ` was verified to 1e-9 against the direct `ζ` lattice sum. `perXP = ℚ ⊗ Ker exp_{G''}` (rank `4n`), so κ is never inflated |
| 3 | OK | uniform `sub` | no nonzero connected `H ⊂ G''` has `T_H ⊂ ker Ψ''`, for **every** adapted `θ` (needs only `θ ⊂ ℚ̄` and `ℚ`-independence) |
| 4 | OK | `d₁ = 0`, `d₂ = 2n+2` | correct (`G''` is anti-affine). Moreover `d₁ + 2d₂ = 2d` is the largest value `2d − 2d₀ − d₁` can take, so the Lean premise is the strongest possible whatever `d₀, d₁` are: this field cannot be a soundness risk |
| 5 | OK | count in `mxP_K` | `m = 3n`, `κ ≥ 2n`, `t = 2n`, `d − 1 − t = 1`; `3n > 4n + 4 − κ` holds since `n = 2r ≥ 6`. Lemma U range: `2N = 4n+2 ≥ κ` for every instance (`κ ≤ 4n`) |
| 6 | OK | `exists_adapted_basis_three` | `K ⊇ ℚ(i, √3, √2, S)`, and `1, i, √3, i√3, √2` are `ℚ`-independent, so `2r ≥ 5`, i.e. `r ≥ 3`. (In fact `8 ∣ n`, so `n ≥ 8` as in the paper) |
| 7 | OK | `mxP_K` vs thm:MXP / D′ | hypotheses identical; pairing `z(X)+w(Y)+a` / `w(X)+z(Y)+c` as in the paper; conclusion = first coordinate of D′ with `K ⊂ ℚ̄` |
| 8 | MINOR (paper) | D′ sketch, l. 893–896 | "`m = 3n`" needs `w₁', w₂'` to be `K`-independent, i.e. `η_ρ/ϖ ∉ K`, which is Cor. Γ. The paper names only `Ω_ρ/ϖ ∉ ℚ̄` (exclusion step). Lean uses both (`hΓ` gives `hηv`, plus `hM`) |
| 9 | MINOR (paper) | cor:deg2(i), l. 935 | **gap confirmed**: "suppose `π = AϖΩ_ρ + Bϖ + CΩ_ρ`" divides by the `π`-coefficient. The case `c₀ = 0`, `c₃ ≠ 0` is not treated. One-line fix below |
| 10 | OK | `deg2_i`, case `c₀ ≠ 0` | the paper's choice (`β = A`, `X = (ϖ, η_i)`, `Y = 0`, `a = C/A`, `b = −B`), closed with D′ + `WuestholzSix` instead of the full MX′ conclusion. Valid, and simpler than the paper |
| 11 | OK | `deg2_i`, case `c₀ = 0` | `β = √3/2`, `X = (ϖ, η_i)`, `Y = (Ω_ρ, η_ρ)`, `a = 2kc₂/√3`, `c = −kc₁`, `k = (√3/2 − 1)/c₃`. `hrelP` is exactly `k·(relation)` (sympy). D′ then forces `a = 0`, hence `c₂ = 0`, hence `c₃ = 0`. Correct |
| 12 | OK | `WuestholzSix` | true: Wüstholz on `E_i^♮ × E_ρ^♮ × G_m × G_a` at `u = (ϖ, η_i; Ω_ρ, η_ρ; 2πi; 1)` (derivation below). [Lit] Baker–Wüstholz, *Logarithmic Forms and Diophantine Geometry*, §6.2 (dimension `2 + 2·#CM classes`) |
| 13 | OK | `LogNat` inputs | `X = (ϖ, π/ϖ)` and `Y = (Ω_ρ, η_ρ)` are lattice points with `w = η(λ)` exactly. Legendre relations and `etaRho_mul` hold to 1e-60; `η` agrees with the Lean `ζ` series to 1e-9; `g₂, g₃ = (4, 0)`, `(0, 4)` |
| 14 | OK | `Final.mxP_K`, `Final.deg2_i` | discharge only `hg₂`, `hg₃` (lemniscatic); `hg₂'`, `hg₃'`, `hΓ`, `hM` / `h6` stay explicit |
| 15 | NIT | `Deg2.lean:160`, `Final.lean:227ff` | `hΓ` is redundant in `deg2_i` (and `deg2_ii`): it follows from `WuestholzSix`, as `ϖ = (√3α/2)η_ρ` if `ϖΩ_ρ/π = α` |
| 16 | NIT | `Deg2.lean:179–232` | the `c₀ = 0` branch could be replaced by a direct `six_zero` call (#9), with no use of `hW` in that branch. Optional |
| 17 | COSMETIC | `MXP.lean:13`, `:20` | `U'` should say `z_i = z_ρ = 0` ("vector subgroup"). "by Lemma K" is literally applicable only when `ρ ∈ K`. Since `Thm11KappaMXP` quantifies over all `K ∋ i`, cite the direct `m = u + ωv` argument (MXGen docstring item 4 / REFEREE_HYP_MXG #3) |
| 18 | MINOR (docs) | `TRUST.md` | stale. §2 lacks `Final.mxP_K` and `Final.deg2_i`. §3 lacks a row for `Gen.Thm11KappaMXP`. §5 l. 116 and l. 118 still say ✗ for MX′/D′ and deg2(i). l. 78 should add `gmXP` to the models whose Lemma U range covers every configuration, and l. 84 should add "MX′: `3n > 4n + 4`" |
| 19 | COSMETIC | `Waldschmidt.lean:12–13`; `Final.lean:28–32` | the instance list omits `Thm11KappaMXP`, and the "What remains assumed" paragraph omits `WuestholzSix` |
| 20 | NIT (paper) | D′ sketch, l. 889–891 | the "canonical lift" sentence by itself does not cover partial lifts. The two-case argument on `G''` (#3) closes this. The conclusion is right |
| 21 | TRUST NOTE (inherited) | W88 §5d | as REFEREE_HYP_MXG #18: Lemma U is checked only for the first application of Thm 4.1 inside §5d. This model has `d₀ = 0`, `W ≠ 0`, `κ > 0` and a non-semiabelian `G₂` |

## Details

### 1–4. Soundness of `gmXP` [Proved, modulo standard facts on `E^♮`]

**The group.**
* `G = E_i^♮ × E_ρ^♮ × G_a²`. Per copy `h`, the tangent coordinates are `(z_i, w_i, z_ρ, w_ρ, a₁, a₂)`, with
  `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))` on each `E^♮`.
* These coordinates are `ℚ̄`-rational: near `O`, `−2x/y = z + O(z⁵)`, and `w − ζ(z) + ℘'(z)/(2℘(z)) = w + O(z³)`,
  both with `ℚ̄`-coefficient series (REFEREE_HYP_MX #2).
* `U' = {z_i = z_ρ = 0, θᵀ(w_ρ + a₁) = 0, θᵀ(w_i + a₂) = 0} ⊂ G^n` is a connected vector group over `ℚ̄`, of dimension
  `4n − 2`.
* The map `G^n → G_i × G_ρ`, `(x_i, x_ρ, a₁, a₂) ↦ (push(x_i) + θᵀa₂, push(x_ρ) + θᵀa₁)`, is onto with kernel `U'`.
  Here `G_i` (resp. `G_ρ`) is the push-out of `(E_i^n)^♮` (resp. `(E_ρ^n)^♮`) along `θᵀ : G_a^n → G_a`. So
  `G'' ≅ G_i × G_ρ`, with fibre coordinates `s₂` resp. `s₁`, and `dim G'' = 2n + 2`.
* `Φ' = Ψ'∘p_θ` descends to `Ψ'' = (θᵀz_i + s₁, θᵀz_ρ + s₂)`. This is `psiP1`, `psiP2`.
* `algXP` (all four blocks algebraic) is the quotient `ℚ̄`-structure. The forms `z_i`, `z_ρ`, `s₁`, `s₂` are
  `ℚ̄`-linear and independent.

**`lam`.**
* Images of copy-`h` vectors:
  - `(z, w) ∈ T(E_i^♮)` gives `(z e_h, 0, 0, θ_h w)` (`gPI`; the fibre of `E_i^♮` feeds `s₂`);
  - `(z, w) ∈ T(E_ρ^♮)` gives `(0, z e_h, θ_h w, 0)` (`gPR`; the fibre feeds `s₁`);
  - `(a, c) ∈ ℚ̄²` gives `(0, 0, θ_h a, θ_h c)` (`gPA`).
* `Λ(G'')` contains the image of `Λ(G^n)`, and it is a `ℚ`-space (division points of algebraic points are algebraic).
* `LogNat` = `Λ(E^♮)` (REFEREE_HYP_MX #1; lattice points with an algebraic fibre offset included).

**`per`.**
* `GP1 = (ϖ, η(ϖ))` and `GP2 = (iϖ, η(iϖ))`, with `η(iϖ) = −iπ/ϖ`.
* `HP1 = (Ω_ρ, η_ρ)` and `HP2 = (ρΩ_ρ, η(ρΩ_ρ))`. Here `η(ρΩ_ρ) = ρ̄η_ρ`, by `ζ(ρz) = ρ̄ζ(z)` or equivalently by
  Legendre: `η₂ = (η₁ω₂ − 2πi)/ω₁ = (ρ − i√3)η_ρ = ρ̄η_ρ`.
* Numerically, the direct `ζ` sum gives `−0.7468342001 − 1.2935547808i`, against `−0.7468342002 − 1.2935547796i` from
  Lean's formula (Richardson-extrapolated lattice sum; diff 1.2e-9).
* `U'` is connected, so `Ker exp_{G''}` is the image of `Ker exp_{G^n}`, which is spanned by these four vectors per
  copy. Hence `perXP = ℚ ⊗ Ker exp_{G''}` (rank `4n`), and `κ_Lean = κ_W88`.

**`sub` (the crucial point).** Let `H ⊂ G''` be connected and nonzero. I show `T_H ⊄ ker Ψ''`. Since `T_H` and
`Ψ''` are `ℚ̄`-rational, `T_H` then contains an `algXP` vector `x` with `Ψ''x ≠ 0`, which is `sub`.
* **Case 1: `H` meets the fibre `F = G_a²` in positive dimension.** Then `T_H ∋ (0, 0, s₁, s₂) ≠ 0`, and its image is
  `Ψ'' = (s₁, s₂) ≠ 0`.
* **Case 2: otherwise.** Then `H ∩ F = 0`, because `F(ℂ)` is torsion-free.
  - So `H ≅ B = B_i × B_ρ ⊂ E_i^n × E_ρ^n`; it is a product because the curves are non-isogenous.
  - `H` is a section of `G''|_B`. Its `G_ρ`-component over `B_i × 0` is a homomorphism `B_i → G_a`, hence 0, and
    likewise for the other one. So `H = H_i × H_ρ`, with `H_i` a splitting of `G_i|_{B_i}`.
  - CM gives `T_{B_i} = W ⊗_k ℂ` for a `k`-subspace `W ⊂ k^n`, with `k = ℚ(i)`.
  - `G_i|_{B_i}` is `(T_{B_i} × ℂ)/{(λ, θᵀη(λ))}`. On `ϖℤ[i]`, `η(λ) = (π/ϖ²)·λ̄` is *purely antilinear* (checked: it
    gives `π/ϖ` and `−iπ/ϖ` on `ϖ`, `iϖ`). So the ℝ-linear extension of the cocycle is `z ↦ (π/ϖ²)θᵀz̄`, which is
    ℂ-antilinear on `T_{B_i}`.
  - A splitting exists iff this extension is ℂ-linear, i.e. iff it vanishes: `φ(m) = θᵀm̄ = 0` for all `m ∈ W`. The
    splitting is then unique (`Hom(B, G_a) = 0`), with `s₂ = 0`.
  - So `T_{H_i} = T_{B_i} × 0`, and `T_H ⊂ ker Ψ''` adds `ψ(m) = θᵀm = 0`.
  - With `m = u + iv` (`u, v ∈ ℚ^n`), `ψ − φ = 2iθᵀv` gives `v = 0`, and then `θᵀu = 0` gives `u = 0`. So `B_i = 0`.
  - Likewise for `B_ρ`. There `η(λ) = (2π/(√3Ω_ρ²))λ̄`, `m = u + ρv`, and `ψ − φ = i√3θᵀv`. This step does **not**
    need `ρ ∈ K`.
* Hence `H = 0`. Equivalently, `U'` is the largest connected subgroup of `G^n` with tangent space in `ker Φ'`. This is
  the paper's claim, and the two cases above make the "canonical lift" sentence complete (#20).

**`d₁`, `d₂`.**
* `G_i` and `G_ρ` are quotients of the anti-affine groups `(E^n)^♮`, along the onto form `θᵀ`. So `G''` is
  anti-affine, and `d₀ = d₁ = 0`, `d₂ = 2n + 2 = d`.
* Independently of this, `d₁ + 2d₂ ≤ 2d` for every group, with equality iff `d₀ = d₁ = 0`. So Lean's `(5.4)` premise
  `m > (2d − κ)(d − 1 − t)` is the strongest possible, and an error in `d₀`, `d₁` could only weaken the hypothesis, not
  make it false (#4).

**Quantifier over adapted bases.** `Thm11KappaMXP` covers every `K ∋ i`, including `r = 1, 2` and `K ∌ √3`. All of
them are sound by the above. Only `θ ⊂ ℚ̄` (`hb.alg`, `I ∈ ℚ̄`) and `hb.indep` are used.

### 5–7. `mxP_K`

**Generators.** Three per copy:
* `P1'` with `Ψ'' = θ_h(ϖ, βΩ_ρ) = θ_h w₁'`;
* `P2'` with `Ψ'' = θ_h(η_ρ, β(2√3/3)π/ϖ) = θ_h w₂'`, using `2√3/3 = 2/√3` and `η_i = π/ϖ`;
* `DP` with `Ψ'' = θ_h(zX + wY + a, wX + zY + c)`.

**Lifts.**
* `liftPI` and `liftPR` are explicit `ℚ`-combinations of `GP*`, `HP*` (Lemma K made explicit). They need `x, y ∈ K`.
* `liftPR` divides by `ρ − ρ̄ = i√3 ∈ K`; this is why `r3 ∈ Kspan` is requested. All `Ψ''`-values are Lean-proved.
* As a check, `w₂' − (η_ρ/ϖ)w₁' = 0` to 1e-60.

**`V''`.**
* `V'' = ker(βΩ_ρΨ''₁ − ϖΨ''₂) = Ψ''⁻¹(ℂw₁')`, a hyperplane (`finrank_ker_phiP`).
* `P2' ∈ V''` uses `etaRho_mul`, and `DP ∈ V''` is `hrel`.
* `W = span{(e_j, 0, −θ_j, 0), (0, e_j, 0, −θ_j)} = ker Ψ''` is `ℚ̄`-rational and of dimension `2n`.

**Independence.**
* Applying `Ψ''₁` to a relation `Σ g·y = 0` gives `Aϖ + Bη_ρ + C(zX + wY + a) = 0`, with `A, B, C = θᵀ(g-blocks) ∈ K`.
* If `C ≠ 0`, this contradicts the negated conclusion. If `C = 0` and `B ≠ 0`, then `η_ρ/ϖ ∈ ℚ̄`, which contradicts
  `hΓ` (`ϖΩ_ρ/π = 2/(√3·η_ρ/ϖ)`). Otherwise `θ`-independence gives `g = 0`.
* The paper's sketch only says "for a hypothetical `v ∉ Kw₁' + Kw₂'` one has `m = 3n`". That silently needs
  `Kw₁' + Kw₂'` to be 2-dimensional, i.e. Cor. Γ (#8).

**Count.**
* `κ ≥ 2n`: the `2n` period lifts are independent and lie in `per`.
* (5.4) reads `3n > (0 + 2(2n+2) − κ)·(2n + 2 − 1 − 2n) = 4n + 4 − κ`. This holds since `4n + 4 − κ ≤ 2n + 4 < 3n`
  for `n ≥ 6`.
* If `X`, `Y` are periods and `a = c = 0`, then `κ = 3n`, which is still fine. In every instance `κ ≤ 4n ≤ 2N = 4n+2`,
  so the Lemma U range is never exceeded. The paper's "`4n+2 ≥ 2n`" is the `κ = 2n` case.

**Exclusion.** There is an algebraic `x ∈ S ⊂ V''` with `Ψ''x ≠ 0`. Then both coordinates are nonzero, and
`Ω_ρ/ϖ = Ψ''₂x/(βΨ''₁x) ∈ ℚ̄`, which contradicts `hM`. This is the paper's "V′ has no `ℚ̄`-rational point".

**Faithfulness.**
* Lean's hypotheses are exactly those of thm:MXP: `X ∈ Λ(E_i^♮)`, `Y ∈ Λ(E_ρ^♮)` via `LogNat`, `a, c ∈ ℚ̄`,
  `β ∈ ℚ̄ˣ`, and `(z(X)+w(Y)+a)·βΩ_ρ = (w(X)+z(Y)+b)·ϖ` (paper l. 880–882).
* The conclusion `zX + wY + a ∈ ℚ̄ϖ + ℚ̄η_ρ` is the first coordinate of D′ (`V' ∩ Ψ'(Λ_K) = Kw₁' + Kw₂'`), with
  `K ⊂ ℚ̄`. So it is a faithful specialisation.
* Lean builds `K ⊇ ℚ(i, √3, √2, β)` internally, so the paper's "`n ≥ 8`" holds there too (`8 ∣ n`). Lean only needs
  `n ≥ 6`.
* The second coordinate and the MX′ conclusion (`z(X) = z(Y) = 0`) are not formalised. TRUST.md §5 should say ◐
  for MX′ (#18).

**Torsion data (falsification attempt).** Take `X`, `Y` torsion, so `z(X) = pϖ`, `w(Y) = q̄η_ρ + alg`. Then `hrel`
forces the constant term to vanish and `v ∈ Kw₁' + Kw₂'`, given the deg2(i) independence. A genuine third direction
would need `|β|² = √3/2` with `β = q/p ∈ ℚ(i, ρ)`, which is impossible since `|q|²/|p|² ∈ ℚ`. So no counterexample
arises; the data are consistent with the conclusion.

### 9–11. `deg2_i` vs cor:deg2(i)

**The paper's case split.** The paper (l. 935) first excludes `c₃ = 0` by the six-independence. It then writes "so
suppose `π = AϖΩ_ρ + Bϖ + CΩ_ρ` with `A ≠ 0`", which divides by `c₀`. So **the case `c₀ = 0`, `c₃ ≠ 0` is omitted.**
I confirm the Lean docstring's claim (`Deg2.lean:16–18`).

**The fix (paper, one line) [Proved, sympy-checked].** If `c₀ = 0`, multiply `c₁ϖ + c₂Ω_ρ + c₃ϖΩ_ρ = 0` by
`π/(ϖΩ_ρ)` and use `π/ϖ = η_i` and `π/Ω_ρ = (√3/2)η_ρ`. This gives
`c₃π + c₂η_i + (√3/2)c₁η_ρ = 0`, so `c₁ = c₂ = c₃ = 0` by the six-independence. The case therefore needs neither
D′ nor MX′. In the paper's own words: the "equivalently" form `π, η_i, η_ρ, η_iη_ρ` has no `η_iη_ρ`-term when
`c₀ = 0`.

**Lean's `c₀ = 0` branch** is nevertheless correct.
* `hrelP − k·(c₁ϖ + c₂Ω + c₃ϖΩ) ≡ 0` symbolically, using `η_ρΩ_ρ = 2π/√3`.
* D′ gives `ϖ + η_ρ + a = xϖ + x'η_ρ`. Six-independence then gives `a = 0`, hence `c₂ = 0` (since `k ≠ 0`, because
  `√3 ≠ 2`). Then `ϖ(c₁ + c₃Ω_ρ) = 0` gives `c₃ = 0`, a contradiction.
* This is a heavier route than needed (#16), but sound.

**Lean's `c₀ ≠ 0` branch.**
* It uses the paper's instance. D′ gives `ϖ + C/A = xϖ + x'η_ρ`, so `C/A = 0` by six-independence.
* Then `hrelP` gives `π/ϖ − B = AΩ_ρ`, i.e. `η_i − B − AΩ_ρ = 0`, which contradicts six-independence (coefficient 1
  on `η_i`).
* The paper instead invokes the full MX′ conclusion (`z(X) = 0`). Lean's route avoids the unformalised "Conclusion"
  paragraph of MX′ and is preferable.

**`transcendental_omegaRho_div_varpi_of_six`.** `Ω_ρ/ϖ = α ∈ ℚ̄` gives `−αϖ + Ω_ρ = 0`, which contradicts
six-independence. Correct.

### 12. `WuestholzSix` is true [Proved modulo Wüstholz 1989]

**Set-up.**
* Let `G = E_i^♮ × E_ρ^♮ × G_m × G_a` and `u = ((ϖ, η_i), (Ω_ρ, η_ρ), 2πi, 1)`. Then `exp u = (0, 0, 1, 1) ∈ G(ℚ̄)`.
* A relation `c₀ + c₁π + c₂ϖ + c₃η_i + c₄Ω_ρ + c₅η_ρ = 0` is `L(u) = 0` for the `ℚ̄`-form
  `L = c₂z_i + c₃w_i + c₄z_ρ + c₅w_ρ + (c₁/2i)t + c₀s`.
* By Wüstholz, `L` vanishes on `T_H` for some connected `H` with `u ∈ T_H`. I show `H = G`.

**Projections.**
* The connected subgroups of `E^♮` are `0`, `F` and `E^♮` (a non-split extension). `(ϖ, η_i) ∉ T_F`, so `H` maps onto
  `E_i^♮`. Likewise onto `E_ρ^♮`, `G_m` and `G_a`.
* `H → E_i × E_ρ` is onto, since the curves are non-isogenous.
* Let `N = ker(H → E_i × E_ρ)° ⊂ F_i × F_ρ × G_m × G_a`, and write `N = N_m × N_a`.

**`N` is everything.**
* `N_m = G_m`. Otherwise `H → G_m` would factor through an abelian variety, up to isogeny.
* `N_a ⊇ F_i × F_ρ`. `H/N_a` is a splitting of the push-out of `(E_i × E_ρ)^♮ × G_a` along `G_a³ → G_a³/N_a`. By
  universality, that push-out splits only if `F_i × F_ρ ⊂ N_a`.
* `G_a ⊂ N_a`. Otherwise `H/N` would be the graph of a map `E_i × E_ρ → G_a`, which is 0, and this contradicts the
  surjection `H → G_a`.

So `H = G`, `L = 0` and all `c_k = 0`. The statement is also the case "two CM isogeny classes" of the standard
dimension formula for `span_ℚ̄{1, 2πi, ω_j, η_j}` [Lit].

**Numerics.** At 200 digits, PSLQ over `ℚ(√3)` with coefficients up to `10⁶` finds no relation among the six numbers.
An 80-digit PSLQ "hit" has residual `1.6e-60` at 200 digits, so it is spurious. PSLQ on `(π, ϖ, Ω_ρ, ϖΩ_ρ)` over
`ℚ(√3)` with coefficients up to `10¹⁰` finds none either [Numerical, sanity only].

### 13. `LogNat` inputs and normalisations [Numerical, 60 digits unless noted]

* **Constants.** `ϖ = 2.62205755429211981046…` and `Ω_ρ = 2.42865064788758161181…`.
* **Invariants.** By Eisenstein series, `g₂(ϖℤ[i]) = 4`, `g₃ = 0`, `g₂(Ω_ρℤ[ρ]) = 0`, `g₃ = 4`, to 1e-60. The direct
  lattice sums agree to 1e-5 (truncation).
* **Quasi-periods.** `η(ω₁) = π²E₂(τ)/(3ω₁)` equals `etaLem 1 0 = π/ϖ` and `etaRho = 2π/(√3Ω_ρ)` to 1e-60.
* **Legendre and `etaRho_mul`.** `η₁ω₂ − η₂ω₁ = 2πi` holds for both lattices with `η₂ = −iη_i`, resp. `ρ̄η_ρ`, to
  1e-60. `etaRho_mul` holds to 1e-60.
* **Independent check against Lean's `ζ`.** The Lean `ζ` is `Σ' (1/(z−l) + 1/l + z/l²)` (`ZetaDef.lean:36,64`).
  Direct truncated sums, Richardson-extrapolated, give `ζ(z₀ + λ) − ζ(z₀)` equal to the Lean quasi-period values for
  `λ = ϖ, iϖ, Ω_ρ, ρΩ_ρ`, to about 1e-9.
* **Conclusion.** `X = (ϖ, π/ϖ)` and `Y = (Ω_ρ, η_ρ)` are exactly the periods `(λ, η(λ))` (first disjunct of
  `LogNat`, offset 0).
* **Optional strengthening.** `Ext/Weierstrass/Legendre.lean` proves Legendre's relation in Lean. Together with
  `ζ(iz) = −iζ(z)` (resp. `ρ̄`), it could turn `etaLem` and `etaR` from stated values into proved facts.

### 14. Wrappers

* `Final.mxP_K` (`Final.lean:213`) and `Final.deg2_i` (`:227`) instantiate `hg₂ := Final.hg₂` and
  `hg₃ := g₃_lemniscatic_isAlgebraic`, and pass everything else through.
* The `#check` output in `AxMXP.out` shows the remaining hypotheses:
  - `Final.mxP_K`: `Thm11KappaMXP`, `hg₂'`, `hg₃'`, `hΓ`, `hM`;
  - `Final.deg2_i`: `Thm11KappaMXP`, `hg₂'`, `hg₃'`, `hΓ`, `WuestholzSix`.
* All of these are true (`hg₂'`, `hg₃'`: #13; `hΓ`, `hM`: Wüstholz, and both follow from `WuestholzSix`).

## Suggested fixes

1. **Paper, cor:deg2(i) (l. 935).** After "is excluded by that independence", insert: "A relation with zero
   coefficient on `π` becomes, after multiplication by `π/(ϖΩ_ρ)`, `c₃π + c₂η_i + (√3/2)c₁η_ρ = 0`, which is also
   excluded." (#9)
2. **Paper, D′ sketch (l. 893–896).** Add: "the `3n` lifts are `ℚ`-independent because `η_ρ/ϖ ∉ K` (Cor. Γ) and
   `v ∉ Kw₁' + Kw₂'`." (#8) Optionally, phrase the maximality of `U'` by the two-case argument on `G''` (#20).
3. **Paper.** Optionally, replace the proof of deg2(i) by Lean's route: D′, first coordinate, plus six-independence.
   It does not need the "Conclusion" paragraph of MX′.
4. **`MXP.lean` docstring (l. 13, 20).** Write `U' = {z_i = z_ρ = 0, θᵀ(w_ρ+a₁) = θᵀ(w_i+a₂) = 0}`, and replace "by
   Lemma K" with "by the direct argument of MXGen item 4 (only `ℚ`-independence of `θ`; `ρ ∈ K` not needed)". Also
   add the observation `d₁ + 2d₂ = 2d` (#4). (#17)
5. **`TRUST.md`.**
   - Add `Final.mxP_K` and `Final.deg2_i` to §2.
   - Add a §3 row: `hW : Gen.Thm11KappaMXP`, the theorem for `G'' = (E_i^♮ × E_ρ^♮ × G_a²)^n/U'`, an extension of
     `E_i^n × E_ρ^n` by `G_a²`, for every adapted `K ∋ i`; review: this file.
   - In §5, set MX′/D′ to ◐ (D′ first coordinate, for `v ∈ Ψ'(Λ(G))`) and deg2(i) to ✔.
   - Add `gmXP` at l. 78, and "MX′: `3n > 4n + 4`" at l. 84. (#18)
6. **`Waldschmidt.lean:12–13`, `Final.lean:28–32`.** List `Thm11KappaMXP` and `WuestholzSix`. (#19)
7. **Optional.** Drop `hΓ` from `deg2_i` / `deg2_ii` (derive it from `h6`), and shorten the `c₀ = 0` branch. (#15, #16)

## Falsification attempts (none succeeded)

* **`K` without `√3`, or `r = 1, 2`.** `sub` stays sound (direct argument). `d₁ + 2d₂ = 2d` makes the `d`-fields
  harmless.
* **Spurious κ.** `perXP = ℚ ⊗ Ker exp_{G''}` exactly. Lean uses `κ ≥ 2n`, and `κ = 3n` (period data) is still in
  range.
* **A subgroup inside `ker Ψ''`.** The fibre case and the splitting case are both excluded. The splitting case uses
  the pure antilinearity of `η` on both CM lattices, plus `ker ψ ∩ ker φ = 0`.
* **A third direction on `V'` from torsion data.** It would need `|β|² = √3/2` with `β ∈ ℚ(i, ρ)`, which is impossible.
* **False named inputs.** `WuestholzSix`, `hΓ`, `hM` and `hg₂'`, `hg₃'` are all true. `hΓ` and `hM` even follow from
  `WuestholzSix`.
* **Wrong quasi-periods.** These would make `LogNat` and `WuestholzSix` speak about the wrong numbers. They were
  checked against the Lean `ζ` series directly.

## Verdict lines

* Item 1 (`gmXP`, `Thm11KappaMXP`, `exists_adapted_basis_three`): **CORRECT**.
* Item 2 (`mxP_K` vs Theorem MX′ / Prop. D′): **CORRECT WITH NOTES** (faithful weakening; paper's sketch should name
  Cor. Γ for the independence).
* Item 3 (`deg2_i`, `WuestholzSix`, `transcendental_omegaRho_div_varpi_of_six`, wrappers, `LogNat` inputs):
  **CORRECT WITH NOTES** (paper gap at `c₀ = 0` confirmed, MINOR, one-line fix via six-independence; TRUST.md stale).
