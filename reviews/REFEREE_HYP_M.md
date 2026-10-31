# Referee report: the frame `gmFM`, the Theorem M model `gmM`, `Thm11KappaM`, Theorem M and Corollary M

Referee: adversarial AI reviewer (Claude), 2026-10-30.

**Scope.**
* In full: `CM4E/Gen/FrameM.lean`, `CM4E/Gen/ThmM.lean`, `CM4E/Gen/ThmMCor.lean`, and the Theorem M section of
  `CM4E/Final.lean` (`thmM_varpi`, `thmM_omegaRho`, `thmM_varpi_k`, `m1_varpi`, `m3_varpi`, `m3'_varpi`, `meta_varpi`).
* For context: `CM4E/Waldschmidt.lean`, `CM4E/Gen/MG.lean` (`Wpsi`, `Qm`, `lamM`, `algQm`, `perQm`,
  `finrank_Wpsi_ge`), `CM4E/Gen/CMLattice.lean` (structure `CMLattice`), `Gen/Basis.lean` (`IsAdaptedFieldBasis`),
  `Gen/Instances.lean`, `Gen/SMG.lean` (`Ltilde`), `Gen/MXGen.lean` (`MasserCM`), `MX.lean` (`LogNat`),
  `Gen/PiTranscendental.lean`, and TRUST.md.
* Paper: Theorem M (l. 156–159), Corollary M (l. 161–169), §`sec:RW` (thm:RW, thm:W88, thm:W88k, the Lemma U list
  l. 249–251, l. 318–320, "Weights used"), §`sec:M` (l. 674–718).
* Baseline: `reviews/REFEREE_HYP_MXP.md`, `REFEREE_HYP_GEN.md` (for `gmMG`/`A''`), `REFEREE_HYP_SMG.md` (earlier models
  with `d₀ > 0`).

**Process.** No project file other than this report and `reviews/checks/hypm/` was edited, and no git command was
run. The scratch files are:
* `reviews/checks/hypm/AxM.lean` and `AxM.out`: the axiom audit, `#check` of the seven `Final` wrappers, `#print` of
  `gmM`, `gmFM`, `Thm11KappaM`, and two `example`s checking that `(gmM L b).d₁ = 2r` and `(gmM L b).d₂ = finrank Qm`;
* `reviews/checks/hypm/check_m.py` and `check_m.out`: numerics (mpmath, 60 digits) and the count / Lemma U table.

## Verdicts

* **Item 1 (`gmFM`, `frameM_false`; `G_a` in `d₀`): CORRECT.** A direct factor `G_a` belongs in `d₀`, which has
  weight 0 in both (5.4) and Thm 4.1. This is the literal decomposition of W88, it is the project's earlier usage
  (SMG `d₀ = 2`, SMG♮ and MX `d₀ = 1`), and it is forced by "`d₀` maximal". The count in `frameM_false` is right.
* **Item 2 (`gmM`, soundness of every field): CORRECT.** `lam ⊂ Λ(G'')`, `per ⊂ ℚ ⊗ Ker exp`, `alg` is the
  `ℚ̄`-structure, the subgroups are products, and every nonzero factor has an algebraic tangent vector with `Ψ'' ≠ 0`.
  `(d₀, d₁, d₂) = (1, n, r)` is exact. Only cosmetic docstring issues were found.
* **Item 3 (`thmM`, `thmM_I_k` vs Theorem M; Lean route; truth of `Thm11KappaM`): CORRECT WITH NOTES.** The Lean
  route is the paper's RW reduction (b) made explicit, followed by the hyperplane theorem W88k instead of Statement R.
  It is valid and needs strictly less than the paper's first proof. `Thm11KappaM` is a true consequence of W88 §5d,
  (5.4), with the usual inherited trust note. Notes: the paper should record this route (and add Theorem M to its
  Lemma U list); the `s ∈ k` clause is formalised only on `E_i`.
* **Item 4 (`ThmMCor`, named inputs, `Final` wrappers): CORRECT WITH NOTES.** (M1), (M3), (M3′), (Mη) match the paper;
  Mathlib's junk value of `℘` at lattice points is never reached and never used. (M2) is honestly listed as not
  formalised. The wrappers discharge exactly `g₂`, `g₃` (lemniscatic) and `ϖ/π`, resp. `Ω_ρ/π`, transcendence. TRUST.md
  and README are stale (MINOR, docs). `HermiteLindemann` could be discharged in Lean (NIT).

**Axioms.** I ran `lake env lean reviews/checks/hypm/AxM.lean` (oleans newer than the sources). All sixteen
declarations use only `propext`, `Classical.choice`, `Quot.sound`: `Gen.frameM_false`, `Gen.thmM`, `Gen.thmM_I_k`,
`Gen.m1`, `Gen.m3`, `Gen.m3'`, `Gen.meta_I`, `Gen.logE_of_wp`, `Gen.logNat_of_logE`, and the seven `Final` wrappers.
`Axioms.lean` already lists the new theorems.

**No FATAL or MAJOR issue was found.**

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `G_a` in `d₀` (key question) | W88 Thm 4.1 (paper l. 229–240) and Thm 1.1/(5.4) give the `G_a^{d₀}` factor weight 0; `G'' = A'' × G_m^n × G_a` is literally of that form, and `d₀ = 1` is maximal (`Hom(G'', G_a) = ℚ̄`). Counting `G_a` in `d₂` would be a non-maximal decomposition, which W88k does not ask for |
| 2 | OK | `frameM_false` count | `m = n + 1`, `κ ≥ n`, `t = d − 2`, so (5.4) reads `n + 1 > n + 2d₂ − κ`, which holds from `κ ≥ n` and `2d₂ ≤ n`. The `d`-fields are load-bearing here (unlike `gmXP`, REFEREE_HYP_MXP #4): `d₁ + 2d₂ = 2n` is the minimum possible weight `2d − 2d₀ − d₁` |
| 3 | OK | `alg`, `lam` | `algQm` is the image of `ℚ̄ⁿ` under the `ℚ̄`-rational quotient `E^n → A''`. `eSlot j u` (`u ∈ 𝓛_E`) maps to the image of the algebraic point `P e_j ∈ E^n(ℚ̄)`; `mSlot`, `aSlot` are logarithms in `G_m^n`, `G_a`. `Λ(G'')` is a `ℚ`-space |
| 4 | OK | `per` | `[ωe_j]`, `[αωe_j]` (REFEREE_HYP_GEN #7) and `2πi e_h`. `G_a` has no periods. `per = ℚ ⊗ Ker exp_{G''}`, of dimension `2n` |
| 5 | OK | `sub` / product claim | connected subgroups are products `B × T × (0 or G_a)` (Goursat; no nonzero homomorphisms between subquotients of an abelian variety, a torus and `G_a`, in either direction). Each nonzero factor has an algebraic `x` with `Ψ''x ≠ 0` (below). No connected subgroup lies in `ker Ψ''` |
| 6 | OK | `d₂ = finrank Qm ≤ r` | `Wpsi = ℂ·ker ψ` exactly, and `dim_k ker ψ = n − n/2`, so `d₂ = dim A'' = r` exactly (checked again for `ℚ(i, √2)`, `ℚ(ρ, √2)`). `finrank_Qm_le` gives `2d₂ ≤ n` |
| 7 | OK | quantifier over adapted bases | soundness uses only that `θ` is algebraic and `ℚ`-independent, and that `ψ` is `k`-linear (always). Covers `r = 1` too |
| 8 | OK | Lemma U range | `2N = 3n`, condition `κ ≤ 2n − 2`. Application: `κ = n` exactly, `3n ≥ 2n + 2`. The only out-of-range instances (`κ ∈ {2n − 1, 2n}`) force a rational toric line into `V`, so their conclusion holds outright |
| 9 | OK | `thmM` proof vs paper | `G''`, `Ψ''` are exactly RW93's `G^n/H` and `Ψ'` for `G = E × G_m × G_a`, `Ψ = (e, t + a)`. `V'' = Ψ''⁻¹(ℂ(Ω, iπ))` is a hyperplane, so W88k suffices. The exclusion uses Schneider (`ω/π ∉ ℚ̄`, proved in `Ext`) |
| 10 | OK | `thmM` statement | Theorem M for `Ω = cω`, `c ∈ ℚ̄ˣ`: covers every period `mω` (`m ∈ ℤ[α]`) and every curve `ℚ̄`-isomorphic to `E`. Hypotheses `u ∈ ℚ̄𝓛_E` (`QbarLogE`) and `ℓ ∈ 𝓛̃` (`Ltilde`) are the paper's |
| 11 | MINOR (paper) | l. 249–251, 318–320 | the paper says `u ∈ ℚ̄𝓛_E` "uses Theorem RW as stated". The Lean route shows it needs only Theorem W88k (the hyperplane case). Add Theorem M to the Lemma U list (`3n ≥ 2n + 2`) |
| 12 | NIT | `thmM_I_k` | the clause "if `u ∈ 𝓛_E` then `s ∈ k`" is formalised only for `E_i`, `Ω = ϖ`. An `E_ρ` version follows the same way from `MasserCM.2` |
| 13 | OK | (M1), (M3), (M3′), (Mη) | statements match the paper. `cω/π`, `cπω` are never lattice points. In (M3′), `ωz ∈ L` would need `z ∈ ℤ[α]`, where `hz` fails by Hermite–Lindemann. The proofs never use `℘` at a lattice point (`logE_of_wp` takes the lattice disjunct) |
| 14 | OK | (M2) | honestly listed as not formalised (`ThmMCor.lean:19`); TRUST.md should say so too (#16) |
| 15 | OK | `Final` wrappers | discharge `hg₂ := Final.hg₂`, `hg₃ := g₃_lemniscatic_isAlgebraic`, `hT` (Schneider, proved in `Ext`; for `Ω_ρ` from `hg₂'`, `hg₃'`). `hW`, `hg₂'`, `hg₃'`, `hMa`, `hHL`, `hπ2` stay explicit |
| 16 | MINOR (docs) | `TRUST.md` | stale. §2 lacks the seven wrappers. §3 lacks rows for `Gen.Thm11KappaM` and `Gen.HermiteLindemann`. §5 l. 113 still says "Theorem M, Cor. M1–Mη: ✗". l. 75–79 and l. 84–87 need the Theorem M entries (fix list below) |
| 17 | COSMETIC | `ThmM.lean:20`, `:27`, `:22–23` | "of dimension `≤ r`" should be "`= r`". "isogeny-quotient" should be "quotient by the abelian subvariety `B_{ker ψ}`". "Without CM the count ties" is RW's per-`K` count; in the Lean count it fails (`n + 1 > 2n` is false) |
| 18 | COSMETIC | `Waldschmidt.lean:12–13`; `Final.lean:28–32`; `README.md:16ff` | the instance list omits `Thm11KappaM` (and `Thm11KappaMXP`). The "What remains assumed" paragraph omits `HermiteLindemann` and the use of `MasserCM` for Theorem M. README has no Theorem M entry |
| 19 | NIT | `ThmMCor.lean:27` | `HermiteLindemann` can be proved like `Gen.transcendental_pi`: Schneider–Lang over `ℚ(z, e^z)` for `w`, `e^w` at the points `kz`. That would remove a named input from `m3'` |
| 20 | NIT | (M2) | (M2) follows from `thmM` (`u = ϖ log α/π`, `ℓ = i log α`) plus Gel'fond–Schneider as a named input, if wanted |
| 21 | TRUST NOTE (inherited) | W88 §5d | as REFEREE_HYP_MXG #18 and SMG #14: Lemma U is checked only for the first application of Thm 4.1 inside §5d, and the `d₀ > 0` regime relies on the Gel'fond part of W88. Regime here: `d₀ = 1`, `W ≠ 0`, `κ = n > 0`, `G₂ = A''` an abelian variety (semiabelian, milder than MX) |

## Details

### 1. `G_a` is a direct factor, so it goes in `d₀` [Proved, modulo the reading of W88]

**What W88 says.**
* Thm 4.1 (paper l. 229–240): `G = G_a^{d₀} × G_m^{d₁} × G₂` is a product decomposition, with `d₀`, `d₁` "need not be
  maximal". Its inequality is `(λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2d₂ − κ)`. The `G_a`-part enters only through `δ₀`,
  which has weight 0, and `d₀` does not appear on the right.
* Thm 1.1 / (5.4) (paper l. 294–304): the same decomposition with `d₀`, `d₁` maximal, and the condition
  `m > (d₁ + 2d₂ − κ)(d − 1 − t)`, with no `d₀`.
* Consistency check: with `G' = 0`, Thm 4.1 at `N = d − 1` reads `m + d₁ + 2d₂ ≤ (d − t)(d₁ + 2d₂ − κ)`. (5.4) is
  `m + d₁ + 2d₂ − κ > (d − t)(d₁ + 2d₂ − κ)`, which contradicts it. So (5.4) excludes `G' = 0` whatever `d₀` is.
* Sanity check against a known theorem: `G = G_a × G_m`, `V = ℂ(1, β)`, `W = 0`. With `d₀ = 1`, (5.4) is `m > 1`, and
  `m = 2` is Gel'fond–Schneider (`e^β`, `e^{√2β}` not both algebraic unless `β = 0`). Counting `G_a` in `d₂` would
  need `m > 3`. So weight 0 for a direct `G_a` factor is the classical behaviour, not an artefact. Waldschmidt himself
  uses Thm 1.1 with `d₀ = 2` (Cor. 2.1; REFEREE_HYP_SMG #14).

**Why `G''` has a direct `G_a` factor.** In RW93's reduction (paper l. 271–274), for `G = E × G_m × G_a` and
`Ψ_β(e, t, a) = (θᵀe, θᵀt + θᵀa)`, the largest connected `H ⊂ G^n` with `T_H ⊂ ker Ψ_β` is the product
`B_{ker ψ} × 0 × {θᵀa = 0}`, by the product structure of subgroups (#5). Then
`G^n/H = A'' × G_m^n × (G_a^n/{θᵀa = 0}) ≅ A'' × G_m^n × G_a`, a direct product. The mixing `θᵀy + s` sits in the
linear map `Ψ''`, not in the group law. So, unlike the earlier models, where `G_a` sits non-split inside `E^♮` or `Q''`
and must go into `G₂`, here `G_a` splits.

**Maximality.** `Hom(G'', G_a) = Hom(A'', G_a) ⊕ Hom(G_m^n, G_a) ⊕ Hom(G_a, G_a) = 0 ⊕ 0 ⊕ ℚ̄`, so `d₀ = 1`.
`Hom(G'', G_m) = ℤⁿ`, so `d₁ = n`. And `d₂ = dim A'' = r`. As a cross-check, `α(G'') = 2d − 2d₀ − d₁ = 2n`, so
`α_K = 2`, the paper's value (l. 678).

**The `n + 1` vs `n + 2` point.** With `G_a` in `d₂`, (5.4) would read `n + 1 > n + 2(r + 1) − κ = n + 2`, which is
false. But that decomposition is not maximal, so W88k does not ask for it. The Lean premise is the strongest correct
one.

### 2. `frameM_false` [Proved by Lean; reading checked]

* **Independence (`hli`).** Apply `Ψ''₁` to a relation: `g_none·x + (θᵀg)·A = 0`. If `g_none ≠ 0`, then `x ∈ ℚ̄A`,
  contradicting `hx`. Otherwise `θ`-independence gives `g = 0`. So `m = n + 1`.
* **`κ ≥ n`.** The `n` lifts `p h` lie in `per`.
* **`V''`, `W''`.**
  - `V'' = ker(Ψ''₂ − σΨ''₁)` is a hyperplane (`phiM_surjective`).
  - `W'' = span wGenM = ker Ψ''` (`wGenM_le_ker`, `ker_PsiM_le`); it is `ℚ̄`-rational (uses `hTalg`, `hθalg`).
  - So `d − 1 − t ∈ {0, 1}` (it is 1, as `Ψ''` is onto).
* **(5.4).** It reads `n + 1 > (n + 2d₂ − κ)·{0, 1}`, which follows from `κ ≥ n` and `2d₂ ≤ n`.
* **Exclusion.** An algebraic `x ∈ S ⊂ V''` with `Ψ''x = (P₁, P₂) ≠ 0` has `P₂ = σP₁`, with `P₁, P₂ ∈ ℚ̄` (`hμ`,
  `hθalg`). If `P₁ = 0` then `P₂ = 0`, a contradiction; otherwise `σ ∈ ℚ̄`, which contradicts `hσ`.

### 3–7. Soundness of `gmM L b` [Proved, modulo standard facts on CM abelian varieties]

**The group.**
* `L = ℤω + ℤαω` with `α` imaginary quadratic (`CMLattice`: `α² = p + qα`, `p, q ∈ ℚ`, `Im α > 0`), and `g₂, g₃ ∈ ℚ̄`
  by hypothesis. So `E` has CM by an order of `k = ℚ(α)`, and all its endomorphisms are defined over `ℚ̄`.
* On `T(E) = ℂ` an element of the order acts as multiplication by itself (`z ↦ αz` on `ℂ/L`).
* For a `k`-subspace `S ⊂ kⁿ` the abelian subvariety `B_S ⊂ E^n` has `T(B_S) = ℂS`. Every abelian subvariety of `E^n`
  is a `B_S` (`End⁰(E^n) = M_n(k)`).
* `ψ(m) = θᵀm` is `k`-linear, so `ker ψ` is a `k`-subspace, `A'' = E^n/B_{ker ψ}` is defined over `ℚ̄`, and
  `T(A'') = ℂⁿ/ℂ·ker ψ = Qm`. `Wpsi` is *defined* as `ℂ·ker ψ` (the span of the `k`-vectors in `ker ψ`).

**`alg`.** The coordinate `z` with `exp z = (℘(z), ℘'(z))` is `ℚ̄`-rational (it is `dx/y`). `algQm` is the image of
`ℚ̄ⁿ` under the `ℚ̄`-rational differential of the quotient map, which is the quotient `ℚ̄`-structure. The toric
coordinates `t` (`exp = e^t`) and the `G_a` coordinate are `ℚ̄`-rational.

**`lam`.**
* `eSlot j u`, with `u ∈ 𝓛_E` (`LogE`: `u ∈ L`, or `℘(u), ℘'(u) ∈ ℚ̄`), is `[u e_j]`. Its exponential is the image in
  `A''` of `(0, …, exp_E(u), …, 0) ∈ E^n(ℚ̄)`, an algebraic point, since `E^n → A''` is defined over `ℚ̄`. **So the
  images in `T(A'')` of `u·e_j` are logarithms of algebraic points of `A''`.** The check that Mathlib's
  `℘'² = 4℘³ − g₂℘ − g₃` (`derivWeierstrassP_sq`) uses the same `g₂`, `g₃` is what makes `logE_of_wp` correct.
* `mSlot h l` with `e^l ∈ ℚ̄` and `aSlot c` with `c ∈ ℚ̄` are logarithms in `G_m^n` and `G_a`.
* `Λ(G'')` is a `ℚ`-space (division points of algebraic points are algebraic), so `span_ℚ lamMS ⊂ Λ(G'')`.

**`per`.** `[ωe_j]`, `[αωe_j]` are images of lattice points of `E^n`, and they generate `Ker exp_{A''}`
(REFEREE_HYP_GEN #7). `2πi e_h` are the toric periods. `per = ℚ ⊗ Ker exp_{G''}`, of dimension `n + n = 2n`, so `κ` is
never inflated. In `thmM`, the toric part of `p h` is `iπ e_h = ½·2πi e_h`. `p h` itself is not a period (its
exponential is `−1` in slot `h`), but `2p h` is, so `rk_ℤ(Y ∩ Ker exp) = dim_ℚ(Y_ℚ ∩ per)` (`Waldschmidt.lean`
docstring) still gives `κ ≥ n`.

**`sub`, the product claim and the exclusion.**
* **Products.** Let `H ⊂ A'' × G_m^n × G_a` be connected. By Goursat it is a product, because no two of the following
  have a common nonzero subquotient:
  - abelian varieties;
  - tori;
  - `G_a`.
  
  In more detail: `Hom(G_a, A) = 0` (`A` has no unipotent subgroup), `Hom(A, G_a) = 0` (`A` is complete), and
  `Hom(G_m, G_a) = Hom(G_a, G_m) = 0`. Torus versus abelian variety is standard. A connected `H` whose two projections
  have isomorphic connected quotients of different types must have those quotients trivial. Hence
  `H = B × T_ℒ × (0 or G_a)`. The docstring claim (`ThmM.lean:29–30`) is correct.
* **Each nonzero factor has an algebraic `x` with `Ψ'' ≠ 0`.**
  - `G_a`: `x = (0, 0, 1)`, with `Ψ''x = (0, 1)`.
  - `T_ℒ ≠ 0`: a rational `l ∈ ℒ ∖ 0`, with `Ψ''(0, l, 0) = (0, θᵀl) ≠ 0` by `ℚ`-independence of `θ`.
  - `B ≠ 0`: the identity component of its preimage in `E^n` is `B_{S'}`, with `S' ⊋ ker ψ` a `k`-subspace. Take
    `s ∈ S' ∖ ker ψ` (in `kⁿ ⊂ ℚ̄ⁿ`); then `x = ([s], 0, 0)` is algebraic and `Ψ''x = (ψ(s), 0) ≠ 0`.
  
  Since `H` is a product, `x ∈ T_H` in each case. So every nonzero connected subgroup is in `sub`. Lean's `sub`
  ("contains an algebraic `x` with `Ψ''x ≠ 0`") is a superset of the true family, which only weakens the conclusion.
* **Falsification attempt.** A connected subgroup with `T_H ⊂ ker Ψ'' = {θᵀz = 0, θᵀy + s = 0}` must be a product of
  factors each inside `ker Ψ''`, and each factor is 0 by the three cases. A "diagonal" between `G_m^n` and `G_a` would
  be the graph of a homomorphism, which is 0. So there is none.

**`d₂`.**
* `finrank_Wpsi_ge` exhibits `r` independent `k`-vectors `α e_{(k,0)} − e_{(k,1)} ∈ ker ψ`. Lemma K gives
  `dim_k ker ψ = n − n/2 = r` exactly.
* So `d₂ = finrank Qm = n − r = r = n/2`. `check_m.out` [6] re-checks this for `ℚ(i, √2)` and `ℚ(ρ, √2)`.
* `d₂` is *defined* as the dimension of the modelled tangent space, so it cannot be undercounted relative to `Qm`.
  `Qm = T(A'')` holds exactly because `Wpsi = ℂ·ker ψ` (`ℂS ∩ kⁿ = S` for a `k`-subspace `S`).

### 8. Lemma U range [Proved; `check_m.out` [7]]

* `d = r + n + 1 = 3n/2 + 1`, so `2N = 2(d − 1) = 3n`. The condition `2N ≥ d₁ + 2d₀ + κ` is `κ ≤ 2n − 2`.
* **Application.** `κ = n` exactly. A combination involving `D` that is a period would put `u ∈ Kω ⊂ ℚ̄cω`, against
  `hx`. So the condition is `3n ≥ 2n + 2`, true for `n ≥ 2` (and `exists_adapted_basis` gives `n ≥ 4`).
* **Out-of-range instances.**
  - If `κ = 2n`, then `V ⊇ ℂ·per = T(A'') × ℂⁿ × 0`.
  - If `κ = 2n − 1`, then `V ∩ per_ℚ` meets `2πiℚⁿ` in dimension `≥ n − 1 ≥ 1`.
  
  Either way `V` contains a rational `l ≠ 0` in the toric slot, with `Ψ''(0, l, 0) ≠ 0`, so the conclusion of
  `HyperplaneKappa` holds outright.
* TRUST.md l. 75–79 should add `gmM` with this sentence. The paper's list (l. 249–251) should add "Theorem M:
  `3n ≥ 2n + 2`".

### 9–10. `thmM` vs Theorem M, and the Lean route [Proved by Lean; reading checked]

**The route.** The paper's first proof (l. 677–683) applies Theorem RW to `G = E × G_m × G_a`. RW's step (b) replaces
`G` by `G^n/H`, which is exactly Lean's `G''` (§1). Since `V = ℂ(Ω, iπ)` is a line in `ℂ²` and `Ψ''` is onto,
`V'' = Ψ''⁻¹(V)` is a **hyperplane**. Statement R in the hyperplane case is W88 Thm 1.1 with (5.4) (paper l. 290–304).
* So Lean needs only W88k, which the rest of the project also assumes, not the general Statement R of RW93 (whose
  proof is the categorical argument of l. 280–285).
* The count is the paper's: `dim_K(V ∩ Ψ(Λ_K)) ≤ α_K − κ = 2 − 1 = 1`, scaled by `n`: `n + 1 > 2n − n`.
* Condition (i) of RW becomes the uniform exclusion: `V''` contains no algebraic `x` with `Ψ''x ≠ 0`, because
  `σ = iπ/(cω) ∉ ℚ̄` (Schneider, proved in `Ext`). Lean does not need Masser's theorem for (i).
* The route is mathematically valid. It is a cleaner proof than the paper's first proof for `u ∈ ℚ̄𝓛_E`, and the paper
  should say so (#11). The sentence at l. 318–320 ("only `u ∈ ℚ̄𝓛_E` uses Theorem RW as stated") is now superseded.

**Lifts.**
* `p h = Σ_j m_{hj}[ωe_j] + iπ e_h`, with `θ_h c = Σ m_{hj}θ_j`, `m_{hj} ∈ ℚ`. This gives
  `Ψ''(p h) = θ_h(cω, iπ) = θ_h(A, σA)`.
* `D = Σ_k Σ_j coordsA(β_k)_j·eSlot j (v_k) + Σ_k Σ_h coordsA(γ_k)_h·mSlot h (l_k) + aSlot β₀`, which gives
  `Ψ''(D) = (u, ℓ) = (u, σu)` by `hrel`.
* `K` is built to contain `c`, `β_k`, `γ_k`. Neither `i ∈ K` nor `η₀` is needed, so `gmM` is unaffected by the
  `Im α` sign issue (REFEREE_HYP_GEN #10; now `0 < α.im` anyway).

**Statement.**
* Paper: `Ω ≠ 0` a period of `E`, `u ∈ ℚ̄𝓛_E`, `ℓ ∈ 𝓛̃`, `iπu = Ωℓ` imply `u = sΩ` and `ℓ = s·iπ` with `s ∈ ℚ̄`.
* Lean: `Ω = cω` with `c ∈ ℚ̄ˣ`. This contains every period `mω` (`m ∈ ℤ[α] ∖ 0`), so it is a faithful
  (slightly stronger) statement.
* `QbarLogE` is the set of finite `ℚ̄`-combinations of `LogE` elements, which is `ℚ̄𝓛_E`. `Ltilde` is
  `ℚ̄ + ℚ̄𝓛` (`SMG.lean:37`).
* `Final.thmM_varpi` / `thmM_omegaRho` instantiate `ϖℤ[i]` and `Ω_ρℤ[ρ]`. Every curve with `j = 1728` (resp. 0) has
  lattice `λϖℤ[i]` (resp. `λΩ_ρℤ[ρ]`) with `λ ∈ ℚ̄`, and `𝓛_{E'} = λ𝓛_E`, so these cover all such curves.

**`s ∈ k` (`thmM_I_k`).**
* `thmM` with `c = 1` gives `u = sϖ` with `s ∈ ℚ̄`. `logNat_of_logE` supplies a `w` with `LogNat` (lattice: `w = η`;
  otherwise `w = ζ(u)`), and `MasserCM.1` then gives `s ∈ ℚ(i)`.
* `MasserCM` is true (Masser 1975: `k`-independent elements of `𝓛_E` are `ℚ̄`-independent), and its truth does not
  depend on `w`.
* An `E_ρ` analogue is not stated (#12).

**Is `Thm11KappaM` true?** Yes. It is W88 §5d, (5.4), applied to a sound model (§§1, 3–7), for every adapted basis.
The out-of-range Lemma U instances are trivially true (§8). The only residual risk is the inherited one (#21).
* **Adversarial checks.** I looked for a configuration where the premise holds but no subgroup lies in `V`:
  - the subgroup list is complete (products);
  - `κ` is never overcounted (`per = ℚ ⊗ Ker exp`);
  - `d₂` is exact;
  - `d₀ = 1` is the literal decomposition.
* **Controls behave correctly.**
  - Without CM, `d₂ = n` and the premise `n + 1 > 2n` fails, so no conclusion is forced.
  - With `E` replaced by `G_m` (`Ω → 2πi`), the count passes, but `V'' = Ψ''⁻¹(ℂ(2, 1))` contains a rational
    toric vector. So the hypothesis returns a true conclusion and no contradiction, matching the paper's control
    (l. 686).

### 13–15. Corollary M and the wrappers

**(M1)** `m1`: `Transcendental (℘(cω/π))` for `c ∈ ℚ̄ˣ`, on every `CMLattice` with algebraic `g₂, g₃`.
* Proof: `u = cω/π`, `ℓ = ic`; then `thmM` gives `c/π = s ∈ ℚ̄`, against `transcendental_pi` (proved).
* `cω/π ∈ L` would need `c/π ∈ ℤ[α]`, so the junk value is never reached.
* This matches paper l. 163 and l. 713.

**(M3)** `m3`: if `e^{π²} ∈ ℚ̄` then `℘(cπω)` is transcendental.
* `ℓ = icπ² ∈ 𝓛̃` (`mem_Ltilde_of_log`), and `s = cπ`, which is impossible.
* Every period of the lattice is `mω`, so "every period" is covered by varying `c`. "Every CM curve" holds for every
  `CMLattice`; only `ϖℤ[i]` is wrapped in `Final`.
* `c = 1` gives "one of `e^{π²}`, `℘(πϖ)` is transcendental".

**(M3′)** `m3'`: for `e^z ∈ ℚ̄ ∖ {1}` (any logarithm `z`, so any branch), `e^{iπz}` and `℘(ωz)` are not both
algebraic.
* `thmM` gives `z ∈ ℚ̄`, and then Hermite–Lindemann applies (`z ≠ 0` because `e^z ≠ 1`).
* This matches l. 167 and l. 715–716. If `ωz ∈ L` then `z ∈ ℤ[α] ∖ 0`, and `hz` already fails by Hermite–Lindemann.
  In any case the proof never evaluates `℘` at a lattice point: `logE_of_wp` uses the lattice disjunct.

**(Mη)** `meta_I`: `(π/ϖ)u ∉ 𝓛̃` for `u ∈ 𝓛_{E_i} ∖ ℚ(i)ϖ`.
* `η(ϖ) = π/ϖ` was verified in earlier reports (REFEREE_HYP_GEN #9, MXP #13).
* `ℓ = i(π/ϖ)u` and `thmM_I_k` give `u ∈ ℚ(i)ϖ`. This matches l. 168.

**(M2)** is not formalised and says so (`ThmMCor.lean:19`). It would follow from `thmM` plus Gel'fond–Schneider (#20).

**`logE_of_wp`.** Off the lattice, `℘'² = 4℘³ − g₂℘ − g₃ ∈ ℚ̄` gives `℘' ∈ ℚ̄`; on the lattice it takes the first
disjunct. Correct.

**`logNat_of_logE`.** Correct, as above.

**`HermiteLindemann`** is true (Lindemann 1882). It can be proved with the vendored Schneider–Lang criterion (#19).

**Wrappers** (`Final.lean:241–293`; types in `AxM.out`).
* `thmM_varpi`, `m1_varpi`, `m3_varpi`, `m3'_varpi` discharge `hg₂ := Final.hg₂`,
  `hg₃ := g₃_lemniscatic_isAlgebraic` and `hT := transcendental_varpi_div_pi` (Schneider).
* `thmM_omegaRho` keeps `hg₂'`, `hg₃'` and derives `hT` from them via `period_div_pi_transcendental`.
* `thmM_varpi_k` and `meta_varpi` keep `hMa`, and `m3'_varpi` keeps `hHL`.
* No other hypothesis is discharged or hidden.

### Numerics [Numerical, 60 digits; sanity only]

* **The lemniscatic `℘`.** By `q`-series: `|℘'² − (4℘³ − 4℘)| = 1.3e-57`, `|℘(z + ϖ) − ℘(z)| = 4e-60`,
  `|℘(iz) + ℘(z)| = 1.4e-60`. `ϖ = 2.62205755429211981046…`.
* **Values.** `℘(ϖ/π) = 1.5794357370991220…` and `℘(πϖ) = 7.2825472286658652…`. Neither satisfies an integer polynomial
  of degree `≤ 6` with coefficients `≤ 10⁵`, consistent with (M1) and with (M3) under `e^{π²} ∈ ℚ̄`.
* **Control.** `℘(ϖ/2) = 1` (2-torsion), so `u = ϖ/2`, `ℓ = iπ/2` satisfies `iπu = ϖℓ` with `s = 1/2`, consistent
  with Theorem M.

## Suggested fixes

1. **Paper, §sec:M and §sec:RW.** Add a remark after the first proof of Theorem M:
   > The same count follows from Theorem W88k (no RW93): with `K ∋ c` and the coefficients, `G'' = A'' × G_m^n × G_a`,
   > `A'' = E^n/B_{ker ψ}` of dimension `n/2`, `Ψ''([z], y, s) = (θᵀz, θᵀy + s)`, `V'' = Ψ''⁻¹(ℂ(Ω, iπ))`, `W'' = ker Ψ''`,
   > with the `n` period lifts and one lift of `(u, ℓ)`: `n + 1 > (n + n − n)·1`; the `G_a` factor is direct, so it
   > counts in `d₀`.

   Update l. 318–320 accordingly, and add "Theorem M: `3n ≥ 2n + 2`" to the Lemma U list (l. 249–251). (#11)
2. **`ThmM.lean` docstring.** At l. 20 write "of dimension `r = n/2`". At l. 27 replace "isogeny-quotient" with
   "quotient by the abelian subvariety `B_{ker ψ}`". At l. 22–23 replace "without CM the count ties" with "without CM,
   `d₂ = n` and the premise `n + 1 > 2n` fails (RW's per-`K` count ties)". Optionally add the one-line reason that
   `d₀ = 1` (`Hom(G'', G_a) = ℚ̄`), and the Lemma U sentence of §8. (#17)
3. **`TRUST.md`.** (#16)
   - §2: add `Final.thmM_varpi`, `thmM_omegaRho`, `thmM_varpi_k`, `m1_varpi`, `m3_varpi`, `m3'_varpi`, `meta_varpi`
     with their assumptions (`hW : Gen.Thm11KappaM`, plus `hg₂'`, `hg₃'` / `MasserCM` / `HermiteLindemann` /
     `e^{π²} ∈ ℚ̄` as applicable).
   - §3: add a row `hW : Gen.Thm11KappaM L` (W88 §5d for `A'' × G_m^n × G_a`, `d₀ = 1`, every adapted `K`; review:
     this file) and a row `Gen.HermiteLindemann` (Lindemann 1882).
   - §5 l. 113: set Theorem M ✔ (`s ∈ k` clause on `E_i` only), Cor. M ◐ ((M1), (M3), (M3′), (Mη) ✔; (M2) ✗).
   - l. 77–79: add `gmM` (out of range only for `κ ∈ {2n − 1, 2n}`, trivially true).
   - l. 84–87: add "Theorem M: `n + 1 > 2n`" to the list of counts that fail without `κ`, and Theorem M to the
     `d₀ = 1` list.
4. **`Waldschmidt.lean:12–13`, `Final.lean:28–32`, `README.md`.** List `Thm11KappaM` (and `Thm11KappaMXP`); name
   `HermiteLindemann` and the Theorem M use of `MasserCM`; add a README entry for Theorem M / Cor. M. (#18)
5. **Optional.**
   - Prove `HermiteLindemann` along the lines of `Gen.transcendental_pi`. (#19)
   - Add `thmM_rho_k` from `MasserCM.2`. (#12)
   - Add (M2) with Gel'fond–Schneider as a named input. (#20)

## Falsification attempts (none succeeded)

* **`G_a` should be in `d₂`.** No: it is a direct factor (RW's `H` is a product), and `d₀ = 1` is maximal. Weight 0 for
  `G_a` is what makes the Gel'fond–Schneider case of W88 work.
* **A subgroup inside `ker Ψ''`.** Subgroups are products, and each factor type is excluded (`ψ` on `S' ⊋ ker ψ`,
  `ℚ`-independence of `θ`, the `s`-coordinate).
* **Undercounted `d₂`.** `d₂ = finrank Qm = r` exactly; `Wpsi = ℂ·ker ψ` by definition.
* **Spurious `κ`.** `per = ℚ ⊗ Ker exp_{G''}`. The half-period `iπ e_h` is handled by the `ℚ`-span equivalence. In the
  application `κ = n` exactly.
* **Lemma U.** In range in every non-trivial instance.
* **Junk `℘`.** Never evaluated at a lattice point in any corollary statement or proof.
* **Wrong wrappers.** `#check` output shows exactly the expected remaining hypotheses.

## Verdict lines

* Item 1 (`gmFM`, `frameM_false`, `G_a` placed in `d₀`): **CORRECT**.
* Item 2 (`gmM` soundness: `lam`, `per`, `alg`, `sub`/product claim, `d₂ = finrank Qm ≤ r`): **CORRECT** (cosmetic
  docstring wording only).
* Item 3 (`thmM`, `thmM_I_k` vs Theorem M; Lean route via W88k; truth of `Thm11KappaM`): **CORRECT WITH NOTES** (route
  valid and lighter than the paper's RW route, so the paper should record it and add Theorem M to the Lemma U list;
  `s ∈ k` only on `E_i`; inherited W88 §5d trust note).
* Item 4 (`ThmMCor`: m1, m3, m3′, meta_I, `HermiteLindemann`, `logE_of_wp`, `logNat_of_logE`; Final wrappers):
  **CORRECT WITH NOTES** (statements faithful, (M2) honestly omitted, wrappers discharge only `g₂`, `g₃` and the
  `ω/π` transcendence; TRUST.md/README stale; `HermiteLindemann` dischargeable).
