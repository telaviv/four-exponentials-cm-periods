# Referee report: the general-`K` model `gmXG`, `Thm11KappaMXG`, and Theorem MX / Corollary MX1 for every `β`

Referee: adversarial AI reviewer (Claude), 2026-10-30. Scope: `CM4E/Gen/MXGen.lean` (in full), the wrappers
`Final.mx_K`, `Final.mx`, `Final.mx1`, with `CM4E/Gen/Basis.lean`, `BasisExists.lean` (statement of
`exists_adapted_basis`), `CMLattice.lean`, `Frame.lean` (the helpers used), `CM4E/MX.lean`, `CM4E/Lattice.lean`,
`CM4E/Waldschmidt.lean`, the `ζ` definition (`Ext/Weierstrass/ZetaDef.lean`) and Schneider's theorem
(`Ext/SchneiderMain.lean`). Paper: Theorem MX, Corollary MX1, §"Proof of Theorem MX" (Prop. D, Steps 1–4, Remark 26
"The count", Remark `rem:gamma`), Lemma K, Theorem `thm:W88k`, Appendix A (Lemma U). Earlier review:
`reviews/REFEREE_HYP_MX.md` (model `gmX`, `K = ℚ(i, √3)`), whose findings I rely on where marked.

No project file other than this report and `reviews/checks/hypmxg/` was edited, and no git command was run.
Check script and output: `reviews/checks/hypmxg/check_mxg.py`, `check_mxg.out`.

## Verdict: CORRECT

* **The model.** `gmXG b` is sound for every adapted basis `θ = theta I b`.
  - Soundness needs only that `θ` is algebraic and `ℚ`-linearly independent. It needs neither `ρ ∈ K` nor the field
    structure of `K`.
  - The Lemma U range `2N ≥ d₁ + 2d₀ + κ` holds for every instance of `HyperplaneKappa (gmXG b)`.
* **The proof.** `mx_K` is a faithful formalisation of the second derivation in Remark 26, for general `β`.
* **The named inputs are true.** `WuestholzMX`, `MasserCM`, `LaurentZeta` and `hΓ` are true statements, each a
  consequence of Wüstholz's analytic subgroup theorem. The derivations are given below; the cited classical
  references are not checked against the sources.
* **The statements.** `mx_full` / `Final.mx` and `mx1` / `Final.mx1` state the main clauses of Theorem MX and
  Corollary MX1 faithfully.
* **Axioms.** `lake env lean Axioms.lean`: all 38 audited declarations use only `propext`, `Classical.choice`,
  `Quot.sound` (two use fewer). Among them are `Gen.mx_K`, `Gen.mx_full`, `Gen.mx1`, `Final.mx_K`, `Final.mx`,
  `Final.mx1` and `Gen.exists_adapted_basis`. `lake build CM4E.Final` is up to date (the `MXGen` olean is newer than
  the source), and `CM4E/` contains no `sorry`, `axiom` or `native_decide`.

Only cosmetic issues were found: stale cross-references and docstrings (#12–#14). The trust notes of
REFEREE_HYP_MX #15 carry over unchanged (#17).

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `alg`, `lam` for general `K` | `algXG` is the quotient `ℚ̄`-structure. `lam` ⊂ Λ(G″). Independent of `K` (only `θ ⊂ ℚ̄` is used) |
| 2 | OK | `per` | the four generators per copy are genuine periods; `perXG = ℚ ⊗ Ker exp_{G″}` (rank `4n`) for every `K` |
| 3 | OK | `sub` for every `K` | every nonzero connected `H ⊂ G″` has an algebraic tangent vector with `Ψ″ ≠ 0`. This needs only `θ` algebraic and `ℚ`-independent: `ker ψ ∩ ker φ = 0` holds for **any** `ℚ`-independent `θ`, with no field structure and with or without `ρ ∈ K` |
| 4 | OK | `d₀ = 1`, `d₁ = 0`, `d₂ = 2n + 1` | maximal for every `K` (`G_ℓ` is a quotient of the anti-affine `A^♮`) |
| 5 | OK | dependence on `K` | `ρ ∈ K` is **not** needed for soundness. It is needed only in the proof (`liftR`, `P1`, `P2`), and there it is ensured by `r3 ∈ K` in the `exists_adapted_basis` call. `ℚ`-independence of `θ` **is** needed (a rational relation would give a type-D subgroup in `ker Ψ″`); it is part of `IsAdaptedFieldBasis` |
| 6 | OK | Lemma U range | `2N = 4n + 2 ≥ 2 + κ` for every instance, since `κ ≤ rk Ker exp_{G″} = 4n` |
| 7 | OK | `liftI`, `liftR`, `P1`, `P2`, `DX` | explicit Lemma K. `Ψ″`-images `θ_h w₁`, `θ_h w₂`, `θ_h v` are Lean-proved; the period lifts lie in `per` ⊂ `lam` |
| 8 | OK | `κ ≥ 2n`, count, exclusion | `m = 3n` (independence from `hM` and the negated conclusion), `κ ≥ 2n`, `d − 1 − t = 1`, `3n > 4n + 2 − κ` with `n = 2r ≥ 4`. The final exclusion is that of Remark 26 (uses `hΓ`) |
| 9 | OK | `WuestholzMX` | true: Wüstholz 1989 on `E_i² × E_ρ² × G_a`. The quantifiers are right; lattice points are allowed and harmless |
| 10 | OK | `MasserCM` | true: Wüstholz on `E²` (or Masser 1975, CM elliptic Baker). Lattice points give `x ∈ ℤ[i]`, resp. `ℤ[ρ]` |
| 11 | OK | `LaurentZeta` | true: Wüstholz on `E_i^♮ × G_a`. Its hypothesis `u ∉ ℚ(i)ϖ` is stronger than needed (`u ∉ Λ` suffices). The `ζ` is the Weierstrass `ζ` |
| 12 | OK | `hΓ`, `hM` | true (Wüstholz); `hM` is derived in Lean from `WuestholzMX` |
| 13 | OK | `mx_full`, `mx1`, `Final.*` | faithful to the main clauses of thm:MX and cor:MX1. The Schneider step for `u + a ≠ 0` is correct and genuinely needed (Lean's `x/0 = 0`) |
| 14 | COSMETIC | stale references | (a) the `MXGen` docstring says the soundness facts of `gmXG` are "those listed there" (in `CM4E/MX.lean`), but `MX.lean` no longer contains `gmX` or any soundness list; (b) `Lattice.lean` l. 32 mentions `gmX`; (c) `Waldschmidt.lean` l. 12 mentions `MX.Thm11KappaMX`, which no longer exists. So the soundness facts of `gmXG` are stated nowhere in the source, contrary to `Waldschmidt.lean`'s own policy |
| 15 | COSMETIC | `Final.lean` module docstring | lists the MX inputs as `hg₂'`, `hg₃'`, `hΓ`, `hM` and omits `WuestholzMX`, `MasserCM`, `LaurentZeta` (TRUST.md lists them correctly) |
| 16 | COSMETIC | `mx1` hypotheses | `hu : u ∉ lattice` is implied by `hu' : u ∉ ℚ(i)ϖ`; harmless |
| 17 | NOTE | not formalised | the "in particular" clauses of Thm MX, the `E_ρ`-symmetric half of MX1, and the Γ-value form of MX1. Prop. D is formalised only for `v ∈ Ψ(Λ(G))` (as in REFEREE_HYP_MX #16) |
| 18 | TRUST NOTE (inherited) | `d₀ = 1` regime; second application in W88 §5d | as REFEREE_HYP_MX #15. Lemma U is checked only for the first application of W88 Thm 4.1 inside §5d (paper, after `thm:W88k`) |

## Details

### 1–2. `alg`, `lam`, `per` for general `K`: OK [Proved]

**Set-up.** `U = {z_i = z_ρ = 0, θᵀa₁ = 0, θᵀ(w_i + w_ρ + a₂) = 0} ⊂ G^n`.
* U lies in the kernel of `G^n → A = E_i^n × E_ρ^n`, which is a vector group. It is cut out by `ℚ̄`-linear equations
  (`θ ⊂ K ⊂ ℚ̄`; `hb.alg` and `I ∈ ℚ̄`). So U is a connected vector subgroup over `ℚ̄`, of dimension `4n − 2`.
* The `2n + 2` forms `s₁ = θᵀa₁`, `z_i`, `z_ρ`, `s₂ = θᵀ(w_i + w_ρ + a₂)` are linearly independent with
  `ℚ̄`-coefficients. So they form a `ℚ̄`-basis of `T_U^⊥ = T(G″)^*`, and `algXG` (all coordinates algebraic) is the
  quotient `ℚ̄`-structure. This uses REFEREE_HYP_MX #2, that `(z, w, a)` are `ℚ̄`-rational on `T(G^n)`.

**`lam`.**
* The images of copy-`h` vectors are `gXI` / `gXR` / `gXA`: `(0, z e_h, 0, θ_h w)`, `(0, 0, z e_h, θ_h w)` and
  `(θ_h a, 0, 0, θ_h t)`.
* `LogNat` = Λ(E^♮) (REFEREE_HYP_MX #1), and `Λ(G″)` is a `ℚ`-space. So `span_ℚ lamGenX ⊂ Λ(G″)`.
* Nothing here depends on `K` beyond `θ ⊂ ℚ̄`.

**`per`.**
* `GX1 = (ϖ, π/ϖ)` and `GX2 = (iϖ, −iπ/ϖ)` are `(λ, η(λ))` for `λ = ϖ, iϖ`.
* `HX1 = (Ω_ρ, η_ρ)`, and `HX2 = (ρΩ_ρ, ρ̄η_ρ)`. The latter is a period because `ζ(ρz) = ρ̄ζ(z)`, so
  `η(ρλ) = ρ̄η(λ)`. Its value was checked numerically in REFEREE_HYP_MX (table: `η(ρΩ_ρ) = −0.746834 − 1.293555i`).
* Ker exp_{G″} is the image of Ker exp_{G^n}, since U is connected. The image map is injective (z = 0 forces λ = 0).
  So `perXG = ℚ ⊗ Ker exp_{G″}`, of rank `4n`, and κ cannot be inflated. This holds for every `K`.

### 3, 5. `sub` for every `K`, and what soundness needs: OK [Proved]

I reran the argument of REFEREE_HYP_MX #8 for general θ. Let `H ⊂ G″` be nonzero and connected.

* **`H` meets `G_a × F` in positive dimension.** Then `T_H ∋ (c, 0, 0, d) ≠ 0`, with `Ψ″`-image `(c, d) ≠ 0`.
* **Otherwise.**
  - `H ≅ B = B_i × B_ρ ≠ 0`. Since `Hom(B, G_a) = 0`, `H = 0 × H′` with `H′` a splitting of `G_ℓ` over B.
  - A splitting forces `φ(S_i) = φ(S_ρ) = 0`. The reason is the fibre character `diag(a, ā)` together with the
    anti-affine image of `B^♮`; neither depends on `K`.
  - On the graph over `T_B`, `Ψ″₁ = θᵀz_i + θᵀz_ρ`, which takes the value `ψ_i(m) + ψ_ρ(m′)` on `(σ(m), σ(m′))`.
* **What is needed.** For `k = ℚ(i)` and `k = ℚ(ρ)`, there must be no nonzero `m ∈ k^n` with `ψ(m) = φ(m) = 0`.
  Write `m = u + ωv` with `u, v ∈ ℚ^n` and `ω ∈ {i, ρ}`. Then:
  - `ψ(m) − φ(m) = (ω − ω̄) θᵀv`, so `θᵀv = 0` and hence `v = 0`;
  - then `ψ(m) = θᵀu = 0` gives `u = 0`.

  This uses only the `ℚ`-independence of θ (`hb.indep`). Lemma K's field-theoretic proof (`k ⊂ K`) is not needed for
  this half. In particular **`ρ ∈ K` is not needed**. For `ρ ∉ K`, `ψ_ρ` is even injective, because `1, ρ` are
  `K`-independent. The identities are sampled numerically in `check_mxg.py` for `K = ℚ(i, √2)`, where `ρ ∉ K`.
* **Conclusion.** `T_H` is `ℚ̄`-rational, so it contains an algebraic `x` with `Ψ″x ≠ 0`, and `sub` holds.
* **Necessity of independence.** If θ were `ℚ`-dependent, a rational `m` with `θᵀm = 0` would give a splitting
  `s(B) ⊂ 0 × G_ℓ` with `T ⊂ ker Ψ″`, and `sub` would fail. So `ℚ`-independence is genuinely needed, and it is
  assumed.
* **Scope of the hypothesis.** `Thm11KappaMXG` quantifies over all adapted bases. That includes `K = ℚ(i)` (`r = 1`)
  and fields without `√3`. Every such instance is sound, so the hypothesis is not stronger than W88 §5d.
* **The docstring.** The `MXGen` docstring claim "do not depend on `K`" is correct.

### 4. `d₀, d₁, d₂`: OK [Proved]

* θᵀw_i is a nonzero form, so `G_ℓ` is the push-out of `A^♮` along an onto form and is a quotient of `A^♮`.
  Hence it is anti-affine: `Hom(G_ℓ, G_a) = Hom(G_ℓ, G_m) = 0`.
* So `Hom(G″, G_a)` is 1-dimensional, and `d₀ = 1`, `d₁ = 0`, `d₂ = 2n + 1` are maximal for every `K`.
* Lean: `d₂ = 2·card(Fin r × Fin 2) + 1` and `finrank TXG = 2n + 2`.

### 6. Lemma U range: OK [Proved]

* `N = d − 1 = 2n + 1`, `d₁ + 2d₀ = 2`, and `κ ≤ rk(V ∩ Ker exp) ≤ 4n`. So `2N = 4n + 2 ≥ 2 + κ` for **every**
  hyperplane, and hence for every instance of `HyperplaneKappa (gmXG b)` and every `K`.
* Equality requires all periods in `V`, i.e. `V = T(G_ℓ)`; that case is still in range.
* The paper's "4n + 2 ≥ 2n + 2" is the `κ = 2n` case.
* The caveat stated in the paper carries over: the condition is checked only for the first application of Thm 4.1
  inside W88 §5d (#18).

### 7–8. The proof of `mx_K`: OK (faithful to Remark 26)

* **Field.** `exists_adapted_basis I … {β, r3}` gives `r ≥ 2` and `K ∋ i, β, √3`, hence `ρ, ρ̄ ∈ K` (`rho_mem`).
  So `K ⊇ ℚ(i, √−3, β)` and `n = 2r ≥ 4`, as in the paper.
* **Lifts.**
  - `liftI x y` solves `U + iV = x`, `U − iV = y`.
  - `liftR x y` solves `U + ρV = x`, `U + ρ̄V = y`, i.e. `V = (x − y)/(ρ − ρ̄)` and `U = x − ρV`. This needs
    `ρ ∈ K`.
  - `coordsK` is defined by `Classical.epsilon`. It is used only through `coordsK_spec` for elements of `K`, and all
    membership side conditions are discharged.
  - `P1 h ↦ θ_h(ϖ, βη_ρ) = θ_h w₁`, and `P2 h ↦ θ_h(Ω_ρ, β(2/√3)π/ϖ) = θ_h w₂` (`2√3/3 = 2/√3`). Both are in
    `perXG`.
  - `DX h` is the θ_h-copy of `(X, Y, a, t)`, which lies in `lam`.
* **`V″` and `W″`.**
  - All 3n generators lie in `V″ = ker(βη_ρΨ″₁ − ϖΨ″₂)`. For `P2` this is Legendre `η_ρΩ_ρ = 2π/√3`
    (`etaRho_mul`), and for `DX` it is `hrel`.
  - `W″ = span{(−θ_j, e_j, 0, 0), (−θ_j, 0, e_j, 0)}` is rational, of dimension 2n, and contained in `V″`.
* **Independence.**
  - Suppose `Σ g·y = 0`. Applying `Ψ″₁` gives `Aϖ + BΩ_ρ + C(z_X + z_Y + a) = 0`, with `A, B, C = θᵀ(g-blocks) ∈ K`.
  - If `C ≠ 0`, this contradicts the negated conclusion. If `C = 0` and `B ≠ 0`, it contradicts `hM`.
  - Otherwise `θ`-independence gives `g = 0`.
  - This is the paper's Step 1 with `L = 0`, together with "w₁, w₂ are `K`-independent".
* **Count.** `m = 3n` and `κ ≥ 2n` (the `2n` period lifts are independent and in `per`). (5.4) reads
  `3n > (4n + 2 − κ)·1`, which holds since `3n > 2n + 2` for `n ≥ 4`.
* **Exclusion.**
  - There is an algebraic `x ∈ S ⊂ V″` with `Ψ″x ≠ 0`.
  - `Ψ″₂x = 0` would force `Ψ″₁x = 0`, since `βη_ρ ≠ 0`. So `ϖ = βη_ρΨ″₁x/Ψ″₂x`, and
    `ϖΩ_ρ/π = 2βΨ″₁x/(√3Ψ″₂x) ∈ ℚ̄`, which contradicts `hΓ`.
  - This is exactly the second derivation in Remark 26, including its dependence on `ϖ/η_ρ ∉ ℚ̄`.
  - The paper's Step 4 (the first derivation, from W88 Thm 4.1) avoids `hΓ`. Lean does not formalise it, as is
    documented.

No gap found. The only use of `β` beyond `β ∈ K` is `β ≠ 0` in the exclusion, and that hypothesis is present.

### 9. `WuestholzMX`: TRUE [Proved modulo Wüstholz 1989]

* **Set-up.** By `LogNat`, `z_X ∈ Λ(E_i)` and `z_Y ∈ Λ(E_ρ)`; the first disjunct gives lattice points, which are
  logarithms of the origin. `w_X, w_Y` play no role. Put `u = (z_X, ϖ, z_Y, Ω_ρ, a) ∈ Λ(E_i² × E_ρ² × G_a)` and
  `L = z₁ − xz₂ + z₃ − x′z₄ + s`, so `L(u) = 0`.
* **Products.** The smallest algebraic `H` with `u ∈ T_H` is a product `B_i × B_ρ × H_a`. The reason is that the
  three factors have no common nonzero subquotient: the curves are non-isogenous, and `Hom` between `G_a` and an
  abelian variety is 0 in both directions.
* **Conclusion.** Wüstholz gives `L|_{T_H} = 0`.
  - If `a ≠ 0`, then `H_a = G_a`, and `L(0, …, 0, 1) = 1 ≠ 0`, a contradiction. So `a = 0`.
  - `(z_X, ϖ) ∈ T_{B_i}` and `L` vanishes there, so `z_X = xϖ`. Likewise `z_Y = x′Ω_ρ`.
* **Premises.** The curves must be defined over `ℚ̄`. This is true (`g₂ = 4, g₃ = 0` and `g₂ = 0, g₃ = 4`), so the
  unconditional Lean statement is true.
* **Docstring.** Using `a` (rather than 1) as the `G_a`-coordinate works as written.

### 10. `MasserCM`: TRUE [Proved modulo Wüstholz] + [Lit]

* **Argument.** Suppose `z ∈ Λ(E_i)`, `z = xϖ` with `x ∈ ℚ̄`. The smallest `H ⊂ E_i²` with `(z, ϖ) ∈ T_H` has
  `T_H ⊂ ker(z₁ − xz₂)`, so `H ≠ E_i²`. Since `ϖ ≠ 0`, H is an elliptic curve `{(αP, βP)}` with
  `α, β ∈ ℤ[i]` and `β ≠ 0`. Its tangent space is `ℂ(α, β)`, because `[i]` acts on the tangent space as
  multiplication by `i` (the lattice is `iΛ = Λ`). So `x = α/β ∈ ℚ(i)`.
* **Same for `E_ρ`,** with `ℚ(ρ) = {p + qρ}`.
* **Lattice points** give `x = m + ni`, resp. `m + nρ`, as they should.
* **Citation.** Masser's LNM 437 contains the CM case of the elliptic Baker theorem: logarithms that are
  `k`-independent are `ℚ̄`-independent together with 1. This gives the statement directly. That is recalled, not
  checked against the source [Lit].

### 11. `LaurentZeta`: TRUE [Proved modulo Wüstholz]

* **Set-up.** Suppose `u ∉ Λ` and `℘(u), ℘′(u) ∈ ℚ̄`. Then `(u, ζ(u)) ∈ Λ(E_i^♮)` (exp `= (℘, ℘′, 0)`). The `ζ` is
  the standard Weierstrass series (`zetaSummand 0 z = 1/z`). If `ζ(u) = c ∈ ℚ̄`, apply Wüstholz to
  `v = (u, ζ(u), 1) ∈ Λ(E^♮ × G_a)` and `L = w − cs`.
* **Projections.** The smallest `H ∋ v` projects onto `E` (since `u ≠ 0`) and onto `G_a`, and `H ≠ G` (since
  `L ≠ 0`). So `dim H = 2`, and `ker(H → E)°` is a line `ℓ ⊂ F × G_a`. Each possible line gives a contradiction:
  - `ℓ = F × 0` would make `H/F ⊂ E × G_a` a 1-dimensional subgroup onto both factors, which is impossible;
  - `ℓ = 0 × G_a` would make `H = H′ × G_a` with `H′` a splitting of `E^♮`;
  - a skew line would make `H/ℓ` a splitting of `(E^♮ × G_a)/ℓ ≅ E^♮`.

  `E^♮` is non-split, so `ζ(u) ∉ ℚ̄`.
* **The hypothesis.** The argument uses only `u ∉ Λ`, so the extra hypothesis `u ∉ ℚ(i)ϖ` (non-torsion) only
  weakens the statement. For instance, for torsion `u = ϖ/2`, `ζ(u) = π/(2ϖ)` is transcendental anyway.
* **Citation.** The paper cites Laurent, C. R. Acad. Sci. 290 (1980) (`La80`) and also Wüstholz on `E^♮ × G_a`.
  I did not check La80 [Lit, unverified]; the Wüstholz route suffices.

### 12. `hΓ`, `hM`: TRUE [Proved modulo Wüstholz]

* **`hΓ`.** As in REFEREE_HYP_MX #14: apply Wüstholz to the period `(ϖ; Ω_ρ, η_ρ)` of `E_i × E_ρ^♮`.
  - `Hom` vanishes in both directions between `E_i` and `E_ρ^♮`, and `E_ρ^♮` has no subgroups other than 0, F and
    itself. So the smallest subgroup is all of `E_i × E_ρ^♮`, and `ϖ ∉ ℚ̄η_ρ`.
  - Since `ϖ/η_ρ = (√3/2π)ϖΩ_ρ`, this gives `hΓ`.
* **`hM`.** `transcendental_omegaRho_div_varpi` derives `hM` from `WuestholzMX` (`z_X = 0`, `z_Y = Ω_ρ`,
  `x = Ω_ρ/ϖ`). This is correct.
* **Numerical check [Numerical].** `findpoly` with degree ≤ 8 and coefficients ≤ 10⁸, at 80 digits, finds no
  relation for `ϖΩ_ρ/π`, `Ω_ρ/ϖ`, `ζ(u)` (at `℘(u) = 2`) or the MX1 value. This is a sanity check only.

### 13. `mx_full`, `mx1` and the `Final` wrappers: faithful

* **`mx_full`.** It concludes `a = 0`, `z_X = (p + qi)ϖ` and `z_Y = (p′ + q′ρ)Ω_ρ` (with `p, q, p′, q′ ∈ ℚ`) for every
  `β ∈ ℚ̄ˣ`. This is thm:MX's main clause.
  - Its hypotheses match the paper: `X, Y ∈ Λ(E^♮)` via `LogNat`, `a, t ∈ ℚ̄`, and the relation
    `(z_X + z_Y + a)βη(Ω_ρ) = (w_X + w_Y + t)ϖ` with `η(Ω_ρ) = etaRho = 2π/(√3Ω_ρ)`.
  - The proof chain (`mx_K`, then `WuestholzMX`, then `MasserCM`) is the paper's "Granting Proposition D" paragraph.
* **`mx1`.** The proof splits on the value `q` of the ratio.
  - **`q = 0`.** Then `ζ(u) + t = 0`, using `u + a ≠ 0`, and this contradicts `LaurentZeta`.
  - **`q ≠ 0`.** Put `β = q√3/2 ∈ ℚ̄ˣ`. Then `(u + a)βη_ρ = (ζ(u) + t)ϖ`; this is Lean-proved, and the residual is
    4·10⁻⁸¹ in `check_mxg.py`. `mx_full` with `X = (u, ζ(u))`, `Y = 0` then gives `u ∈ ℚ(i)ϖ`, contradicting `hu'`.
  - This is the paper's derivation ("the case X = (u, ζ_i(u)), Y = 0; the value 0 … excluded separately").
* **Schneider step.** In Lean `x/0 = 0`, so `Transcendental(…)` implicitly asserts `u + a ≠ 0`. That is true: if
  `u = −a ∈ ℚ̄` with `u ∉ Λ`, Schneider (`wp_transcendental`, proved in `Ext/`) makes `℘(u)` transcendental, contrary
  to `hwp`. The step is correctly used and necessary.
* **The paper's illustration** reproduces to all printed digits [Numerical]: `u = 0.72694593546890819853…` and
  `ϖΩ_ρζ(u)/(πu) = 3.76379062156897182773…` (Laurent series of ℘ and ζ, 80 digits).
* **Wrappers.**
  - `Final.mx_K`, `Final.mx` and `Final.mx1` only discharge `g₂, g₃(ϖℤ[i])`.
  - `Final.mx_K` keeps `hM` as an explicit hypothesis, which is weaker than assuming `WuestholzMX`. This matches
    TRUST.md rows 26–28.

### 14–16. Cosmetic

* **#14.** Suggested fix: put the soundness facts in `gmXG`'s docstring, since `MX.lean` no longer has them. They
  are:
  - `algXG` is the quotient `ℚ̄`-structure;
  - `lam` ⊂ Λ(G″);
  - `perXG = ℚ ⊗ Ker exp_{G″}`;
  - every nonzero connected `H` has an algebraic `x ∈ T_H` with `Ψ″x ≠ 0`, with the two clauses of
    REFEREE_HYP_MX #9 and the remark that only the `ℚ`-independence of θ is used;
  - `d₀ = 1` is maximal.

  Also update or remove the `gmX` mention in `Lattice.lean` and the `MX.Thm11KappaMX` mention in `Waldschmidt.lean`.
* **#15.** In the `Final.lean` module docstring, add `WuestholzMX`, `MasserCM` and `LaurentZeta` to "What remains
  assumed".
* **#16.** Drop `hu` from `mx1` (it follows from `hu'`), or leave it as documentation.

### 17–18. Notes

* **#17.** Not formalised:
  - the "in particular" sentence of thm:MX (non-torsion `u, u′`), which follows from `mx_full` with
    `X = (u, ζ_i(u))` and `Y = (u′, ζ_ρ(u′))`;
  - MX1's `E_ρ` half;
  - the Γ-value reformulation.

  TRUST row 107 is accurate as written.
* **#18.** Unchanged from REFEREE_HYP_MX #15: this is a model with `d₀ = 1`, `W ≠ 0`, `κ > 0` and a non-semiabelian
  `G₂`. An expert check of W88 §§6–7 should cover these together, and also the second application inside §5d, for
  which Lemma U's range is not checked.

## Falsification attempts (none succeeded)

* **Fields without `√3`, or `K = ℚ(i)`.** The model stays sound (#3, #5), so the "∀ adapted b" quantifier does not
  overstate W88.
* **A `ℚ`-dependent θ.** It would break `sub`, but it is excluded by `IsAdaptedFieldBasis.indep`.
* **Spurious κ.** `per` is exactly `ℚ ⊗ Ker` (#2). Lean uses only `κ ≥ 2n`.
* **False named inputs (the vacuity risk).** All four (`WuestholzMX`, `MasserCM`, `LaurentZeta`, `hΓ`) were derived
  from Wüstholz's theorem.
  - The edge cases were checked: lattice points in `LogNat`, `a = 0`, `z = 0`, and torsion `u` (excluded, and true
    anyway).
  - The premises `g₂, g₃ ∈ ℚ̄` are true. So none of the theorems is vacuous through its hypotheses.
* **Division by zero in MX1.** Handled correctly by Schneider (#13).
