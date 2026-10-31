# Referee report: is `Thm11KappaMX` (model `gmX`) a true consequence of W88 §5d, and is `MX.main` honest?

> **Status (added when the report was filed in `reviews/`).** Reviewed `CM4E/MX.lean` at commit `c0d7d93`. Its
> cosmetic findings were applied in `4437373`. Later refactors replaced the file's own copy of the `ζ` series by the
> identical `CM4E.Ext.Weierstrass.zeta` and `MX.OmegaRho` by the identical `CM4E.omegaRho`. Scripts and outputs are in
> `checks/hypmx/`.

Referee: adversarial AI reviewer (Claude), 2026-10-30. No project file other than this report was edited, and no git
command was run. Scratch scripts and their outputs are in
`checks/hypmx/`:
* `check.py` / `check.out`: Γ-values, g₂ and g₃ from q-series, η from E₂, Legendre, and direct sums of the Lean `ζ`
  series. These cover η of lattice vectors, ζ(iz), ζ(ρz), Legendre, the curve equations, the addition cocycle and
  ∫℘.
* `lemmaK.py` / `lemmaK.out`: exact sympy checks of Lemma K for both k, plus the Legendre identities used by
  `preW2` / `V''`.

Sources read:
* `CM4E/MX.lean` and `CM4E/Waldschmidt.lean`, in full.
* Mathlib's `PeriodPair` definitions (`weierstrassP`, `derivWeierstrassP`, `G`, `g₂ = 60 G 4`, `g₃ = 140 G 6`).
* `REFEREE_HYP_NAT.md`, and TRUST.md rows 22–24 and 54.
* From the paper: Theorem MX, §"Theorem MX" (Set-up, Prop. D, Steps 1–4, Remark "The count", Remark `rem:gamma`),
  Theorem `thm:W88`, Lemma `lem:K`, Lemma `lem:natural`, and Appendix A (Lemma U).
* The W88 scans w88-01, w88-02 (Thm 1.1), w88-10 (Lemmas 5.1, 5.2) and w88-11 (§5d, (5.4)).

## Verdict: CORRECT (with cosmetic caveats and one trust note)

I found no encoding bug that would make `HyperplaneKappa gmX` stronger than W88 Thm 1.1 with (5.4) for
G″ = G_a × G_ℓ. Each field of the model is sound, and in the right direction:
* `lam` ⊂ Λ(G″);
* `per` is exactly ℚ ⊗ Ker exp_{G″};
* every connected algebraic subgroup satisfies `sub`;
* (d₀, d₁, d₂) = (1, 0, 9) is W88's maximal decomposition.

The premises g₂, g₃ ∈ ℚ̄ are true, and so are `hΓ` and `hM` (Wüstholz). `MX.main` is an honest statement of
Proposition D, restricted to v ∈ Ψ(Λ(G)) and β ∈ ℚ(i, √3)ˣ. The residual risk is the one already flagged in TRUST.md:
the κ-term of W88 §§6–7 itself. A new point: this is the first model with **d₀ = 1** (see #15).

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `LogNat` | equals Λ(E^♮) exactly (both inclusions) for exp(z, w) = (℘, ℘′, w − ζ(z)) |
| 2 | OK | E^♮ model, ℚ̄-structure | the cocycle is rational over ℚ̄; the extension is non-split, so it is the universal vector extension; (z, w) are ℚ̄-rational tangent coordinates; [a] acts by diag(a, ā) |
| 3 | OK (verified) | `etaI`, `etaR`, `etaRho` | the true η of the Lean `ζ`: ζ(iz) = −iζ(z), ζ(ρz) = ρ̄ζ(z), Legendre = 2πi on both lattices |
| 4 | OK (verified) | `OmegaRho`, `varpi` | Ω_ρℤ[ρ]: g₂ = 0, g₃ = 4. ϖℤ[i]: g₂ = 4, g₃ = 0 (40 digits) |
| 5 | OK | `lam` | ℚ-span of images of Λ(G⁴) ⊂ Λ(G″) |
| 6 | OK | `genI/genR/genA`, `psi1/psi2` | match the quotient by U and Ψ″ = Φ mod T_U exactly |
| 7 | OK | `perX` | equals ℚ ⊗ Ker exp_{G″} (rank 16), so κ cannot be inflated; H2 is a genuine period |
| 8 | OK | `sub` (docstring fact 4) | true: every nonzero connected H ⊂ G″ has T_H ⊄ ker Ψ″. Independent proof below |
| 9 | COSMETIC | fact 4 write-up | two one-line steps are implicit: the G_a-component of a splitting is 0, and why a splitting forces φ(S) = 0 |
| 10 | OK (exact) | Lemma K | for θ = (1, i, √3, i√3): det(ψ, φ) = 16 for ℚ(i) and 9 for ℚ(ρ); dim_ℚ ker ψ = dim_ℚ ker φ = 4; intersection 0 |
| 11 | OK | d₀ = 1, d₁ = 0, d₂ = 9 | maximal (Hom(G″, G_a) is 1-dim, Hom(G″, G_m) = 0); (5.4) and Lemma 5.2 do not involve d₀ |
| 12 | OK | Lemma U range | 2N = 18 ≥ d₁ + 2d₀ + κ = 2 + κ for every instance, since κ ≤ 16; tight only at V = T(G_ℓ) |
| 13 | OK | `main`: V″, W″, Y″, κ | preW1, preW2 ∈ V″ by Legendre; κ ≥ 8 is legitimate; 12 > 18 − κ |
| 14 | OK / COSMETIC | `hΓ`, `hM` | true by Wüstholz 1989 (derivation below). The "Masser 1975" attribution for Ω_ρ/ϖ ∉ ℚ̄ is unverified; Wüstholz alone suffices |
| 15 | TRUST NOTE | d₀ = 1 regime | first model using W88 with a G_a factor (the Gelfond part, b > 1, case δ = τ); this regime was not covered by earlier reviews |
| 16 | COSMETIC | name "Proposition D (K-form)" | Lean proves it for v ∈ Ψ(Λ(G)), not for v ∈ Ψ(Λ_K(G)); this suffices for Theorem MX |
| 17 | NOTE (positive) | robustness, non-vacuity | the η formulas hold for every ωℤ[i], ωℤ[ρ]; all premises are true and LogNat is satisfiable, so `main` is not vacuous |

## Details

### 1–2. `LogNat` = Λ(E^♮), and the model of E^♮: OK [Proved]

* **Group law.** Put s = w − ζ(z). Then exp(z+z′, w+w′) has
  s″ = s + s′ − c(z, z′), where c(u, v) = ζ(u+v) − ζ(u) − ζ(v) = ½(℘′(u) − ℘′(v))/(℘(u) − ℘(v)). This is a rational
  function over ℚ̄ (g₂, g₃ ∈ ℚ̄) of the two points. Numerically the residual is 5·10⁻¹¹ (E_i) and 7·10⁻¹² (E_ρ),
  from the direct Lean-series sums.
  - So the image of exp is a G_a-torsor over E with transition s ↦ s + f near O, where f = −y/(2x). It is a group
    over ℚ̄.
  - The extension is non-split. A splitting would make ζ − (rational function) additive, hence η(λ) = cλ, which
    contradicts Legendre.
  - Ext¹(E, G_a) is one-dimensional, so this group is the universal vector extension over ℚ̄, up to scaling the
    G_a.
* **Periods and the fibre over O.** ζ(z+λ) = ζ(z) + η(λ), so (λ, η(λ)) ∈ Ker exp and exp(λ, w) = exp(0, w − η(λ)).
  The map c ↦ exp(0, c) is the vector subgroup, an isomorphism over ℚ̄ onto the fibre. Hence exp(λ, w) ∈ E^♮(ℚ̄)
  iff w − η(λ) ∈ ℚ̄. This is the first disjunct of `LogNat`.
  - Off the lattice, (℘, ℘′, s) are regular functions over ℚ̄ on E^♮|_{E∖O} ≅ (E∖O) × G_a. That gives the second
    disjunct.
  - Both inclusions hold, so `LogNat` is exactly Λ(E^♮). Only ⊂ is needed.
  - m and n are unique, since ω₁ and ω₂ are ℝ-independent. The 1/0 = 0 convention is harmless, because the second
    disjunct requires z ∉ L.
* **ℚ̄-structure.** Near O, the functions t = −2x/y = z + O(z⁵) and σ = s − y/(2x) = w − (ζ − f)(z) = w + O(z³) are
  ℚ̄-rational local parameters. I computed ζ − f = (g₂/12)z³ + … from the Laurent series. Their differential at 0 is
  the identity in (z, w), so ∂_z and ∂_w are ℚ̄-rational, and so is the vector-group coordinate w.
* **CM action.**
  - [i] on E_i: exp(iz, −iw) = (−℘, i℘′, −i(w − ζ)), which is algebraic in exp(z, w). So [i] acts by diag(i, −i).
  - [ρ] on E_ρ: exp(ρz, ρ̄w) has third coordinate ρ̄(w − ζ). So [ρ] acts by diag(ρ, ρ̄).
  - This is the "conjugate character on the fibre" used in Step 3 (κ₁ = 0 for both curves).
* **Sign.** ∫℘ over the period ϖ is −1.19814 = −η(ϖ). So w is dual to −x dx/y. This is harmless, and it causes no
  docstring problem here, because MX.lean defines the coordinates through exp rather than through differentials.
  This differs from REFEREE_HYP_NAT #7.

### 3. Quasi-periods: OK [Proved] + [Numerical]

* **Derivation.** For a lattice stable under multiplication by a unit u, ζ(uz) = u⁻¹ζ(z), so η(uλ) = ū η(λ). Then
  Legendre, η(ω₁)ω₂ − η(ω₂)ω₁ = 2πi with Im(ω₂/ω₁) > 0, gives:
  - for (ϖ, iϖ): 2iϖη(ϖ) = 2πi, so η(ϖ) = π/ϖ;
  - for (Ω, ρΩ): η(Ω)Ω(ρ − ρ̄) = 2πi, so η(Ω) = 2π/(√3Ω).
  Hence `etaI m n` = (m − ni)π/ϖ and `etaR m n` = (m + nρ̄)η_ρ. Exact sympy confirms the ρ-Legendre identity and
  1 + 2ρ = i√3, 1 + 2ρ̄ = −i√3.
* **q-series** (40 digits): E₂(i) = 3/π and E₂(ρ) = 2√3/π. So η(ω₁) = (π²/3ω₁)E₂ equals π/ϖ and 2π/(√3Ω_ρ), with
  error about 2·10⁻⁴¹.
* **Direct Lean series.** Box |m|, |n| ≤ 700, double precision, with the l = 0 term 1/z exactly as in Lean (`1/0 = 0`).
  The truncation error is about 10⁻⁵.

| quantity | direct ζ(z₀+λ) − ζ(z₀) | Lean constant |
|---|---|---|
| η(ϖ) | 1.1981406 | etaI 1 0 = 1.1981402 |
| η(iϖ) | −1.1981405i | etaI 0 1 = −1.1981402i |
| η((2−3i)ϖ) | 2.39627 + 3.59442i | 2.39628 + 3.59442i |
| η(Ω_ρ) | 1.4936688 | etaR 1 0 = 1.4936684 |
| η(ρΩ_ρ) | −0.746834 − 1.293555i | etaR 0 1 = −0.746834 − 1.293555i |
| η(i√3 Ω_ρ) (H2) | −2.5871102i | etaR 1 2 = −i√3 η_ρ = −2.5871096i |
| η((3−2ρ)Ω_ρ) | 5.97465 + 2.58708i | 5.97467 + 2.58711i |
| Legendre, E_i / E_ρ | 6.283187i / 6.283188i | 2πi = 6.283185i |
| ζ_i(iz) + iζ_i(z) | ≤ 6·10⁻¹⁷ | 0 |
| ζ_ρ(ρz) − ρ̄ζ_ρ(z) | ≤ 4·10⁻⁸ | 0 |

### 4. g₂, g₃: OK [Numerical]

* Mathlib uses g₂ = 60 Σ′ l⁻⁴ and g₃ = 140 Σ′ l⁻⁶, with the l = 0 term 0⁻¹ = 0.
* Ω_ρ = Γ(1/3)³/(2^{4/3}π) = 2.42865064788758161… gives:
  - g₂ = (4π⁴/3)E₄(ρ)/Ω⁴ = 1·10⁻⁴⁰ (exactly 0 by ρ-symmetry);
  - g₃ = (8π⁶/27)E₆(ρ)/Ω⁶ = 4.0000… (40 digits).
* ϖ = 2.62205755429211981… gives g₂ = 4.000… and g₃ = 2·10⁻⁴¹ (g₃ = 0 is proved in Lean).
* The direct ℘ series satisfies ℘′² = 4℘³ − 4℘ and ℘′² = 4℘³ − 4, up to 10⁻⁶–10⁻⁵ against |℘′²| ≈ 20–680
  (truncation).

### 5–6. `lam` and the generators: OK [Proved]

* **The quotient by U.** T_U is *defined* as the joint kernel of the ten forms s₁ = θᵀa₁, z_i (4), z_ρ (4) and
  s₂ = θᵀ(w_i + w_ρ + a₂).
  - So these forms are a basis of T_U^⊥ ≅ T(G″)*. dim U = 24 − 10 = 14 = 4n − 2, and dim G″ = 10.
  - The forms have coefficients in K, and the coordinates (z, w, a) on T(G⁴) are ℚ̄-rational (#2). So `algX` (all ten
    coordinates algebraic) is exactly the quotient ℚ̄-structure.
  - U is a vector subgroup (it lies in z = 0), defined over ℚ̄.
* **Images.** A vector of copy h of E_i^♮ maps to (0, z e_h, 0, θ_h w), which is `genI`. Likewise for `genR`, and
  (a e_h, t e_h) on G_a² maps to (θ_h a, 0, 0, θ_h t), which is `genA`.
* **Ψ″.** Φ = Ψ ∘ p_θ = (θᵀz_i + θᵀz_ρ + θᵀa₁, θᵀ(w_i + w_ρ + a₂)), which is (`psi1`, `psi2`).
* **G″ = G_a × G_ℓ.** G_a⁴(a₁)/{θᵀa₁ = 0} ≅ G_a. The rest is (A^♮ × G_a⁴(a₂)) modulo the relations, which is the
  push-out of A^♮ along θᵀ(w_i + w_ρ). This is the paper's description.
* **Λ(G″) is a ℚ-vector space.** [N] on G″ is a finite surjective morphism over ℚ̄ (an isogeny on A, an isomorphism on
  the vector part). So N-division points of ℚ̄-points are ℚ̄-points.
  - The quotient map is defined over ℚ̄, so it sends Λ(G⁴) into Λ(G″). Hence span_ℚ(`lamGen`) ⊂ Λ(G″).
  - The ℚ-span versus ℤ-span reduction is the one in REFEREE_HYP 1(d): rk(Y_ℤ) = dim_ℚ Y_ℚ, and
    rk(Y_ℤ ∩ Ker) = dim_ℚ(Y_ℚ ∩ Ω_ℚ) ≥ dim_ℚ(Y_ℚ ∩ per).

### 7. `perX`: OK, in fact equality [Proved]

* U is connected, so Ker exp_{G″} is the image of Ker exp_{G⁴}. Since exp(x) ∈ U = exp(T_U), x ∈ T_U + Ker.
* G1 and G2 (copy j) are (ϖ, η(ϖ)) and (iϖ, η(iϖ)); H1 and H2 are (Ω, η_ρ) and ((1+2ρ)Ω, η((1+2ρ)Ω)). These are
  genuine periods (#3; H2 numerically −2.5871102i against −2.5871096i). Their images span the image of
  Ker exp_{G⁴} ⊗ ℚ.
* The 16 generators are ℚ-independent. Their z-parts are ϖe_j, iϖe_j, Ωe_j, i√3Ωe_j, and ϖ, iϖ (resp. Ω, i√3Ω) are
  ℝ-independent.
* rk Ker exp_{G″} = 16 = rk H₁(A). There is no extra period, since T_U ∩ Ker = 0 (z = 0 forces λ = 0).
* So perX = ℚ ⊗ Ker exp_{G″}, and κ in the Lean statement is W88's κ.

### 8–9. `sub`: every nonzero connected algebraic H ⊂ G″ has T_H ⊄ ker Ψ″. OK [Proved]

ker Ψ″ = {s₂ = 0, s₁ = −θᵀz_i − θᵀz_ρ}. Let π : G″ → A = E_i⁴ × E_ρ⁴, with kernel G_a × F. The tangent space of
G_a × F is span{(1,0,0,0), (0,0,0,1)}.

* **Case H ∩ (G_a × F) ≠ 0.** An algebraic subgroup of G_a² in characteristic 0 is a ℂ-subspace, so T_H ∋ (c,0,0,d) ≠ 0,
  with Ψ″-image (c, d) ≠ 0. ✔
* **Case H ∩ (G_a × F) = 0.** Then H → B := π(H) is an isomorphism and B ≠ 0. Hom(E_i, E_ρ) = 0 (different CM
  fields), so B = B_i × B_ρ, with B_• = B_{S_•} for k_•-subspaces S_• ⊂ k_•⁴ and T_{B_•} = ℂσ(S_•).
  - (a) The projection of H to G_a is a homomorphism from an abelian variety to G_a, hence 0. So H = 0 × H′, with H′ a
    splitting of G_ℓ over B. ***The docstring skips this step*** (it is needed for "Ψ″₁ = θᵀz on T_H").
  - (b) A splitting forces φ(S_i) = φ(S_ρ) = 0. If φ(m) ≠ 0 for some m ∈ S_•, consider the image J in G_ℓ of
    (E_•^♮)^b under the matrix M with column space S_•.
    - Its tangent space is ℂσ(S) × ℂσ̄(S), by functoriality and diag(a, ā).
    - J contains (0, φ(m)), i.e. the fibre direction. J is anti-affine (a quotient of a universal vector extension),
      so its projection to F ≅ G_a under π⁻¹(B) = H′ × F is trivial, and J ⊂ H′.
    - This contradicts Lie J ∩ Lie F ≠ 0. ***The docstring asserts this step without proof***; the paper's
      parenthetical in Step 3 covers it.
  - (c) By Lemma K (#10), ψ ≠ 0 on S_i or on S_ρ (whichever is nonzero). So Ψ″₁ = θᵀz_i + θᵀz_ρ ≠ 0 on
    T_H = graph over T_B. (By uniqueness of splittings, the second component of T_H is 0.) ✔
* T_H is defined over ℚ̄, hence spanned by `algX` vectors, so one of them has nonzero Ψ″-image: `sub` holds. H = 0
  gives ⊥ ✔. The case analysis also holds for subgroups defined only over ℂ, so it is robust.

This agrees with the paper's Step 3 table (types A–E). The only type with Ψ″(T) = 0 is D with B = 0, i.e. G′ = 0.

**Suggested fix (#9):** add to docstring fact 4 the two clauses "(the G_a-part of a splitting is trivial, as
Hom(B, G_a) = 0)" and "(if φ(m) ≠ 0 the anti-affine image of B^♮ contains the fibre)".

### 10. Lemma K, exact (`lemmaK.py`)

The (ψ, φ) map k⁴ → K × K is written as an 8×8 rational matrix in the θ-basis:
* k = ℚ(i): det = 16;
* k = ℚ(ρ) (ρ̄ = complex conjugate, matching the fibre character): det = 9.

In both cases dim_ℚ ker ψ = dim_ℚ ker φ = 4 (k-dimension 2 = n/2), and dim_ℚ(ker ψ ∩ ker φ) = 0. ✔

### 11. d₀, d₁, d₂: OK [Proved]

* G_ℓ is a quotient of the anti-affine group A^♮ (the push-out map is onto), so Hom(G_ℓ, G_a) = Hom(G_ℓ, G_m) = 0.
* Hence Hom(G″, G_a) ≅ ℚ̄ and Hom(G″, G_m) = 0. The maximal unipotent factor is G_a (d₀ = 1), d₁ = 0, and
  d₂ = 10 − 1 = 9. This is the paper's d₂ = 2n + 1.
* W88 Thm 1.1 (w88-01) allows d₀ > 0, and (1.2)/(5.4) contain only d₁ + 2d₂. Using d₀ = 0, d₂ = 10 would only weaken
  the hypothesis.
* Lemma 5.2's bound rk Ω′ ≤ (d₁ + 2d₂) − (d₁′ + 2d₂′) holds for this G. G_a-parts carry no periods, so the proof's
  "product" phrasing is not needed. Check: for G′ = 0, 16 ≤ 18 ✔; for the type-E line G′ (d₀′ = 1, d₂′ = 0), G″/G′ ≅ G_ℓ
  and 16 ≤ 18 ✔.
* Sanity check of the G_a weight 0 [Proved]: for G = G_a × G_m, (5.4) with m = 2 is exactly Gelfond–Schneider.

### 12. Lemma U range: OK [Proved]

N = 9, d₁ = 0, d₀ = 1, and κ ≤ rk Ker exp_{G″} = 16. So 2N = 18 ≥ 2 + κ for **every** instance of
`HyperplaneKappa gmX`. Equality is possible only if V contains all periods, i.e. V = T(G_ℓ) = {s₁ = 0}, which is
still inside the range. The paper's line "Theorem MX: 4n + 2 ≥ 2n + 2" is the κ = 8 case.

### 13. `main`: V″, W″, Y″ and κ: OK

* V″ = ker(βη_ρ Ψ″₁ − ϖΨ″₂) = Ψ″⁻¹(ℂ(ϖ, βη_ρ)) is a hyperplane (Lean). W″ = span of the eight
  (−θ_j, e_j, 0, 0) / (−θ_j, 0, e_j, 0) = ker Ψ″ is rational, of dimension 8 (Lean). So d − 1 − t = 1.
* `preW1 h` has Ψ″-image θ_h(ϖ, βη_ρ) ∈ V. `preW2 h` has image θ_h(Ω_ρ, β(2/√3)π/ϖ), which lies in V iff
  η_ρΩ_ρ = 2π/√3. That is Legendre for ρ: exact sympy gives 0, and `etaRho_mul` proves it in Lean. Both are
  ℚ-combinations of the period generators, hence in per.
* `dataV h` = θ_h-copy of (X, Y, a, t), which is in Λ(G⁴), so its image is in `lam`.
* κ ≥ 8: the eight lifts are ℚ-independent, since their Ψ″₁-values are θ_hϖ, θ_hΩ_ρ and `hM` holds (Lean). This is
  the paper's Step 1 with L = 0.
* (5.4) reads 12 > (0 + 18 − κ)·1 ≤ 10. As in the earlier models, it fails without κ (12 > 18 is false), so the result
  rests on the κ-term.
* The final step matches the Remark "The count": an algebraic x ∈ S ⊂ V″ with Ψ″x ≠ 0 forces
  ϖ/(βη_ρ) = Ψ″₁x/Ψ″₂x ∈ ℚ̄, i.e. ϖΩ_ρ/π ∈ ℚ̄. This contradicts `hΓ`.
* Consistency check [Proved]: every hyperplane V meets the 2-dim space T(G_a × F) in a line ℓ_V. If ℓ_V is
  ℚ̄-rational, the conclusion of the hypothesis holds trivially (ℓ_V = T of a 1-dim vector subgroup). In `main`,
  ℓ_V = ℂ(ϖ, 0, 0, βη_ρ), which is irrational exactly by `hΓ`. So the hypothesis is used in its non-trivial regime,
  as intended.

### 14. `hΓ`, `hM`: true [Lit] + derivation [Proved modulo Wüstholz]

* **`hΓ`.** Suppose ϖ = cη_ρ with c ∈ ℚ̄. Then the period u = (ϖ; Ω_ρ, η_ρ) of E_i × E_ρ^♮ lies in a proper ℚ̄-rational
  subspace. By Wüstholz's analytic subgroup theorem it then lies in T_H for a proper connected algebraic H.
  - Hom(E_i, E_ρ^♮) = Hom(E_ρ^♮, E_i) = 0, and E_ρ^♮ has only the subgroups 0, F and E_ρ^♮. So H = H₁ × H₂.
  - ϖ ≠ 0 forces H₁ = E_i, and Ω_ρ ≠ 0 forces H₂ = E_ρ^♮. Contradiction.
  - Since ϖ/η_ρ = (√3/2π)ϖΩ_ρ, this gives `hΓ`.
* **`hM`.** The same argument on E_i × E_ρ.
* **Citation.** TRUST.md and the paper attribute `hM` also to "Masser 1975" (LNM 437). I could not confirm that
  LNM 437 contains the two-curve statement; I recall it as a one-curve theory. Wüstholz 1989 suffices, and the
  CM-case route via Bertrand–Masser 1980 is another option. COSMETIC: cite Wüstholz, or check the Masser reference.

### 15. TRUST NOTE: the d₀ = 1 regime

`gmE` and `gmQ` have d₀ = 0. gmX has d₀ = 1, so the hypothesis now relies on the G_a part of W88's proof (Gelfond
directions, the (log S)^{bd₀} parameters). The paper's Appendix A itself says b > 1 is used only in the case δ = τ,
"which requires d₀ ≥ 1 (Theorem MX)".

This is within W88's stated scope: Thm 1.1 is stated for G = G_a^{d₀} × G_m^{d₁} × G₂. It adds no new failure point
to the encoding, but an expert check of W88 §§6–7 should be asked explicitly to cover these together:
* d₀ ≥ 1 with the case δ = τ;
* W ≠ 0;
* κ > 0;
* a non-semiabelian G₂ (G_ℓ, as in REFEREE_HYP_NAT #11).

Suggest adding one line to TRUST.md.

### 16. COSMETIC: how much of Proposition D is formalised

Prop. D says V ∩ Ψ(Λ_K(G)) = Kw₁ + Kw₂, with Λ_K the K-span. `main` assumes v = Ψ(X, Y, a, t) with X, Y single
logarithms, i.e. v ∈ Ψ(Λ(G)) and not its K-span, and concludes only the first coordinate:
z ∈ Kϖ + KΩ_ρ.

The second coordinate follows: v = sw₁ with s = x + x′Ω_ρ/ϖ and w₂ = (Ω_ρ/ϖ)w₁, so v = xw₁ + x′w₂. So for such v the
conclusion is equivalent to v ∈ Kw₁ + Kw₂. It is exactly what Theorem MX needs, and the β ∈ K restriction is
documented. Suggest: "Proposition D for v ∈ Ψ(Λ(G))" in the docstring and TRUST row 54.

### 17. NOTE (positive): robustness and non-vacuity

* Legendre plus unit symmetry give η(ω) = π/ω on ωℤ[i] and η(ω) = 2π/(√3ω) on ωℤ[ρ] for every ω. So `etaI` and `etaR`
  are correct whatever the Γ-formulas are; the Γ-values enter only through the premises g₂, g₃ ∈ ℚ̄, which are true
  (#4). If a premise were false, the hypothesis would be vacuous, never false.
* `main`'s other premises are true (#14), and `LogNat` is satisfiable (X = 0 via m = n = 0, or genuine points). So
  `main` is not vacuous.

## Falsification attempts (none succeeded)

* **Spurious κ.** `per` is exactly ℚ ⊗ Ker exp_{G″} (#7).
* **Missing subgroups / overly narrow `sub`.** Fact 4 is proved for all H, even over ℂ (#8). Rational V
  (ℓ_V rational), V = T(G_ℓ) (κ up to 16) and V ⊃ ker Ψ″ rational (type-E line) all satisfy the conclusion.
* **Wrong η.** Checked to 40 digits via E₂, and against the Lean series directly (#3). A wrong η would have put G1–H2
  outside Λ and outside Ker; it does not happen.
* **Hidden d₀ inflation.** d₀ = 1 is genuinely maximal, and d₂ = 9 is not undercounted (#11).
* **Encoding traps.** The coordinate order (s₁, z_i, z_ρ, s₂) is consistent across `psi1`, `psi2`, `genI/genR/genA`,
  `wI/wR`, `phiX` and `sub`. θ in `psi1` matches `θ`. There is no ℚ/ℤ mismatch and no ℂ/ℚ scalar mixing in `⊓`.
