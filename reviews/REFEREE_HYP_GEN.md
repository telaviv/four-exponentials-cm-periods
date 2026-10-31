# Referee report: the general hypothesis models `gmF`, `gmMGn`, `gmMG` (`CM4E/Gen/`) and the new `Final` theorems

Referee: adversarial AI reviewer (Claude), 2026-10-30. This report is the only project file I edited. I ran no git
command. My check script and its output are in `checks/hypgen/` (`check.py`, `check.out`).

Files reviewed:
* In full: `CM4E/Gen/Basis.lean`, `Frame.lean`, `CMLattice.lean`, `MGn.lean`, `MG.lean`, `Instances.lean`, and
  `CM4E/Final.lean` (the new section).
* For context: `CM4E/Waldschmidt.lean`, `MainNat.gmQ`, the statement of `Gen.exists_adapted_basis`, TRUST.md, and
  REFEREE_HYP_NAT / REFEREE_HYP_MX.
* From the paper: Thm 1 (thm:A), Lemma K, Lemma natural, Thms MG and MG♮, Remarks 15 and 20 (rem:MG5d, rem:MGn5d),
  Cor. MG2 and MG♮2, and Appendix A (Lemma U).

`CM4E/Gen/MXGen.lean` was created after the build and is not imported by `CM4E.lean`. It is outside this review.

Build check: `lake env lean Axioms.lean` passes [Proved by Lean]. The oleans are newer than the sources. Every new
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`:
* `Gen.frame_false`, `Gen.exists_adapted_basis`, `Gen.fourExpAt_MGn`, `Gen.fourExpAt_MG`;
* `Final.fourExpAt_varpi_all`, `fourExpAt_varpi_div_pi_all`, `fourExpAt_omegaRho_all`, `fourExpAt_omegaRho_div_pi_all`,
  `two_three_omegaRho`.

## Verdict: CORRECT (cosmetic and latent caveats only)

For every adapted basis θ:
* `gmMGn L b` is a sound model of G″ = G_m^{2n} × Q″.
* `gmMG L b` is a sound model of G″ = G_m^{2n} × A″.

Here "sound" means four things:
* `lam` ⊂ Λ(G″);
* `per` ⊂ ℚ ⊗ Ker exp (in fact equality);
* every connected algebraic subgroup satisfies `sub`;
* (d₀, d₁, d₂) is W88's maximal decomposition, and d₂ is not undercounted.

`frame_false` implements the §5d count of Remarks 15/20 faithfully. The five `Final` theorems state Theorem 1(a)/(b)
for Ω ∈ ℚ̄^×ϖ and Ω ∈ ℚ̄^×Ω_ρ, for every choice of logarithms.

One latent defect (#10) is not reached by any final theorem. `CMLattice` allows Im α < 0, and then its Legendre field
forces η₀ = −η*(ω). That makes `gmMGn L` unsound for such an `L`. Fix: require `0 < α.im`.

The residual risk is unchanged: W88 §5d itself (#16).

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `IsAdaptedFieldBasis` | encodes "θ = (b_j, αb_j) is a ℚ-basis of a number field K ⊂ ℂ". K ⊇ k = ℚ(α) is automatic, since α ∈ K (`α_mem`) |
| 2 | OK | `gmF`: lam, per, alg, d₁, d₂ | sound for any (Q, λ) satisfying the docstring conditions; the ℚ-span `lam` is fine because Λ(G) is a ℚ-space |
| 3 | COSMETIC | `gmF` docstring, "products" | Goursat needs no nonzero homomorphisms between subquotients of a torus and of G₂, not just between the torus and G₂. True for Q″ and A″ |
| 4 | OK | `gmMGn`: tangent space, `Wphi`, d₂ | T(Q″) = ℂⁿ/ℂ·ker φ × ℂ with coordinates ([z], θᵀw) exactly. `Wphi` = ℂ·ker φ exactly. d₂ = n/2 + 1 (exact checks for n = 4, 6, 8) |
| 5 | OK | `perQn`, `lam` | the generators are the images of (ωe_j, η*(ω)e_j) and (αωe_j, η*(αω)e_j). They generate Ker exp_{Q″}, of rank n. per = ℚ ⊗ Ker exp_{G″} |
| 6 | OK / COSMETIC | `sub` for Q″ | every nonzero connected H ⊂ Q″ has λ = θᵀw ≠ 0 on T_H (canonical-lift argument below). The docstring cites the paper without the one-line reason |
| 7 | OK | `gmMG` | T(A″) = ℂⁿ/ℂ·ker ψ; λ([z]) = θᵀz; periods [mω]; every nonzero abelian subvariety has θᵀ ≠ 0 on its tangent space; d₂ = n/2 |
| 8 | OK | `algQn`, `algQm` | exactly the image of the ℚ̄-structure under the ℚ̄-rational quotient map |
| 9 | OK (verified) | `latI`, `latRho` | Legendre ωη₀(α − ᾱ) = 2πi is right. η₀ = η(ω) and η(αω) = ᾱη(ω) hold to 40 digits via E₂. g₂, g₃ = (4, 0) and (0, 4) |
| 10 | COSMETIC (latent) | `CMLattice.him : α.im ≠ 0` | for Im α < 0 the field `legendre` forces η₀ = −η*(ω), so `perQn` contains non-periods and `Thm11KappaMGn L` is not a W88 instance. Not reached (both instances have Im α > 0). Fix: `0 < α.im` |
| 11 | OK | Lemma U range | gmMGn: 2N ≥ d₁ + κ in every instance. gmMG: fails only when κ = 3n − 1, and every such instance has a conclusion that holds outright. All non-trivial instances have κ ≤ n |
| 12 | OK | `frame_false` vs §5d | m = 3n, κ ≥ n, d₁ = 2n, d₂ = dim Q, d − 1 − t ∈ {0, 1}, (5.4) ⟸ dim Q < n; subgroup exclusion as in the Remarks |
| 13 | OK | non-vacuity | the hypotheses are sound W88 instances, so they are not false (modulo W88). The other premises (Schneider, `hg₂'`, `hg₃'`) are true |
| 14 | OK | `Final` statements | exactly Theorem 1(a)/(b) at t = cϖ, cϖ/π, cΩ_ρ, cΩ_ρ/π (all c ∈ ℚ̄^×), with any fixed logarithms. `two_three_omegaRho` uses the real logarithms |
| 15 | COSMETIC | TRUST.md / README | not updated: no rows for the five new theorems or for `Gen.Thm11KappaMGn` / `Gen.Thm11KappaMG`. The status table still says "Missing: general c, Ω_ρ" |
| 16 | TRUST NOTE | residual | as before: W88 §5d with W ≠ 0, κ > 0 and a non-semiabelian G₂ (Q″), now for every even n ≥ 4. The second application inside §5d (the subgroup from Lemma 5.1) is not covered by Lemma U |

## Details

### 1. `IsAdaptedFieldBasis`: OK [Proved]

The structure encodes the following:
* θ is ℚ-independent;
* K = span_ℚ θ contains 1 and is closed under products and inverses, so K is a field with [K : ℚ] = 2r;
* the b_j are algebraic, so θ is algebraic.

`CMLattice.α_mul_mem` shows αK ⊂ K, using α² = p + qα, so α ∈ K and k ⊂ K. Lemma K needs only k ⊂ K and
[K : ℚ] < ∞. In particular it does not need K to be stable under complex conjugation.

Soundness of the models (#4–#8) does not even need Lemma K. It holds for any algebraic θ. Lemma K enters only
through d₂ = n/2 (+1), which the proofs use as an upper bound (`finrank_W*_ge`). There it can only make d₂ smaller,
which would be unsafe, but #4 shows it is exact.

### 2–3. The generic model `gmF`: OK [Proved]

* **`lam`.** This is span_ℚ of three kinds of vector:
  - toric single-slot logarithms (tor1/tor2 j x with e^x ∈ ℚ̄);
  - `qv` of period generators of G₂.
  
  All of these lie in Λ(G″). Λ(G″) is a ℚ-vector space: [N] is an isogeny on the abelian part and an isomorphism on
  the vector part, so N-division points of ℚ̄-points are ℚ̄-points. Hence span_ℚ ⊂ Λ(G″).
* **`per`.** The generators are 2πi in a toric slot and `qv` of periods of G₂. All are periods.
* **ℚ-span versus ℤ-span.** This is the same reduction as in REFEREE_HYP §1(d). Also, `Module ℚ` on an additive group
  is unique, so the ℚ-structure on the quotient types cannot be exotic.
* **`alg`.** The toric coordinates t (with exp = e^t) are ℚ̄-rational, and `algQ` is the ℚ̄-structure of Q (#8).
* **`sub`.** The family is: T_L × h with h = ⊥ or λ ≠ 0 somewhere on h. It contains every T_L × T_H with T_H = 0 or
  λ ≢ 0 on T_H. A larger family only weakens the conclusion. It is a superset of the old `gmQ` condition (fibre vector
  in h), and that is fine.
* **d₁ = 2n, d₂ = finrank Q.** These are correct when G₂ has no G_a or G_m quotient, which holds for both Q″ and A″
  (#4, #7). Then Hom(G″, G_a) = 0 and Hom(G″, G_m) = ℤ^{2n}, so d₀ = 0 and d₁ = 2n are maximal.
* **#3 (cosmetic).** The docstring justifies "connected subgroups are products" by "no nonzero homomorphisms between a
  torus and G₂". Goursat's lemma actually needs this for subquotients: the quotient H₂/K₂ of a connected subgroup of G₂
  is never a nonzero torus.
  - True for G₂ = Q″: every subquotient is an extension of an abelian variety by a vector group.
  - True for G₂ = A″.
  
  Suggest rewording to "no subquotient of G₂ is a nonzero torus, and Hom(G_m, G₂) = 0".

### 4. `gmMGn`: tangent space, `Wphi`, d₂: OK [Proved] + exact checks

Coordinates on (E^♮)ⁿ are (z, w): z is the base coordinate, and w is the conjugate-eigen fibre coordinate, where [a]
acts by diag(a, ā) (REFEREE_HYP_MX #2). The periods are (mω, m̄η₀) for m ∈ ℤ[α]ⁿ. That needs η*(mω) = m̄η₀ on ℤ[α],
which follows by ℤ-linearity from η*(αω) = ᾱη₀ (#9, #10).

* **The canonical lift.** For a k-subspace S ⊂ kⁿ, B_S has tangent space ℂS. Its canonical lift B_S^♮ has tangent
  space ℂS × ℂS̄: this is the ℂ-span of its periods (m, m̄), and (α − ᾱ)(m, 0) = (αm, ᾱm̄) − ᾱ(m, m̄).
* **T(U).** For m ∈ ker φ we have θᵀm̄ = φ(m) = 0, so ℂ·conj(ker φ) ⊂ {θᵀw = 0}. Hence
  T(U) = ℂ ker φ × {θᵀw = 0}, a product.
* **The quotient.** T(Q″) = ℂⁿ/ℂ ker φ × ℂⁿ/{θᵀw = 0} ≅ ℂⁿ/ℂ ker φ × ℂ, via (z, w) ↦ ([z], θᵀw). That is `Qn`.
* **Why ker φ.** U is the largest connected subgroup on which θᵀw vanishes. If H lies over B_S, then H ⊇ B_S^♮
  (#6), so θᵀw|_{T_H} = 0 forces φ(S) = 0. So ker φ, and not ker ψ, is the right subspace in the base. This matches
  the paper.
* **`Wphi`.** It is span_ℂ{v ∈ kⁿ : Σθ_j v̄_j = 0}, with `kSet α` = {u + vα} = k. This is ℂ·ker φ exactly. φ is
  k-semilinear, so ker φ is a k-subspace.
* **Dimension.** k-independent vectors of kⁿ stay ℂ-independent, so dim_ℂ `Wphi` = dim_k ker φ = n/2 (Lemma K). So
  d₂ = finrank `Qn` = n/2 + 1, exactly the paper's value, and not undercounted.
* **Exact checks** (`check.out`, Part A). For θ = (b_j, αb_j), I computed dim_ℚ ker ψ, dim_ℚ ker φ, and the ℂ-ranks
  of their spans:

  | K | n | det(ψ, φ) | dim_ℚ ker ψ, ker φ | ℂ-rank of spans |
  |---|---|---|---|---|
  | ℚ(i, 2^{1/3}) | 6 | 64 | 6, 6 | 3, 3 |
  | ℚ(ρ, 2^{1/3}) | 6 | 27 | 6, 6 | 3, 3 |
  | ℚ(i, √2, √3) | 8 | 256 | 8, 8 | 4, 4 |
  | ℚ(√−2, √3) | 4 | 64 | 4, 4 | 2, 2 |

  In every case (ψ, φ) is a bijection, and the ℂ-rank of each span is n/2.
* **d₀ and d₁.** (E^♮)ⁿ is anti-affine, and so is its quotient Q″. So Hom(Q″, G_a) = Hom(Q″, G_m) = 0, which makes
  d₀ = 0 and d₁ = 2n maximal.
* **U is over ℚ̄.** θ is algebraic and the coordinates (z, w) are ℚ̄-rational. For a general CM curve,
  w* = w − κ₁z with κ₁ ∈ ℚ̄; for E_i and E_ρ, κ₁ = 0.

### 5. `perQn` and `lam`: OK, with per = ℚ ⊗ Ker exp [Proved]

* **Generators.** The image of (mω, m̄η₀) is ([mω], θᵀm̄ η₀). For m = e_j this is ([ωe_j], θ_jη₀), and for m = αe_j
  it is ([αωe_j], θ_jᾱη₀). These are exactly the two families in `perQn`.
* **Ker exp_{Q″} is the image of the lattice.** U is connected, so exp⁻¹(U) = T(U) + Ker.
* **Rank n.** The kernel of ℤ[α]ⁿ → T(Q″) is {m : m ∈ ℂ ker φ, φ(m) = 0} = ker φ ∩ ℤ[α]ⁿ, of rank n. So
  Ker exp_{Q″} has rank 2n − n = n, which is rk H₁(A″). The fibre G_a carries no periods.
* **Conclusion.** per = ℚ ⊗ Ker exp_{G″}, of dimension 3n, so κ cannot be inflated. `lam` ⊂ Λ(G″) by #2.
* **The period lifts are genuine.** In `fourExpAt_MGn`, qh(h) = Σ m_{hj}([ωe_j], θ_jη₀) ∈ span_ℚ `perQn`, and
  λ(qh h) = η₀(α − ᾱ)θ_h/c = s·2πiθ_h with s = 1/(cω), by Legendre.
* **Lean versus paper.** Lean only needs c ∈ K and (α − ᾱ) ∈ K, not i ∈ K. This is a harmless simplification of the
  paper's normalisation K ⊇ k(i, c).

### 6. `sub` for Q″: OK [Proved]; COSMETIC docstring

Let H ⊂ Q″ be connected and nonzero, with image B′ in A″ = Eⁿ/B_{ker φ}.

* **Case B′ = 0.** Then H lies in the fibre F ≅ G_a, so H = F. On F, λ is the coordinate, so λ ≢ 0 on T_H.
* **Case B′ ≠ 0.**
  - Let H̃ be the preimage of H in (E^♮)ⁿ; it is connected, since U is connected. H̃ maps onto B_{S′} with S′ ⊋ ker φ.
  - Let P be the preimage of B_{S′}. Then P/H̃ is a quotient of the vector group, and Hom(B^♮_{S′}, G_a) = 0. So
    B^♮_{S′} ⊂ H̃, and T_H̃ ⊇ 0 × ℂS̄′.
  - For s ∈ S′ ∖ ker φ, the vector (0, s̄) has θᵀs̄ = φ(s) ≠ 0. So λ ≢ 0 on T_H.

The argument holds for subgroups over ℂ, and Goursat (#3) gives the product form in G″.

Suggestion: add "(H contains the canonical lift B^♮_{S′}, as Hom(B^♮, G_a) = 0, and θᵀw = φ ≠ 0 on its fibre directions)"
to the `gmMGn` docstring. This is the same kind of omission as REFEREE_HYP_MX #9.

### 7. `gmMG`: OK [Proved]

* **Tangent space.** T(A″) = ℂⁿ/ℂ ker ψ. `Wpsi` = ℂ·ker ψ exactly, and ψ is k-linear. So dim = n/2 (#4 table).
* **λ.** `lamM` = θᵀz descends to the quotient (`Wpsi_le_ker`).
* **Periods.** The periods are [mω] for m ∈ ℤ[α]ⁿ, generated by [ωe_j] and [αωe_j], i.e. `perQm`. They do not depend
  on η₀.
* **`sub`.** A nonzero abelian subvariety B′ ⊂ A″ comes from a connected B_{S′} ⊃ B_{ker ψ} with S′ ⊋ ker ψ. Its tangent
  space contains [s] with s ∈ S′ ∖ ker ψ, and λ([s]) = ψ(s) ≠ 0.
* **d-values.** A″ is an abelian variety, so d₀ = 0, d₁ = 2n and d₂ = n/2.
* **Period lift.** λ(qh h) = Σ m_{hj}θ_jω = 2icωθ_h = s·2πiθ_h with s = cω/π. This needs i, c ∈ K, and Lean puts both
  into K.

### 8. `algQn`, `algQm`: OK [Proved]

The ℚ̄-structure of a quotient by a ℚ̄-subgroup is the image of the ℚ̄-structure.
* `algQm` is literally that image.
* For `algQn`: the image of an algebraic (v, w) is ([v], θᵀw) with θᵀw ∈ ℚ̄. Conversely, a ∈ ℚ̄ equals θᵀ(a/θ_{i0} e_{i0}).
  So `algQn` = {([v], a) : v ∈ ℚ̄ⁿ, a ∈ ℚ̄} is exactly the image.
* So `Rational W` really means "defined over ℚ̄". The W″ generators used in `frame_false` (`wGen`) are algebraic for
  this reason.

### 9–10. `CMLattice`, `latI`, `latRho` [Numerical] + [Proved]

* **Legendre.** With Im(ω₂/ω₁) > 0, Legendre reads η(ω₁)ω₂ − η(ω₂)ω₁ = 2πi. This also holds for η* = η − κ₁·id, since
  the κ₁ terms cancel. With ω₂ = αω and η*(αω) = ᾱη*(ω), it becomes ωη*(ω)(α − ᾱ) = 2πi, which is the field
  `legendre`.
  - latI: ϖ·(π/ϖ)·2i = 2πi.
  - latRho: Ω_ρ·(2π/(√3Ω_ρ))·i√3 = 2πi.
* **40-digit checks** (`check.out` Part B). Here η is computed from E₂, independently of the Lean ζ series; the series
  itself was checked in REFEREE_HYP_MX #3.
  - |η(ω) − η₀| ≤ 2.3·10⁻⁴¹ and |η(αω) − ᾱη₀| ≤ 2.3·10⁻⁴¹, for both lattices.
  - The generic Legendre residual is ≤ 10⁻⁴⁰.
  - ϖ = 2.62205755429211981…, Ω_ρ = 2.42865064788758161…
  - g₂, g₃ = (4, 0) for ϖℤ[i] and (0, 4) for Ω_ρℤ[ρ], up to 10⁻⁴⁰.
* **Positive observation [Proved].** If Im α > 0, the field `legendre` determines η₀ = 2πi/(ω(α − ᾱ)), and this equals
  η*(ω) for every CM lattice. So the soundness fact in `Instances.lean` ("η₀ is the quasi-period") is a consequence of
  the structure plus the existence of the conjugate-eigen η* (κ₁ ∈ ℚ̄). It is not an independent assumption.
  - This also holds when p, q ∉ ℤ. Take N with Nα integral; then η*(Nαω) = Nᾱη₀ and ℤ-linearity give η*(αω) = ᾱη₀.
* **#10 (latent).** `him : α.im ≠ 0` allows Im α < 0. Take α′ = ᾱ, which gives the same lattice ℤ[ᾱ] = ℤ[α]. Then
  `legendre` forces η₀′ = 2πi/(ω(α′ − ᾱ′)) = −η*(ω). Numerically: −1.19814… against η(ϖ) = +1.19814…, and
  −1.49367… against +1.49367….
  - The `perQn` "generators" are then not periods.
  - Their exponentials are fibre points with transcendental coordinate, so they are not in Λ either.
  - So `Thm11KappaMGn L` is not a W88 instance for such an `L`.
  - The proved implication `fourExpAt_MGn` is still true, and the final theorems use only `latI` and `latRho`
    (Im α = 1 and √3/2), so nothing is wrong today.
  - `gmMG` does not use η₀ and is unaffected.
  - **Fix:** `him : 0 < α.im`. Both instances discharge it trivially, and then `CMLattice` carries no hidden soundness
    condition at all.

### 11. Lemma U range (2N ≥ d₁ + 2d₀ + κ, N = d − 1): [Proved]

For a hyperplane V, κ ≤ dim_ℚ(V ∩ Ω_ℚ) ≤ 3n − 1. The ℂ-span of Ω_ℚ is all of T(G″), because the toric periods span
ℂ^{2n}, the periods of A″ span T(A″) over ℝ, and those of Q″ span T(Q″) by Legendre.

* **gmMGn.** 2N = 5n and d₁ + κ ≤ 2n + 3n − 1. The condition **holds in every instance**.
* **gmMG.** 2N = 5n − 2, so the condition is κ ≤ 3n − 2.
  - **It fails exactly when κ = 3n − 1.** This happens, for example, for V = {first toric coordinate = 0} with Y made of
    the 2n − 1 toric periods in V and the n periods of A″.
  - In every such instance V ∩ Ω_ℚ has dimension 3n − 1 inside the 3n-dimensional Ω_ℚ. So it meets the 2n-dimensional
    toric part 2πiℚ^{2n} in dimension ≥ 2n − 1 ≥ 1.
  - Hence V contains the Lie algebra of a 1-dimensional subtorus, and the conclusion of `HyperplaneKappa` holds outright,
    without W88. So these instances need no Lemma U.
* **Both models.** If V contains no subtorus Lie algebra, then V ∩ 2πiℚ^{2n} = 0. So V ∩ Ω_ℚ injects into the period
  space of G₂, which has dimension n, and κ ≤ n. Then 2N ≥ 2n + n holds (5n ≥ 3n, and 5n − 2 ≥ 3n for n ≥ 1).
* **The applications.** κ = n exactly. κ ≥ n is proved in Lean. For κ ≤ n: a ℚ-combination of the data lifts that is
  a period would need b_hY₁ + c_hY₂ = s(b_hX₁ + c_hX₂), with both sides in 2πiℚ. Since s ∉ ℚ, both sides vanish, and
  then b_h = c_h = 0. This matches the paper's "5n ≥ 3n" and "5n − 2 ≥ 3n".
* **Caveat (paper's own).** Lemma U covers only the first application of Cor. 5.3 inside §5d. The second application
  (the auxiliary G′ from W88 Lemma 5.1) is not checked (#16).

### 12–13. `frame_false` and vacuity: OK [Proved by Lean, reading checked]

* **The count.** `frame_false` checks each piece of the §5d count:
  - m = 3n (`hfin`, via `genF_linearIndependent` on the second-block coordinates);
  - κ ≥ n (`hk`: the n period lifts lie in `per`);
  - d₁ = 2n and d₂ = finrank Q;
  - d − 1 − t ∈ {0, 1}, from ker Ψ″ ⊂ W ⊂ V″ (`hWlo`, `hWhi`).
  
  With these, (5.4) reads 3n > (2n + 2 dim Q − κ)·(0 or 1), and it follows from dim Q < n. This is the paper's
  3n > 2n + 2 (MG♮, n ≥ 4) and 3n > 2n (MG).
* **Where the bounds come from.**
  - `finrank_Qn_lt` needs r ≥ 2, and `exists_adapted_basis` always returns r ≥ 2: it adjoins √2, so n ≥ 4.
  - `finrank_Qm_lt` needs r ≥ 1.
* **V″, W″ and the data lifts.**
  - V″ = ker(θᵀy + λ(q) − sθᵀx) = Ψ″⁻¹(ℂ(1, s)), as in the paper. W″ is ker Ψ″ (rational).
  - The data lifts are toric: MG♮ uses (cωx_k, x_k) with s = 1/(cω), and MG uses (x_k, sx_k) with s = cω/π. This matches
    Remarks 15 and 20.
* **Subgroup exclusion.** This is the paper's two-line argument:
  - h = ⊥: a rational l ∈ L gives s = B/A ∈ ℚ̄, against Schneider.
  - h ≠ ⊥: (0, 0, x) ∈ V″ forces λ(x) = 0.
* **Not vacuous or false.** The models are sound (#2–#8). So `Thm11KappaMGn latI`, `Thm11KappaMGn latRho`,
  `Thm11KappaMG latI` and `Thm11KappaMG latRho` all follow from W88 §5d. They are not contradictory unless W88 is false.
  - In MG♮ the hypothesis is used in its non-trivial regime: V″ contains no rational toric line, because s is
    transcendental.
  - The other premises are true:
    - transcendence of ϖ, ϖ/π, Ω_ρ, Ω_ρ/π (Schneider, proved in `Ext`);
    - `hg₂'`, `hg₃'` for Ω_ρℤ[ρ]. These are assumed, not proved in Lean, as already for `mx`, and are numerically 0
      and 4.
    
    So the final theorems are not vacuous.
* **Quantifier scope.** The hypotheses quantify over all adapted b. Soundness holds for every algebraic θ (#1), so this
  does not make them stronger than W88.

### 14. `Final` statements: OK [Proved]

* **`FourExpAt t`.** It says: for all a, b ∈ logAlg that are ℚ-independent, e^{ta} and e^{tb} are not both algebraic.
  Every a ∈ logAlg is a logarithm of e^a ∈ ℚ̄^×, and every determination of log α is in logAlg. So `FourExpAt (cΩ)` is
  exactly Theorem 1(a) for that Ω, c, and every choice of log α, log β. The same holds for (b) at cΩ/π.
* **The four theorems.**
  - `fourExpAt_varpi_all` / `_div_pi_all` give t = cϖ and t = cϖ/π, for all algebraic c ≠ 0.
  - `fourExpAt_omegaRho_all` / `_div_pi_all` give t = cΩ_ρ and t = cΩ_ρ/π.
* **`two_three_omegaRho`.** This is c = 1, a = Complex.log 2, b = Complex.log 3, the real logarithms. It matches the
  paper's example "2^{Ω_ρ} and 3^{Ω_ρ}".
* **Scope.** "All c" covers every nonzero period of every curve over ℚ̄ with j = 1728 or j = 0. For y² = 4x³ − g₂x the
  lattice is (4/g₂)^{1/4}ϖℤ[i], and similarly for j = 0, so all periods lie in ℚ̄^×ϖ or ℚ̄^×Ω_ρ. Theorem 1 for CM
  curves with other j is not formalised. The machinery (`CMLattice`) is general, but there are only two instances.
  The docstrings say "for Ω = ϖ" / "Ω = Ω_ρ", which is accurate.

### 15. COSMETIC: TRUST.md not updated

TRUST.md lists none of the following:
* the five new `Final` theorems;
* the hypotheses `Gen.Thm11KappaMGn` and `Gen.Thm11KappaMG`, with their models `gmMGn` and `gmMG` and the soundness
  facts in their docstrings;
* the instance facts for `latI` and `latRho`.

Rows 83 and 85 of the status table still say "Missing: general c, Ω_ρ". README has no entry for `CM4E/Gen/`.
`Axioms.lean` already lists everything.

Suggest a TRUST row per hypothesis, naming this report and REFEREE_HYP_NAT (the n = 4 special case `gmQ`). Also add
the note that `hg₂'` and `hg₃'` for Ω_ρℤ[ρ] remain premises.

### 16. TRUST NOTE

The models add no new failure point, but the hypotheses now invoke W88 §5d for G_m^{2n} × Q″ with every even n ≥ 4.
That is still the same regime: d₀ = 0, W ≠ 0, κ > 0, and a non-semiabelian G₂ (REFEREE_HYP_NAT #11). An expert check of
W88 §§5d–7 should cover this regime, together with the unchecked second application inside §5d.

## Falsification attempts (none succeeded)

* **ker ψ in place of ker φ in Q″'s base, or vice versa.** I checked against the canonical-lift tangent space
  ℂS × ℂS̄. `Wphi` (MG♮) and `Wpsi` (MG) are each the right one.
* **Undercounted d₂.** `Wphi` and `Wpsi` are exactly ℂ·ker, of dimension n/2 (proved via Lemma K, and exact for
  n = 4, 6, 8). A larger W would have lowered d₂; that does not happen.
* **Spurious κ.** per = ℚ ⊗ Ker exp, of dimension 3n. The fibre G_a has no periods, and T(U) ∩ lattice = ker φ is
  accounted for.
* **Wrong fibre values.** θ_jη₀ and θ_jᾱη₀ were checked against η(ω) and η(αω) to 40 digits. The only way to break
  them is Im α < 0 (#10), which neither instance has.
* **Missing subgroups.** Every connected H ⊂ Q″ or H ⊂ A″, even over ℂ, satisfies `sub` (#6, #7). Rational
  hyperplanes containing subtorus Lie algebras satisfy the conclusion trivially.
* **Lemma U.** The only out-of-range instances (gmMG, κ = 3n − 1) are trivial ones (#11).
* **Encoding traps.**
  - The coordinate order ((t₁, t₂), q) is consistent across `phiF`, `PsiF`, `wGen`, `genF` and `sub`.
  - `snd` is the fibre coordinate in `Qn`.
  - `Fin r × Fin 2` indexes θ(j, 0) = b_j and θ(j, 1) = αb_j consistently in `theta`, `Wphi`, `perQn` and `exists_coords`.
  - ℚ-module structures are unique, so the `⊓` and `span ℚ` computations are not affected by instance choice.
