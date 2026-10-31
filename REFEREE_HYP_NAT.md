# Referee report: is `Thm11KappaNat` (model `gmQ`) a true consequence of W88 §5d?

Referee: adversarial AI reviewer (Claude), 2026-10-30. No project file other than this report was edited, and no git
command was run. Scratch scripts are in
`C:\Users\SHAWNK~1\AppData\Local\Temp\claude\C--Users-Shawn-Krisman-math\9bf70abd-7b4c-4b52-88e0-7fbce744eb82\scratchpad\hypnat\`
(`check.py`: quasi-periods, Legendre, g₂, g₃; `kerphi.py`: exact check of the coordinates on T(Q″)).

Sources read: `CM4E/MainNat.lean` and `CM4E/Waldschmidt.lean` in full, `REFEREE_HYP.md`, the paper's proof of Theorem
MG♮ (`pilot_thmM/paper/paper.tex`, lines 433–473) and Lemma `lem:natural`, and
`schanuel/five_exp/pilot_epi2_mix/REFEREE_MGF_2.md`. I also read the W88 page images
(`schanuel/five_exp/ref/w88_pages/`; they are not under `pilot_thmM/ref/`): w88-01 and w88-02 (Thm 1.1 and its
setting), w88-10 (Lemma 5.2) and w88-11 (§5d, (5.4)).

## Verdict: CORRECT (with cosmetic caveats)

I found no encoding bug that would make `HyperplaneKappa gmQ` stronger than W88 §5d for G″ = G_m⁸ × Q″. Each field
of the model is a sound under- or over-approximation in the right direction:
* `lam` is a subset of Λ(G″);
* `per` equals the ℚ-span of Ker exp_{G″} exactly;
* `sub` contains the Lie algebra of every connected algebraic subgroup;
* d₀ = 0, d₁ = 8 and d₂ = 3 are W88's maximal decomposition.

Given the premise g₂(ϖℤ[i]) ∈ ℚ̄, `Thm11KappaNat` follows from W88 Thm 1.1 with (5.4), *as printed*. As with `gmE`,
the residual risk is the κ-term of W88 Thm 4.1 / Prop. 6.1 (§§6–7) itself, not the encoding.

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `per` | equals ℚ ⊗ Ker exp_{G″}; κ cannot be inflated |
| 2 | OK | `lam` | ⊂ Λ(G″) |
| 3 | OK | `sub` | the list T_L × {0, F, π⁻¹(B′)} is complete; the fibre is `Pi.single 2 1` |
| 4 | OK | d₀, d₁, d₂ | 0, 8, 3, matching W88's "maximal factor" convention |
| 5 | OK | `alg` / `Rational` | the coordinates are ℚ̄-rational, so this matches "defined over ℚ̄" |
| 6 | OK (verified) | quasi-periods | ϖη(ϖ) = π, η(iλ) = −iη(λ), g₂ = 4, g₃ = 0 |
| 7 | COSMETIC | sign in the docstring | in coordinates dual to (dx/y, x dx/y) the periods are (λ, **−**η(λ)) |
| 8 | OK | V, W, Y in `main` | they match Thm 1.1's hypotheses; 12 > 14 − κ with κ ≥ 4 |
| 9 | NOTE (positive) | robustness | soundness needs only g₂ ∈ ℚ̄ (the premise), not the Γ-formula for ϖ |
| 10 | NOTE (positive) | Lemma U range | its condition 2N ≥ d₁ + 2d₀ + κ holds for every instance of the hypothesis |
| 11 | TRUST NOTE | regime | G₂ = Q″ is not semiabelian: this uses W88 beyond the `gmE` regime, though within its stated scope |
| 12 | MINOR DOC | pointers | REFEREE_MGF_2 and the W88 scans live in other folders than the ones cited |

## Details

### 1. `per` ⊂ ℚ ⊗ Ω(G″): OK, in fact equality

* **G_m⁸ part.** The periods are 2πi·e_j. ✔
* **Periods of E^♮.** For ϖℤ[i] they are (λ, η(λ)), with η(λ) = ζ(z+λ) − ζ(z) the full-period quasi-period (sign
  convention: see #7).
  - Legendre, for the basis (ϖ, iϖ): η(ϖ)·iϖ − η(iϖ)·ϖ = 2πi.
  - ζ(iz) = −iζ(z) on a square lattice (substitute ω = iω′ in the Weierstrass series), so η(iϖ) = −iη(ϖ). Hence
    ϖη(ϖ) = π and η((m+ni)ϖ) = (m − ni)π/ϖ. This is `etaL`. ✔
* **Periods of Q″.** U is connected, so π₁((E^♮)⁴) → π₁(Q″) is onto. So the periods of Q″ are exactly the images of
  the periods of (E^♮)⁴. ✔ That is `perImg`, coordinate by coordinate.
* **Clean description.** Put μ_j = m_j + n_j i and x = φ(μ) = Σθ_j μ̄_j ∈ K. Since τ(μ̄_j) = μ_j for τ(i) = −i,
  perImg = (ϖ·τ₁(x), ϖ·τ₂(x), (π/ϖ)·x).
  - So ℚ ⊗ Ω(Q″) = {(ϖτ₁x, ϖτ₂x, πx/ϖ) : x ∈ K}, of ℚ-rank 4 = 2·dim A″, as it must be (the G_a fibre carries no
    periods).
  - The kernel of perImg is ker φ ∩ ℤ[i]⁴, the periods of B^♮_{ker φ}. ✔
* **Conclusion.** `per` is the full ℚ-span of the true periods (dim_ℚ = 12), so κ in the Lean statement is the true κ
  of W88. There is no "periods outside the lattice" bug.

### 2. `lam` ⊂ Λ(G″): OK

`lam` requires e^{y_j} ∈ ℚ̄ (automatically nonzero) and a Q″-component in `perQ` (the lattice, not its ℚ-span). So
exp_{G″}(y) = ((e^{y_j}), 0) ∈ G″(ℚ̄). ✔

Only the generators are constrained. That suffices because G″(ℚ̄) is a group, and the ℚ-span/ℤ-span equivalence of
REFEREE_HYP 1(d) carries over verbatim. The ℚ-span of the periods is used for κ, which is again equivalent
(N·v ∈ Y_ℤ ∩ Ker).

### 3. `sub` contains every connected algebraic subgroup: OK, and the list is complete

* **Products.** No torus is a quotient of a connected subgroup H ⊂ Q″: Hom(H, G_m) kills the vector part and then
  factors through an abelian variety. Also Hom(G_m, Q″) = 0: the image dies in A″, and Hom(G_m, G_a) = 0. By Goursat,
  connected subgroups of G_m⁸ × Q″ are products T_L × H. Lie T_L = L ⊗ ℂ with L ⊂ ℚ⁸, as encoded. ✔
* **Subgroups of Q″.** The fibre F = ker(Q″ → A″) is G_a⁴/{θᵀw = 0} ≅ G_a, which is connected; I checked that
  U ∩ G_a⁴ = {θᵀw = 0}. G_a has no nontrivial finite subgroups in characteristic 0, so for connected H ⊂ Q″ either
  H ∩ F = F or H ∩ F = 0.
  - If F ⊂ H, then H = π⁻¹(π(H)) = π⁻¹(B′), with B′ = 0 allowed (H = F).
  - If H ∩ F = 0 and H ≠ 0, then H is a splitting over B′ = π(H) ≠ 0, so π⁻¹(B′) = H ⊕ F.
    - B′ = B_{S′}/B_{ker φ} for a k-subspace S′ ⊋ ker φ: every abelian subvariety of E⁴ is a B_S, since
      End(E⁴) = M₄(ℤ[i]).
    - J = image of B^♮_{S′} is anti-affine, so its projection to F ≅ G_a is trivial, and J ⊂ H.
    - But T(B^♮_{S′}) ∋ (0, m̄) for m ∈ S′ (functoriality of ♮; [a] acts by diag(a, ā)). Its image in T(Q″) is
      (0, 0, θᵀm̄) = (0, 0, φ(m)), which is nonzero for m ∉ ker φ. So Lie J ∩ Lie F ≠ 0, hence F ⊂ J ⊂ H. This is a
      contradiction.
  - So the list is complete: 0, F, π⁻¹(B′). Every nonzero member contains F. This agrees with REFEREE_MGF_2 #1–2,
    which I reconstructed independently before reading it.
* **The fibre direction.** Lie F is the image of {(0, w)}. In the coordinates (ℓ_{τ₁}(z), ℓ_{τ₂}(z), θᵀw) that image is
  ℂ·(0, 0, 1) = `Pi.single 2 1` (`Fin 3`, index 2 = third coordinate). This is consistent with `perImg` (index 2 =
  θᵀη) and with `phiN` (`v.2 2` = σ). ✔
* **Over-approximation.** `sub` allows any h ∋ e₂, which is a superset. That only weakens the conclusion. ✔

### 4. d₀, d₁, d₂: OK

W88 (p. 375) defines d₀ and d₁ as the dimensions of the maximal unipotent and multiplicative *factors*, i.e. direct
factors. Q″ is a quotient of the anti-affine group (E^♮)⁴, so it is anti-affine, and Hom(Q″, G_a) = Hom(Q″, G_m) = 0.
Hence G″ has no G_a direct factor (d₀ = 0), the torus factor is exactly G_m⁸ (d₁ = 8), and G₂ = Q″ (d₂ = 3, so
d = 11).

The fibre G_a sits inside Q″, not as a factor, so it is correctly counted with weight 2 inside d₂. Treating it as
d₀ = 1 would be wrong, and would make the hypothesis stronger than W88.

Cross-check with Lemma 5.2's bound rk Ω′ ≤ (d₁ + 2d₂) − (d′₁ + 2d′₂) for G′ = F: 12 ≤ 14 − 2. ✔ For G′ = 0: 12 ≤ 14. ✔

### 5. `alg` / `Rational` versus "W defined over ℚ̄": OK

The ℚ̄-structure on T(E^♮) = H¹_dR(E/ℚ̄)^∨ has the coordinates dual to (dx/y, x dx/y) rational. Here
E: y² = 4x³ − g₂x is over ℚ̄ by the premise; g₃ = 0 is proved in Lean.

U is defined over ℚ̄:
* B_{ker φ} comes from CM endomorphisms defined over ℚ(i);
* ♮ is functorial over ℚ̄;
* {θᵀw = 0} has coefficients in K.

So T(Q″) carries the quotient ℚ̄-structure. Its rational dual is spanned by ℚ̄-rational forms on T((E^♮)⁴) that
vanish on T(U).

**Exact check (`kerphi.py`).** T(U) = (ker φ ⊗ ℂ) × {θᵀw = 0}, of dimension 2 + 3 = 5. The conjugate-eigen part of
T(B^♮_{ker φ}) lies inside {θᵀw = 0}. Then:
* dim_ℚ ker φ = 4, it is a ℚ(i)-subspace, and its ℂ-span has rank 2;
* ℓ_{τ₁} and ℓ_{τ₂} vanish on it and have rank 2;
* so (ℓ_{τ₁}, ℓ_{τ₂}, θᵀw) is a ℚ̄-rational basis of T(Q″)*.

Also, x dx/y is the conjugate eigenvector exactly: [i]*(x dx/y) = −i x dx/y, with κ₁ = 0, and E₂(i) = 3/π checked.
`alg` (all 11 coordinates algebraic) is therefore the right ℚ̄-structure. `Rational` = "spanned by algebraic vectors"
is the standard meaning of "defined over ℚ̄". ✔

### 6. Numerical checks (`check.py`): all pass

* ϖ = Γ(1/4)²/(2√(2π)) = 2.6220575542921198…
* E₂(i) − 3/π = 0 (40 digits), so η(ϖ) = (π²/3)E₂(i)/ϖ = π/ϖ (error 2·10⁻⁴¹).
* g₂ = (4π⁴/3)E₄(i)/ϖ⁴ = 4.000… (40 digits), and g₃ ≈ 2·10⁻⁴¹.
* Direct Weierstrass-ζ sums (box |a|, |b| ≤ 400, double precision; truncation error about 10⁻⁶):

| quantity | direct sum | target |
|---|---|---|
| η(ϖ) | 1.198141 | π/ϖ = 1.198140 |
| η(iϖ) | −1.198141i | −iπ/ϖ |
| η((2−3i)ϖ) | 2.39624 + 3.59441i | (2+3i)π/ϖ |
| η₁ω₂ − η₂ω₁ | 6.283190i | 2πi = 6.283185i |

* ℘′² − (4℘³ − 4℘) ≈ 10⁻⁵ (finite differences), so ϖℤ[i] uniformises y² = 4x³ − 4x.

### 7. COSMETIC: sign convention in the docstring

The `MainNat` docstring says the coordinates are "(z, w) dual to (dx/y, x dx/y)" with periods "(λ, η(λ))". But
∫_γ x dx/y = ∫℘(u)du = −η(λ), checked numerically: ∫ over one period gives −1.198141 = −η(ϖ). So in coordinates dual to
(dx/y, x dx/y) the periods are (λ, −η(λ)), and the model's w is dual to −x dx/y.

This is harmless. w ↦ −w is a ℚ̄-rational automorphism preserving the conjugate eigenline, U, F and every field of the
model. Suggested fix: write "dual to (dx/y, −x dx/y)", or note the sign.

### 8. V, W, Y in `main`: OK

* V = ker `phiN (t⁻¹)` = Ψ″⁻¹(ℂ(1, s)), with Ψ″ = (θᵀt₁, θᵀt₂ + σ), as in the paper. It is a hyperplane
  (`finrank_ker_phiN`).
* W = span `wN` = ker Ψ″: nine ℚ̄-rational vectors in V, so t = 9 and d − 1 − t = 1.
* **Generators.**
  - `perV h` = (2πiD e_h, image of the E^♮-period λ₀e_h). This is a genuine period of G″ (`perImg_single`), and it
    lies in V because η(λ₀) = 2πi(p + qi)/ϖ = s·2πiD.
  - `dataV` has Q″-component 0 and G_m-entries t·a and a, with e^{ta}, e^a ∈ ℚ̄.
* (5.4) becomes 12 > (8 + 6 − κ)·1 with κ ≥ 4 proved, i.e. 12 > 10. That is margin 2 = n − 2, as in the paper.
* As in REFEREE_HYP, the inequality fails without κ (12 > 14 is false). So the result rests entirely on the κ-term.

### 9. NOTE (positive): robustness of the model

Soundness does not depend on the Γ-value formula for ϖ, nor on g₂ = 4 specifically. Legendre and ζ(iz) = −iζ(z) hold
for *every* square lattice ωℤ[i], so ωη(ω) = π regardless of ω. The ℚ̄-rationality needs only that E(ωℤ[i]) is
defined over ℚ̄, which is exactly the premise `IsAlgebraic ℚ lemniscatic.g₂`; g₃ = 0 is proved.

`lemniscatic` is (varpi, i·varpi), the same `varpi` as in `perImg`/`etaL`. So the premise and the model refer to the
same lattice. If the premise failed, the hypothesis would be vacuous, never false.

### 10. NOTE (positive): Lemma U's range covers the whole hypothesis

The paper's Appendix Lemma U (its write-up of W88's multiplicity step) needs 2N ≥ d₁ + 2d₀ + κ. For any hyperplane in
T(G″): N = 10, d₁ = 8, d₀ = 0 and κ ≤ dim_ℚ per = 12, so 20 ≥ 8 + κ always holds. `HyperplaneKappa gmQ`, quantified
over all V, W, Y, therefore never leaves the range in which the project's own account of the κ-step applies.

### 11. TRUST NOTE: a different regime from `gmE`

In `gmE`, G₂ = E is semiabelian. Here G₂ = Q″ is a non-split extension of an abelian surface by G_a, with the vector
part counted at weight 2.

W88 Thm 1.1 is stated for an arbitrary commutative algebraic group over ℚ̄ (p. 375). Its proof (§6) embeds G₂ in P_N
and uses Philippon's zero estimate, which is general. So this is within W88's stated scope.

It is, however, a regime that `REFEREE_HYP` did not exercise. Any expert check of W88 §§6–7 should be asked
explicitly to cover groups with a non-split vector part, such as E^♮ and its quotients. This adds no new failure point
beyond the κ-term already flagged, but it should be stated in TRUST.md.

### 12. MINOR DOC: pointers

* TRUST.md and the `MainNat` docstring cite "REFEREE_MGF_2 #1–2" without a path. The file is
  `schanuel/five_exp/pilot_epi2_mix/REFEREE_MGF_2.md`, not `pilot_thmM/`.
* The W88 scans are in `schanuel/five_exp/ref/w88_pages/`, not `pilot_thmM/ref/`.
* The docstring's soundness item 3 could add the one-line no-splitting argument (anti-affine image of B^♮_{S′}
  contains F) from #3 above, so that the model's justification is self-contained.

## Falsification attempts (none succeeded)

* **Periods.** `per` is exactly ℚ ⊗ Ω(G″) (#1), so no V can gain spurious κ.
* **Missing subgroups.** The subgroup list is provably complete (#3). Every degenerate V tried satisfies the
  conclusion. Example: V = {q₂ = t₀/(2iϖ)} contains a period and unboundedly many G_m-logarithms with t₀ = 0, but it
  also contains the rational torus direction e₁, so the conclusion holds.
* **d₂ too small.** Ruled out (#4). The weight-2 count for the fibre is W88's.
* **Encoding traps.** No ℚ/ℤ mismatch, no ℂ/ℚ scalar mixing in `⊓`, and the index 2 is consistent across `perImg`,
  `phiN` and `sub`.
