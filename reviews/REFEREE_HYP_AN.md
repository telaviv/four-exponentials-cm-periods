# Referee report: `CM4E/AbVar/ThmAn.lean` (Theorem MG♮-A, the model `gmAn`, the instance `y⁵ = x(1 − x)`)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope (commit c364a07).**
* Read in full: `CM4E/AbVar/ThmAn.lean`, `CM4E/AbVar/ThmA.lean`, `CM4E/Gen/Frame.lean`; the relevant parts of
  `CM4E/AbVar/Basis.lean` (`thetaD`, `KspanD`, `IsAdaptedBasisD`, `coordsD`), `CM4E/Defs.lean` (`logAlg`, `FourExpAt`) and
  `CM4E/Waldschmidt.lean` (`GroupModel`, `Rational`, `HyperplaneKappa`).
* Paper [II] (`schanuel/five_exp/paper2/paper2.tex`): Theorem A and its examples (l. 84–102); §2 with Lemma K′, (S1),
  (P), (Ch), (W), (F1)–(F4) and the Beta dictionary (l. 261–420); Theorem MG-A, MG♮-A and the proof of Theorem A
  (l. 423–538).
* Baseline: `REFEREE_HYP_GEN.md` (the frame `gmF`, `frame_false`, the elliptic `gmMGn`) and `REFEREE_HYP_A.md` (the
  first-kind sibling `gmA`, same curve).

**Process.** I edited no Lean file and ran no git command. My scratch files are in `reviews/checks/hypan/`:
* `check_an.py` / `check_an.out` (mpmath, 70 digits, 6 s). This is independent of `checks/hypa/check_a.py`. It uses a
  different loop: a figure eight through x = 1/2, counterclockwise around 0 and then clockwise around 1. Along it, y is
  continued by explicit continuous logarithms and cross-checked by nearest-root tracking. A second computation integrates
  directly over γ = [0 → 1 on sheet y₀] + [1 → 0 on sheet ζy₀], substituting x = u⁵ at the endpoints. Result: **ALL OK**.
* `axAn.lean` / `axAn.out`: axiom audit (see the end of this report).

## Verdict: CORRECT WITH NOTES (no soundness or fidelity defect; scope, citation and cosmetic notes)

* For every `F`-basis `b` (`IsAdaptedBasisD`), `gmAn 5 2 (s ↦ s+1) perA5 perB5 b` is a sound W88 model of
  G″ = G_m^{2n} × Q″. Here Q″ = (A^♮)^r/W′ and A = Jac(y⁵ = x(1 − x)).
  - Q″ is a ℚ̄-algebraic group, an extension of A^r by G_a that does not split over any nonzero B ⊂ A^r.
  - The Lean coordinates (z(s, j), f), the ℚ̄-structure and the period generators are the right ones.
  - Every nonzero connected subgroup of Q″ contains the fibre G_a, so the product-form `sub` is right.
  - d₂ = 2r + 1 is exact.
* **The Lean group is not merely analogous to the paper's: it is isomorphic to it.** Take the paper's (A^♮)ⁿ/U with
  θ(j, e) = ζ^e b_j. The map x ↦ (Σ_e [ζ^{−e}] x_{(j,e)})_j identifies it with Lean's (A^♮)^r/W′, coordinates included
  (#5). Nothing is lost.
* The instance is right, to 10⁻⁵⁵ or better:
  - P̄ = `perB5` = (1 − ζ⁴)B(4/5, 4/5) is ∫_γ dx/y over the **same** closed cycle γ that gives `perA5 0`, `perA5 1`.
  - [ζ]^* dx/y = ζ⁴ dx/y.
  - dx/y is of the second kind (a pole of order 4 at ∞ with residue 0) and has a nonzero period. So its class spans the
    ζ⁴-eigenline of H¹_dR, which is not in H⁰(Ω¹).
  - `beta5_mul` holds numerically.
* `WuestholzB5` is true. It follows from Wüstholz's theorem on A^♮ × G_m (argument in #10). It is also **equivalent to
  Schneider's 1941 theorem** that B(1/5, 1/5) is transcendental.
* The statements match the paper:
  - `fourExpAt_beta5'` is Theorem A at t ∈ ℚ̄^× B(1/5, 1/5), for any fixed logarithms.
  - `two_three_beta5'` is the paper's headline example t = Γ(1/5)²/Γ(2/5), with the principal logarithms.
  - `fourExpAt_An` is the direct family t ∈ ℚ̄^× P̄/π of Theorem MG♮-A.

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | Q″ as an algebraic group; `algAn`; tangent coordinates | W′ ⊂ V^r (V = fibre of A^♮, dim g) is the ℚ̄-subspace {z = 0, Σ_j b_j w_j = 0}, of dim gr − 1. It contains **all** of the other second-kind directions (here w₃, from dx/y²). So Q″ has dim gr + 1, with tangent coordinates (z(s, j), f = Σ_j b_j w_j). `algAn` is exactly the image of the ℚ̄-structure |
| 2 | OK (verified) | `perAngen`: the CM direction on the fibre | w([ζ^e]X) = ⟨ω_σ̄, [ζ^e]_*X⟩ = ⟨[ζ^e]^*ω_σ̄, X⟩ = ζ^{(N−1)e} w(X). This is the same (pull-back) convention as the base slots ζ^{κ s · e}. Numerically: dx/y⁴, dx/y³, dx/y, dx/y² have eigenvalues ζ, ζ², ζ⁴, ζ³. span_ℚ `perAngen` = ℚ ⊗ Ker exp_{Q″}, of rank n, injective, with no periods in the fibre |
| 3 | OK | `sub`: every nonzero connected H ⊂ Q″ contains the fibre | H ∩ G_a ∈ {0, G_a}. If it is 0 and the image B_S is nonzero, then F3 gives W′ ⊇ W_{B_S}. By F4 that means Σ_j b_j σ̄(m_j) = 0 for all m ∈ S, and σ̄(m_j) ∈ F, so F-independence of b forces S = 0. The docstring argument (l. 23–25) is right, but terse (#13) |
| 4 | OK | d₀, d₁, d₂ | Q″ is a quotient of the anti-affine (A^♮)^r, so Hom(Q″, G_a) = Hom(Q″, G_m) = 0, d₀ = 0 and d₁ = 2n. d₂ = `finrank` = gr + 1 = dim Q″ exactly (= n/2 + 1, the paper's value), and it is not undercounted. Goursat gives products T_L × H |
| 5 | OK (stronger than claimed) | Lean group vs the paper's (A^♮)ⁿ/U | With θ(j, e) = ζ^e b_j, the paper's U = B^♮_{ker ψ_σ} + {θᵀt_σ = 0} is exactly the kernel of (A^♮)ⁿ → (A^♮)^r → Lean's Q″, so the two groups are isomorphic, not just isogenous. Lean's toric part, V″, W″ and data are the paper's. TRUST.md l. 167–169 ("isogenous … via CM quotient maps") is conservative here |
| 6 | OK | Lemma U range | Ω_ℚ(G″) has ℚ-dim 3n and spans T(G″) over ℂ, so κ ≤ 3n − 1 for every hyperplane. 2N = 4n + 2gr = 5n ≥ 2n + κ in **every** instance. This is the paper's "5n ≥ 3n" |
| 7 | NOTE | generic `fourExpAt_An`, `Thm11KappaAn N g κ P P̄` | This is a W88 instance only for parameters that come from a real A. Two conditions are implicit: φ(N) = 2g (forced; Lean assumes only 2g ≤ φ(N)), and ζ ↦ ζ^{N−1} ∉ Φ, i.e. 1 ∈ κ(Fin g). Otherwise w is a base coordinate and Q″ makes no sense. `fourExpAt_An` has no κ s₀ = 1 hypothesis (the proof does not need one), and the docstring only says "as in ThmA.lean". For bad parameters the theorem is vacuous; the instance carries the content (same as REFEREE_HYP_A #5) |
| 8 | OK (verified) | `perB5` = ∫_γ dx/y, the same γ as `perA5` | The loop integrals over L = −γ are −(1 − ζ^j)B(j/5, j/5) for k = 1, 2, 3, 4 (j = 5 − k), with \|diff\| ≤ 7·10⁻⁷¹. The direct integrals over γ agree to ≤ 4·10⁻⁷⁰. The formula extends to j = 4 (and j = 3): B(4/5, 4/5) converges, and γ passes through the totally ramified points over 0 and 1, where dx/y = 5u³du is holomorphic. The 4×4 period matrix of [ζ^e]γ̃ in (z₀, z₁, w₄, w₃) has \|det\| = 8224.67 ≠ 0 |
| 9 | OK (verified) | dx/y represents the w-coordinate | ord_∞(dx/y^k) = 2k − 6, so dx/y has a pole of order 4 at the single point at ∞. Its residue is 0 (a five-turn integral: \|·\| = 3·10⁻⁷⁰), so it is of the second kind and its periods are well defined on H₁(C). Its period is 1.78329840858… ≠ 0, so [dx/y] ≠ 0 spans the ζ⁴-eigenline. Since H⁰(Ω¹) = ζ¹ ⊕ ζ² lines, this class is not in H⁰(Ω¹) |
| 10 | OK | `WuestholzB5` true as stated | Suppose P̄ = aπ. Then the period (γ̃, 2πi) of A^♮ × G_m lies in the ℚ̄-hyperplane w = (a/2i)x. Connected subgroups are products, and A is simple, so F3 says any subgroup over A is all of A^♮. So the smallest subgroup is A^♮ × G_m, which is not in the hyperplane. Also: P̄/π = (1 − ζ⁴)ρ/B(1/5, 1/5) (verified), so `WuestholzB5` ⟺ B(1/5, 1/5) ∉ ℚ̄, which is **Schneider 1941** |
| 11 | OK (verified) | `beta5_mul`, `rho5` | Γ(8/5) = (3/5)Γ(3/5) plus two reflections. Numerically \|diff\| = 1.5·10⁻⁷⁰, and ρ = 4.58793973490391… |
| 12 | OK | `fourExpAt_beta5'`, `two_three_beta5'` vs Theorem A | With c′ = (c(1 − ζ⁴)ρ)⁻¹, the inverse of c′P̄/π is cB(1/5, 1/5) (checked numerically for c = 7/3 + 2i). This is exactly the paper's route ("B(1/5, 1/5) … by Theorem MG♮-A (inverted)", l. 536–537). `betaIntegral (1/5) (1/5)` = Γ(1/5)²/Γ(2/5) |
| 13 | COSMETIC | docstring l. 11–25 | (a) Notation clash: Lean's σ̄ is the paper's σ ∉ Φ, and Lean's P̄ is the paper's P_σ. The paper's "P_{σ̄} ∉ ℚ̄" (l. 496) is Lean's `perA5 0`. One sentence would prevent confusion. (b) The `sub` argument omits the cases "image 0" and "H ∩ G_a = G_a", and the fact that algebraic subgroups of G_a are 0 and G_a. (c) "W′ = {fibre vectors with Σ_j b_j w_j = 0}" should say that w_j is the σ̄-coordinate of copy j, and that W′ contains the other fibre eigen-directions |
| 14 | NOTE (scope) | MG♮-A vs Lean | Lean proves the consequence `FourExpAt (cP̄/π)`, not the dimension bound dim_K S♮_K ≤ 2. As in REFEREE_HYP_A #12, no "t·2πi ∉ ℚ̄𝓛" input is needed: `frame_false` only uses Y₁, Y₂ ℚ-independent, and a larger κ only helps. This is legitimate under the project's reading of §5d. Inverted family of MG♮-A: only `cB(1/5, 1/5)` = (c″P̄/π)⁻¹ is stated, since that is the target. The paper's example Γ(1/7)²/Γ(2/7) is not covered (it needs a level-7 second-kind instance) |
| 15 | COSMETIC | `two_three_beta5'` (l. 250–256) | Uses the principal Complex.log. The paper says "any choice of log 2, log 3". That case is covered by `fourExpAt_beta5'`, since every determination lies in `logAlg` and any two choices are ℚ-independent, but no theorem states it |
| 16 | COSMETIC | TRUST.md | Row l. 175 (`Thm11KappaAn`) and row l. 186 (`WuestholzB5`) cite this report but carry no verdict yet. Suggest "CORRECT WITH NOTES" and, for `WuestholzB5`, "equivalently Schneider 1941 (B(1/5, 1/5) transcendental)". Optional: in l. 167–169, note that for `gmAn` the identification is an isomorphism |
| 17 | TRUST NOTE | residual | Two items remain trusted. (i) W88 §5d (trust point T: W ≠ 0, κ > 0) for G_m^{2n} × Q″, with Q″ a non-split G_a-extension of A^r and A a simple CM abelian surface. This is the same regime as `gmMGn`; the second application inside §5d is still unchecked (REFEREE_HYP_GEN #16). (ii) Soundness of `sub` uses (F1)–(F4), i.e. Mazur–Messing universality plus Poincaré reducibility, which the paper labels Lit/Proved. Neither is a Lean hypothesis |

## Details

### 1–2. Q″, its coordinates and its periods [Proved, given (F1), Mazur–Messing; numerics for the instance]

**Coordinates.** A = Jac(C), C: y⁵ = x(1 − x), genus 2, with CM by ℤ[ζ₅] via [ζ](x, y) = (x, ζy). Lie(A^♮) = H¹_dR(C/ℚ̄)^∨,
and the period lattice is H₁(C, ℤ) via γ ↦ (ω ↦ ∫_γ ω).
* The ℚ-rational classes dx/y⁴, dx/y³ (holomorphic) and dx/y, dx/y² (second kind) are [ζ]^*-eigenvectors, with
  eigenvalues ζ¹, ζ², ζ⁴, ζ³.
* They are pairwise distinct and all have nonzero periods (#8), so they form a ℚ̄-basis of H¹_dR.
* The dual coordinates are (z₀, z₁, w₄, w₃). The fibre V = Lie of the vector part is {z₀ = z₁ = 0} (F1). w = w₄ is the
  σ̄-coordinate, σ̄: ζ ↦ ζ⁴ = ζ^{N−1}.

**The quotient.** On (A^♮)^r, W′ = {z = 0, Σ_j b_j w_{4,j} = 0}. It has no condition on the w₃-coordinates, so
dim W′ = 2r − 1. It is a ℚ̄-subspace of the vector group V^r (b is algebraic: `IsAdaptedBasisD.alg`), hence a ℚ̄-algebraic
subgroup.
* Q″ = (A^♮)^r/W′ is a commutative algebraic group over ℚ̄ of dimension 4r − (2r − 1) = 2r + 1 = gr + 1.
* Its Lie algebra has coordinates (z(s, j), f) with f = Σ_j b_j w_{4,j}, the `snd` component of `(Fin g × Fin r → ℂ) × ℂ`.
* The ℚ̄-structure of T(Q″) is the image of that of T((A^♮)^r): {(z, f) : z ∈ ℚ̄^{2r}, f ∈ ℚ̄}. For "⊇", take
  f = b_{j₀}·(f/b_{j₀}). This is `algAn`.

**Periods.** W′ is a vector group, so exp⁻¹(W′) = Lie W′ and Ker exp_{Q″} is the image of Ker exp_{(A^♮)^r}.
* That kernel is ⊕_j H₁(A, ℤ)·γ̃, with H₁(A, ℚ) = Fγ, since A is simple with End⁰ = F (REFEREE_HYP_A #7).
* The image of [ζ^e]γ̃ in copy j has base coordinates z_s = ζ^{κ_s e}P_s, in copy j only, and fibre value
  f = b_j·w₄([ζ^e]γ̃) = b_j ζ^{4e}P̄.
* The direction is right: both z_s and w₄ are pairings with eigen-classes, and [ζ^e]_* on cycles is dual to [ζ^e]^* on
  forms (check 3: [ζ]_*L integrates dx/y^k to ζ^{−k} times the integral over L).
* The ℚ-span of {[ζ^e]γ̃ : e ∈ ℕ} is Fγ̃, so span_ℚ `perAngen` = ℚ ⊗ Ker exp_{Q″}.
* The map lattice → T(Q″) is injective: base coordinates already separate H₁(A^r). So the rank is 2gr = n.
* The proof uses the generators with index (j, (N − 1)e), whose fibre value is b_j ζ^{(N−1)²e}P̄ = θ_{(j,e)}P̄
  (`zetaN_pow_sq`). So λ(qh h) = (cP̄/π)·2πiθ_h, the period lift of the frame. It lies in span_ℚ `perAngen` (l. 87–88).

### 3. `sub` for Q″ [Proved, given (F2)–(F4)]

Let H ⊂ Q″ be connected and nonzero, with image B in A^r. By (S1), B = B_S for an F-subspace S ⊂ F^r. H ∩ G_a is an
algebraic subgroup of G_a, so it is 0 or G_a (characteristic 0, and the subgroup is connected in either case).
* **H ∩ G_a = G_a.** Then the fibre direction (0, 1) lies in T_H and λ = f = 1 on it.
* **H ∩ G_a = 0.** Then B ≠ 0, and the preimage H̃ ⊂ (A^♮)^r is connected (W′ is connected), lies over B and has
  H̃ ∩ V^r = W′.
  - By F3 this forces W′ ⊇ W_{B_S}.
  - By F4, W_{B_S} contains the vectors with w₄-coordinates (σ̄(m_j))_j, m ∈ S, and other coordinates 0.
  - So Σ_j b_j σ̄(m_j) = 0 for all m ∈ S.
  - F = ℚ(ζ₅) is Galois, so σ̄(m_j) ∈ F ⊂ ℂ. `IsAdaptedBasisD.indep` (θ = (ζ^e b_j) is ℚ-independent) says exactly that b is
    F-independent. Hence m = 0, S = 0, a contradiction.
  
So every nonzero connected subgroup contains the fibre, and λ ≢ 0 on T_H.

Subgroups of G″: no subquotient of Q″ is a nonzero torus (they are extensions of abelian varieties by unipotent groups),
so Goursat gives T_L × H (as in REFEREE_HYP_GEN #3). `sub` in `gmF` is the superset "h = ⊥ or λ ≠ 0 somewhere on h". The
argument works for subgroups over ℂ as well. The ∀ b in `Thm11KappaAn` is harmless: soundness uses only that b is algebraic
and F-independent.

### 4. d-values [Proved]

* (A^♮)^r is anti-affine, and so is its quotient Q″. So Hom(Q″, G_a) = Hom(Q″, G_m) = 0, d₀ = 0 is maximal, and d₁ = 2n.
* d₂ = `finrank ℂ ((Fin g × Fin r → ℂ) × ℂ)` = gr + 1 = dim Q″, exact.
* In the instance, n = 4r and d₂ = n/2 + 1, the paper's value.
* `hfin` (l. 114–117) is gr + 1 < φ(N)r. It follows from 2 ≤ g and 2g ≤ φ(N), and it is the frame's `dim Q < n`.
* So (5.4) reads 3n > (2n + 2(n/2 + 1) − κ)·(0 or 1). With κ ≥ n this needs n > 2, which matches the paper's minimum
  margin n − 2.

### 5. The paper's (A^♮)ⁿ/U is Lean's Q″ [Proved]

Paper (l. 487–491): θ is a ℚ-basis of K, n = [K : ℚ] copies, U = B^♮_{ker ψ_σ} + {θᵀt_σ = 0} with σ ∉ Φ (Lean's σ̄).
Take θ(j, e) = ζ^e b_j (Lean's `thetaD`), and define
* π: (A^♮)ⁿ → (A^♮)^r, x ↦ (Σ_e [ζ^{−e}] x_{(j,e)})_j.

This map is surjective (the e = 0 term), and its kernel is ≅ (A^♮)^{n−r}, which is connected.
* **Base.** Σ_{j,e} ζ^e b_j σ̄(m_{je}) = Σ_j b_j σ̄(M_j) with M_j = Σ_e ζ^{−e}m_{je}. By F-independence of b,
  ker ψ_σ̄ = {M = 0}, which is the kernel of π on H₁.
* **Kernel of π.** ker π is a connected subgroup over B_{ker ψ}, with fibre of the full dimension g(n − r). By F3,
  ker π = B^♮_{ker ψ}.
* **Fibre.** f∘π = Σ_j b_j Σ_e σ̄(ζ^{−e}) t_{σ̄,(j,e)} = θᵀt_σ̄.
* **Conclusion.** π⁻¹(W′) = B^♮_{ker ψ} + {θᵀt_σ̄ = 0} = U, so (A^♮)ⁿ/U ≅ Q″, compatibly with the coordinates
  ([z], θᵀt_σ̄) ↔ (z, f).

The toric part G_m^{2n}, Ψ″, V″ = Ψ″⁻¹(ℂ(1, s)), W″ = ker Ψ″ and the 3n generators are those of the paper's proof (l. 487–496).
So Lean's G″ is the paper's G″, and nothing is lost. The paper's K ⊇ F^c(i, c) is provided by `exists_adapted_basisN`
({c, I} ⊂ K ⊇ F = F^c), and its [K′ : ℚ] ≥ 4 is automatic, since n = 4r.

### 8–9. The instance [Numerical, 70 digits]

`check_an.out`, parts 1–4:

| differential | eigenvalue | ∫_γ (loop L = −γ and direct) | formula | \|diff\| |
|---|---|---|---|---|
| dx/y⁴ (holomorphic) | ζ (κ = 1) | `perA5 0` | (1 − ζ)B(1/5, 1/5) | 7·10⁻⁷¹ |
| dx/y³ (holomorphic) | ζ² (κ = 2) | `perA5 1` | (1 − ζ²)B(2/5, 2/5) | 7·10⁻⁷¹ |
| dx/y (2nd kind) | ζ⁴ = ζ^{N−1} | `perB5` | (1 − ζ⁴)B(4/5, 4/5) | 4·10⁻⁷¹ |
| dx/y² (2nd kind) | ζ³ | — | (1 − ζ³)B(3/5, 3/5) | 4·10⁻⁷¹ |

* **The branch.** The branch of y along L is closed on the curve: it starts on y₀, reaches ζy₀ after the loop around 0,
  and returns to y₀. Nearest-root tracking agrees with the continuous-log branch to 3·10⁻³¹ (at 30 digits).
* **One cycle for all three periods.** All three Lean periods are integrals over the same γ. This is what `perAngen`
  needs: the base and fibre values of one period γ̃.
* **Why the j = 4 formula is valid.** The formula (1 − ζ^j)B(j/5, j/5) comes from γ = [0 → 1, y₀] − [0 → 1, ζy₀]:
  ∫_γ dx/y^k = (1 − ζ^{−k})B(1 − k/5, 1 − k/5), and 1 − ζ^{−k} = 1 − ζ^j. For k = 1 the real integral converges
  (x^{−1/5}), and the point at ∞, where dx/y has its pole, is not on γ. So the formula extends to j = 4.

### 10. `WuestholzB5` [Lit, true as stated]

**From Wüstholz.** Suppose P̄/π = a′ ∈ ℚ̄. Then u = (γ̃, 2πi) ∈ Lie(A^♮ × G_m) has exp u = 0 and lies in the ℚ̄-hyperplane
w₄ = (a′/2i)x. By the analytic subgroup theorem, there is a connected algebraic subgroup H with u ∈ Lie H ⊂ hyperplane.
* H = H₁ × (G_m or 0) by Goursat, and the G_m-component of u is 2πi ≠ 0, so H = H₁ × G_m.
* H₁ ⊂ A^♮ contains γ̃, whose image γ ≠ 0, so H₁ maps onto the simple A.
* By F3, H₁ ∩ V ⊇ W_A = V, so H₁ = A^♮.
* But Lie(A^♮ × G_m) ⊄ {w₄ = a″x}. Contradiction.

This is the paper's derivation of (W) (l. 359–367, with F3 at l. 384).

**Equivalently, Schneider.** P̄/π = (1 − ζ⁴)B(4/5, 4/5)/π = (1 − ζ⁴)ρ/B(1/5, 1/5) (check 7, \|diff\| = 5·10⁻⁷²). So
`WuestholzB5` ⟺ B(1/5, 1/5) ∉ ℚ̄. That is Schneider's theorem (J. reine angew. Math. 183, 1941): B(a, b) is transcendental
for a, b, a + b ∈ ℚ ∖ ℤ. The input is therefore classical, older than Wüstholz.

Side remark, outside this review's scope: `WuestholzA5` (B(1/5, 1/5)/π ∉ ℚ̄) is likewise ⟺ B(4/5, 4/5) ∉ ℚ̄, which is
also Schneider.

### 12. Statements [Proved by Lean, reading checked]

* **`fourExpAt_An`.** FourExpAt(cP̄/π) for c ∈ ℚ̄^×, under `hW`, 2 ≤ g, 2g ≤ φ(N) and P̄/π ∉ ℚ̄. This is the direct
  family t = cP⁻/π of the proof of Theorem A (l. 516), for P⁻ the second-kind period.
* **`fourExpAt_beta5'`.** FourExpAt(cB(1/5, 1/5)) for all c ∈ ℚ̄^×. FourExpAt quantifies over all a, b ∈ `logAlg`, i.e.
  every determination of the logarithms, so this is Theorem A at t ∈ ℚ̄^× B(1/5, 1/5), the inverted MG♮-A family.
* **`two_three_beta5'`.** "2^t, 3^t not both algebraic at t = `betaIntegral (1/5) (1/5)`" = Γ(1/5)²/Γ(2/5), with the
  real logarithms. This is the paper's first example (l. 96) and the abstract's headline.
* **Hypotheses.** Only `hW` (W88 §5d for the sound model) and `WuestholzB5` (true). The second-kind period is pinned to the
  cycle by the definitions, and `beta5_mul` is proved in Lean. So the theorems are not vacuous (modulo W88).

## Falsification attempts (none succeeded)

* **Wrong CM direction on the fibre.** Suppose w([ζ]X) were ζ·w(X) instead of ζ⁴·w(X). Then the fibre values in
  `perAngen` would not be periods. Checked numerically: the integral of dx/y over [ζ]_*L is ζ⁴ times the integral over L,
  and the base slots use the same convention (ζ¹, ζ²).
* **Different cycles for P and P̄.** If `perB5` were the period over a different cycle than `perA5`, the generator
  [ζ^e]γ̃ would mix two lattice vectors and would not be a period. All three come from one loop (#8).
* **dx/y secretly holomorphic or exact.** It has a pole of order 4, and its period is nonzero, so its class is nonzero. Its
  eigenvalue ζ⁴ ∉ {ζ, ζ²}, so its class is not in H⁰(Ω¹).
* **A subgroup of Q″ not containing the fibre.** This needs Σ_j b_j σ̄(m_j) = 0 with m ≠ 0, which F-independence rules
  out (#3). This holds for every b allowed by `IsAdaptedBasisD`.
* **Undercounted d₂, inflated κ.** d₂ = dim Q″ exactly. per = ℚ ⊗ Ker exp exactly: the fibre has no periods, and the
  lattice injects.
* **Lemma U.** 5n ≥ 2n + κ for every κ ≤ 3n − 1 (#6).
* **Encoding traps.**
  - `zetaN_pow_sq`: (N − 1)²e ≡ e (mod N), with the primitive root from `zetaN_prim`.
  - The generator index (p.1, (N − 1)·p.2) in `hqh` is the one in `pv`.
  - `snd` is f, and ker f is spanned by the algebraic vectors (e_p, 0) (l. 129–141).
  - q₁ = (0, 1) has λ = 1 and is algebraic.

## Axiom audit

`checks/hypan/axAn.lean` / `axAn.out`. My first attempt hit a concurrent `lake build` from another session: the `Frame2`
olean was missing while it was being rebuilt. I did not start a build myself. After that build finished, `ThmAn.olean`
(01:16:04) was newer than `ThmAn.lean` (01:04:36), and the audit gives:
* `fourExpAt_An`, `beta5_mul`, `fourExpAt_beta5'` and `two_three_beta5'` each depend only on
  [propext, Classical.choice, Quot.sound] [Proved by Lean].
* `#check two_three_beta5'` shows exactly the hypotheses `Thm11KappaAn 5 2 (s ↦ s+1) perA5 perB5` and `WuestholzB5`.
* `perB5` = (1 − ζ₅⁴)·`betaG (4/5) (4/5)`, and `WuestholzB5` = `Transcendental ℚ (perB5 / π)`.

## Verdict lines

* Item 1 (soundness of `gmAn`, `sub`, d₂, use of Lean's Q″ in place of the paper's (A^♮)ⁿ/U, `Thm11KappaAn` ∀ b):
  **CORRECT WITH NOTES** (#7 implicit parameter conditions on the generic hypothesis; #13 docstring). The groups are
  isomorphic.
* Item 2 (instance: `perB5` = ∫_γ dx/y over the same γ, σ̄-eigen, w-coordinate; `beta5_mul`): **CORRECT** (verified to
  ≤ 4·10⁻⁷⁰).
* Item 3 (`WuestholzB5`): **CORRECT**, true as stated. It follows from Wüstholz on A^♮ × G_m and is equivalent to Schneider
  1941 (B(1/5, 1/5) ∉ ℚ̄); suggest citing Schneider.
* Item 4 (statement fidelity of `fourExpAt_An`, `fourExpAt_beta5'`, `two_three_beta5'`): **CORRECT WITH NOTES** (#14 scope,
  #15 principal logarithms in the corollary).
* Overall: **CORRECT WITH NOTES**. No soundness or fidelity defect. Residual trust: W88 §5d (trust point T) for
  G_m^{2n} × Q″, plus (F1)–(F4) as soundness facts.
