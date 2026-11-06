# Referee report: the named classical inputs of `CM4E/AbVar/X7.lean`

Scope: `WuestholzBeta7` and `WuestholzX7 LA` (commit 697eabb), with definitions from `CM4E/AbVar/Fermat7.lean`
(`zeta7`, `alpha7`, `betaG`, `perA`, `omega7`, `mu7'`) and `CM4E/Gen/ThmM.lean` (`LogE`). The paper source is
draft [II]: §`sec:setting` ((S1), (P), (W)), §`sec:X` (slot splitting) and §`sec:X7`.
The W88 hypothesis `Thm11KappaX7` is not in scope. No Lean file was edited and git was not run.
Scratch files are in `reviews/checks/inputsx7/`: `pslq_x7.gp` / `.out` and `cs_49a1.gp` / `.out`.

Labels: [Lit] = published theorem; [Proved] = derived here from [Lit] with a complete argument;
[Numerical] = numerical evidence only.

**Verdicts**
* `WuestholzBeta7`: **TRUE AS STATED.**
* `WuestholzX7 LA`: **TRUE WITH NOTES.** It holds for the intended `LA`, and also for every subset of it and for the
  ℚ̄-span of the logarithms. It is false for some other choices of `LA`, which makes `thmX7` vacuous, not wrong.
  TRUST.md must say exactly which `LA` is intended (§4).

---

## 0. Geometric facts used (all [Lit] or elementary)

**(G1) The curve and its periods.** [Proved, elementary]
* `C : y⁷ = x(1−x)` has three branch points (0, 1, ∞), each totally ramified (at ∞, `y⁷ ~ −x²` and gcd(7,2) = 1).
  Riemann–Hurwitz gives `2g − 2 = 7·(−2) + 3·6`, so `g = 3`.
* Take local parameters with `x ~ t⁷, y ~ t` at 0 and 1, and `x ~ t⁻⁷, y ~ t⁻²` at ∞. Then `dx/y^k` has order `6 − k`
  at 0 and 1, and order `2k − 8` at ∞. So `dx/y^k` is holomorphic exactly for `k = 4, 5, 6`. These three differentials
  are defined over ℚ.
* `[ζ] : y ↦ ζy` pulls `dx/y^{7−s}` back to `ζ^s · dx/y^{7−s}`. So `A = Jac C` has `ℤ[ζ₇] ⊂ End A` and CM type
  `{1, 2, 3}`.
* The stabiliser of `{1, 2, 3}` in `(ℤ/7)ˣ` is trivial (u = 2 gives {2,4,6}, u = 3 gives {3,6,2}, and so on), so the
  type is primitive. By Shimura–Taniyama [Lit] (Shimura, *Abelian varieties with CM*, §8.2; also Koblitz–Rohrlich,
  Canad. J. Math. 1978), **A is simple** with `End⁰A = F = ℚ(ζ₇)`.
* **Periods.** Let `γ` = (lift of [0,1] to the sheet y > 0) − (its image under `[ζ]`). Both paths run from the
  ramification point over 0 to the one over 1, so `γ` is closed. On the first path the integral is
  `∫₀¹ x^{j/7−1}(1−x)^{j/7−1} dx = B(j/7, j/7)`. On the image path `(ζy)^{−(7−j)} = ζ^j y^{−(7−j)}`, which gives
  `ζ^j B`. Hence `z_s(γ) = ∫_γ dx/y^{7−s} = (1 − ζ^s)B(s/7, s/7) = perA s` **exactly**. Here `z_s` is the
  ℚ̄-rational eigen-coordinate on `Lie A` dual to `dx/y^{7−s}` (the Abel–Jacobi integral).
  [Numerical] `intnum` check of the three integrals: errors ≤ 1e-37.
* As a cross-check, the Koblitz–Ogus labels of `B(1/7,1/7)`, `B(2/7,2/7)`, `B(3/7,3/7)` are `{1,2,3}`, `{1,4,5}`,
  `{1,3,5}`. These are `Φ`, `4Φ` and `5Φ`, i.e. the three embeddings of the same simple `A`. The label of `B(1/7,2/7)`
  is `{1,2,4}`, induced from `ℚ(√−7)`. The four labels are pairwise distinct.

**(G2) The elliptic curve, and the Lean lattice `E7 = Ω·ℤ[α]`.**
* **α.** `α = ζ + ζ² + ζ⁴ = (−1 + √−7)/2`, since `Im α = sin(2π/7) + sin(4π/7) − sin(π/7) > 0`. So `ℤ[α] = O_K` with
  `K = ℚ(√−7)`, class number 1.
* **Chowla–Selberg** [Lit] (Gross 1978, Invent. Math. 45, with Rohrlich's appendix). Take `D = −7`, `w = 2`, `h = 1`,
  and `χ = (1,1,−1,1,−1,−1)` on 1, …, 6. Normalise the formula on the lemniscatic case (the lemniscate constant
  `ϖ ∈ ℚ̄ˣ Γ(1/4)²/√π`). Then reflection gives a period of E in `ℚ̄ˣ · Γ(1/7)Γ(2/7)/Γ(3/7) = ℚ̄ˣ · B(1/7, 2/7)`.
* Any E/ℚ̄ with CM by `O_K` (for example 49a1, `j = −3375`) has period lattice `ω_E·O_K` with respect to a ℚ̄-rational
  differential (class number 1). Then `Ω ℤ[α] = λ·Λ_E` with `λ = Ω/ω_E ∈ ℚ̄ˣ`. Since `g₂(λΛ) = λ⁻⁴g₂(Λ)` and
  `g₃(λΛ) = λ⁻⁶g₃(Λ)`, **the lattice `E7` has algebraic `g₂, g₃`**. So `y² = 4x³ − g₂x − g₃` is a curve over ℚ̄ whose
  period lattice for `dx/y` is exactly `Ωℤ[α]`, and `𝓛_E = LogE E7` is meaningful.
* [Numerical] (PARI, 300 digits, `cs_49a1.out`):
  * `ω₁(49a1)/B(1/7,2/7)` is a root of `49x³ − 7x + 1` (residual 0e-307). With `x = y/7` this is the cyclic cubic
    `y³ − 7y + 7` of conductor 7, so the ratio lies in `ℚ(ζ₇)⁺`.
  * `ω₂/ω₁` is a root of `x² − x + 2`.
  * `g₂(Ωℤ[α])` is a root of the irreducible cubic `1075648x³ − 384160x² + 14700x − 125` (residual 4e-306).
  * `g₃(Ωℤ[α])` is a root of the irreducible cubic `60236288x³ − 2612288x² + 3920x − 1` (residual 6e-308).
  * `j(Ωℤ[α]) = −3375` to 300 digits.
* Mathlib's `PeriodPair.weierstrassP` is the standard series `Σ' (1/(z−l)² − 1/l²)`. At lattice points it returns a junk
  value, but those points are in `LogE` through the first disjunct anyway.

**(G3) Subgroups.** [Lit / Proved]
* `Hom(A, E) = 0`, since A is simple of dimension 3.
* Abelian subvarieties of `A^m × E^k` are products `B × B'`: a homomorphism from the A-isotypic part to `E^k`
  vanishes (Poincaré reducibility).
* Connected algebraic subgroups of `G_a × (abelian variety)` are products `L × B` (paper (P); `Hom(B, G_a) = 0`).
* Every abelian subvariety `B ⊂ A^m` is stable under the diagonal action of `F`, because `F` is the centre of
  `End⁰(A^m) = M_m(F)` and `B` is the image of an idempotent. So `T(B)` is the direct sum of its σ-eigen-components
  (σ = σ₁, σ₂, σ₃, pairwise distinct characters).

**(AST) Wüstholz's analytic subgroup theorem** [Lit] (G. Wüstholz, *Multiplicity estimates on group varieties*,
Ann. of Math. 129 (1989) 471–500; statement as Thm 6.1 in Baker–Wüstholz, *Logarithmic Forms and Diophantine Geometry*,
CUP 2007, cited from memory). Let `G/ℚ̄` be a commutative algebraic group, `W ⊂ Lie G` a ℚ̄-subspace, and `ξ ∈ W` with
`exp_G ξ ∈ G(ℚ̄)`. Then there is a connected algebraic subgroup `H/ℚ̄` with `ξ ∈ Lie H ⊂ W`.

---

## 1. `WuestholzBeta7`: TRUE AS STATED

Statement: for algebraic `a₀, …, a₄`, `a₀ + a₁P₁ + a₂P₂ + a₃P₃ + a₄Ω = 0` implies that all `aᵢ` are 0. Here
`Pⱼ = perA j` and `Ω = omega7 = B(1/7,2/7)`.

**Derivation** [Proved from (AST), (G1)–(G3)]:
1. Let `G = G_a × A × E`, with E the curve of (G2) whose lattice is `Ωℤ[α]` (so Ω is itself a period). Let
   `ξ = (1, γ, Ω) ∈ Lie G`. Then `exp ξ = (1, 0, 0) ∈ G(ℚ̄)`.
2. Let `ℓ = a₀t + a₁z₁ + a₂z₂ + a₃z₃ + a₄z_E`. Here `t, z₁, z₂, z₃, z_E` are ℚ̄-rational coordinates forming a
   **basis** of `(Lie G)^∨`: they are dual to `dt, dx/y⁶, dx/y⁵, dx/y⁴, dx/y`. By (G1), `ℓ(ξ)` is the given relation,
   so `ℓ(ξ) = 0`.
3. If `ℓ ≠ 0`, apply (AST) to `W = ker ℓ`. This gives `H = L × B₁ × B₂` by (G3). Then:
   * `t(ξ) = 1` forces `L = G_a`;
   * `γ ≠ 0` and A simple force `B₁ = A`;
   * `Ω ≠ 0` forces `B₂ = E`.

   So `Lie H = Lie G ⊄ ker ℓ`, a contradiction. Hence `ℓ = 0`, so every `aᵢ = 0`.

Notes:
* Only `z_s(γ) ∈ ℚ̄ˣ P_s` for one cycle and `ω_E ∈ ℚ̄ˣΩ` are needed. Since `H₁(A,ℚ) = Fγ`, another choice of cycle
  changes `z_s` by `σ_s(F)`. So the statement does not depend on the cycle or on the normalisation of E.
* The statement is equivalent to the ℚ̄-independence of `1, B(1/7,1/7), B(2/7,2/7), B(3/7,3/7), B(1/7,2/7)`, because
  the factors `1 − ζ^j` are units. An alternative literature route is Wolfart–Wüstholz, Math. Ann. 273 (1985) 1–15:
  ℚ̄-linear relations among 1 and Beta values at rational points come only from coinciding eigen-slots, and the four
  KO labels above are distinct. (Citation from memory; check the exact statement before citing.)
* **Hidden-relation hunt.** The only known algebraic relation is `relation_R`, `P₁P₂ = μ'P₃Ω`. It is multiplicative
  (degree 2) and gives no linear relation. A ℚ̄-relation among the five real numbers would give one with real algebraic
  coefficients.

  [Numerical] PARI `lindep` (`pslq_x7.out`), inputs truncated to the stated precision. "Max |coef|" is the largest
  coefficient of the shortest vector found. A genuine relation would give a small vector with residual ~1e-615 when
  re-evaluated at 600 digits, as in the two controls.

  | coefficient field | n | digits | max \|coef\| | residual at 600 digits |
  |---|---|---|---|---|
  | ℚ | 5 | 120 | 4.5e21 | 4e-87 |
  | ℚ(cos 2π/7) = ℚ(ζ₇)⁺ | 15 | 300 | 1.7e16 | 6e-231 |
  | ℚ(√7) | 10 | 200 | 4.9e16 | 4e-153 |
  | ℚ(cos 2π/7, √7) | 30 | 500 | 1.6e13 | 6e-389 |
  | ℚ(cos 2π/7, 7^{1/4}) | 60 | 600 | 1.9e8 | 3e-485 |
  | ℚ(cos 2π/7), with π added | 18 | 400 | 6.7e17 | 2e-306 |
  | control: `B11·B22` vs `B12·B33` | 6 | 120 | 2 | 3e-615 |
  | control: `ω(49a1)` vs `B12` | 6 | 120 | 4 | 2e-616 |

  Every non-control row has a large shortest vector and a residual of about 10^(−0.75·digits). That is generic noise:
  no relation.
* `relation_R` holds numerically to 1.6e-614.

**Issues:** none affecting truth.
* (Cosmetic) The docstring could say "on one cycle γ" and "`G_a × A × E`, A simple, `Hom(A,E) = 0`, E with lattice
  `Ωℤ[α]` over ℚ̄ by Chowla–Selberg". It could also give the equivalent Beta-value form.

---

## 2. `WuestholzX7 LA`: TRUE WITH NOTES

Intended `LA` = `LA_A := {(z₁(v), z₂(v), z₃(v)) : v ∈ Lie A, exp_A v ∈ A(ℚ̄)}`. The `z_s` are the Abel–Jacobi
eigen-coordinates of (G1), the same ones for which `perT = (z₁(γ), z₂(γ), z₃(γ))`. In particular `perT ∈ LA_A`.

**Clause 1** [Proved]. Let `v ∈ LA_A ∪ {perT}`, `u ∈ 𝓛_E`, algebraic `q, c, c'`, and `z₁(v) + u + q = cP₁ + c'Ω`.
1. Take `G = G_a × A² × E²` and `ξ = (1, v, γ, u, Ω)`. Then `exp ξ = (1, exp v, 0, exp_E u, 0)` is algebraic. For
   `exp_E u` this uses (G2): either u is in the lattice, or `℘(u), ℘'(u) ∈ ℚ̄` on a curve over ℚ̄.
2. Let `ℓ = q·t + (z₁^{(1)} − c·z₁^{(2)}) + (z_E^{(1)} − c'·z_E^{(2)})`. It is ℚ̄-rational and `ℓ(ξ) = 0`.
3. (AST) gives `H = L × B × B'` with `B ⊂ A²` and `B' ⊂ E²` (G3), and `T_H ⊂ ker ℓ`.
4. **G_a part.** `t(ξ) = 1` gives `L = G_a`, so `(1,0,0) ∈ T_H` and `q = ℓ(1,0,0) = 0`. This is correct.
5. **A and E parts.** `ℓ` splits as (G_a part) + (A² part) + (E² part), and `T_H = T_L ⊕ T_B ⊕ T_{B'}`. So the A² part
   vanishes on `T_B ∋ (v, γ)`, which gives `z₁(v) = cP₁`. The E² part vanishes on `T_{B'} ∋ (u, Ω)`, which gives
   `u = c'Ω`.

**Clause 2** [Proved]. Let `v, v' ∈ LA_A ∪ {perT}` and `z₃(v') + z₂(v) + q = cP₃ + c'P₂`.
1. Take `G = G_a × A³` and `ξ = (1, v', v, γ)`.
2. Let `ℓ = q·t + (z₃^{(1)} − c·z₃^{(3)}) + (z₂^{(2)} − c'·z₂^{(3)})`. (AST) and (G3) give `H = G_a × B` with
   `B ⊂ A³`, hence `q = 0` as before.
3. By (G3), `T(B) = ⊕_σ T(B)_σ`, where the σ₃-component involves only the `z₃^{(i)}` and the σ₂-component only the
   `z₂^{(i)}`.
4. The A part of ℓ is (σ₃-form) + (σ₂-form), and it vanishes on `T(B)`. So each form vanishes on its own component.
5. The σ₃-projection of `(v', v, γ)` lies in `T(B)_{σ₃}`, which gives `z₃(v') = cP₃`. The σ₂-projection lies in
   `T(B)_{σ₂}`, which gives `z₂(v) = c'P₂`.

   This needs only `σ₂ ≠ σ₃` (`ζ² ≠ ζ³`). It does not need `v = v'`: different points sit in different copies of A,
   which is exactly how the Lean clause is quantified. It also handles `v = v'` and `v = perT`.

**The points raised in the brief**
* Different points `v, v'` in clause 2: handled, as above.
* E-lattice normalisation: `Ωℤ[α]` has algebraic `g₂, g₃` and `j = −3375` (G2: proof, plus numerics identifying them
  as cubic irrationals in `ℚ(ζ₇)⁺`). So `𝓛_E` is the set of logarithms of ℚ̄-points of a curve over ℚ̄, and the
  period `Ω = E7.ω₁` in the conclusion is a genuine period of that curve.
* `q = 0` splitting: correct. Only `T_L = Lie G_a` is needed, which `t(ξ) = 1` forces.
* Comparison with the paper's proof (§`sec:X`, "Slot splitting"): it is the same argument. The paper attributes the
  separation of slots a and d to (S1) ("independent vectors u_σ"). For a = z₁ and d = E on *different* varieties, the
  reason is the product decomposition `B × B'`, since `Hom(A,E) = 0`. The conclusion is unaffected; this is a wording
  point only.

**Robustness of the clause** [Proved, same arguments]
1. *Downward closed:* if `WuestholzX7 LA` holds and `LA' ⊂ LA`, then `WuestholzX7 LA'` holds.
2. It holds for `LA = ℚ̄-span` of the triples of logarithms (use `m` copies of A).
3. It only uses single coordinates (`v 0`, `v 1`, `v' 2`). So it would hold even for "incoherent" triples whose
   coordinates come from different points.
4. It is invariant under rescaling each `z_s` by a factor in ℚ̄ˣ.

Points 3 and 4 are **not** true of the soundness of `Thm11KappaX7`. That hypothesis uses the `[ζ^e]` action on a whole
triple (`aGen`: `ζ^{(s+1)e}v_s`, which is the correct convention, since `z_s([ζ]v) = ζ^s z_s(v)` by (G1)). It also
uses `perT` in the same normalisation as `LA`. So `LA` should be documented as coherent triples in the Abel–Jacobi
normalisation of (G1).

**Wrong instantiations make the hypothesis false.** Example: `LA = {(1,0,0)}`. Take `v = (1,0,0)`, `u = 0`, `q = −1`,
`c = c' = 0`. The premise `1 + 0 − 1 = 0` holds, but the conclusion `q = 0` fails. So `WuestholzX7 {(1,0,0)}` is false
and `thmX7` becomes vacuous for that `LA`.

### Issues for input 2

| # | severity | issue | fix |
|---|---|---|---|
| X1 | Minor (documentation) | The docstring "holds when LA consists of eigen-coordinate triples of logarithms of algebraic points of A" does not fix the normalisation of `z_s`. | Say "`z_s(v) = ∫ dx/y^{7−s}` (Abel–Jacobi, the coordinates with `z_s(γ) = perA s`), triples of one point `v` with `exp_A(v) ∈ A(ℚ̄)`; any subset is allowed". |
| X2 | Minor (documentation) | The role of E7 (curve over ℚ̄) is stated only in the module docstring of X7. | Add to TRUST.md: `g₂, g₃` of `Ωℤ[α]` are algebraic (Chowla–Selberg plus class number 1), and they are not proved in Lean. Numerically they are cubic irrationals with `j = −3375` (this report). |
| X3 | Info (paper) | §`sec:X`, slot splitting: separation of slots on different varieties is by the product decomposition, not by (S1). | Optional wording change: "slots on different isogeny classes separate because `H` is a product; slots on one `A` separate by (S1)". |

---

## 3. Is a parameter `LA` acceptable as a trust statement?

Yes, provided the documentation is explicit.
* `thmX7` is proved for **every** `LA ⊂ ℂ³`. Its hypotheses `Thm11KappaX7 LA` and `WuestholzX7 LA` are the only places
  where `LA` acquires meaning.
* If `LA` is instantiated badly, the hypotheses become false and the theorem vacuous. Nothing false is proved
  (`WuestholzX7` fails already for `LA = {(1,0,0)}`).
* The remaining risk is interpretive. Lean does not connect `v ∈ LA` with Jacobians, so reading `thmX7` as the paper's
  Theorem X7 rests on (i) the intended instantiation `LA = LA_A` and (ii) the truth of both hypotheses for it.
  This report establishes (ii) for `WuestholzX7`; `Thm11KappaX7` needs its own model review for the same `LA_A`.
* Since `WuestholzX7` is downward closed, any finite set of genuine logarithms is a legitimate instantiation.
* The same pattern is already used and accepted for `WuestholzMX` and `LogNat`.

## 4. Suggested TRUST.md wording

The §5 coverage row "Theorem X, Prop. 15, Theorem X7, Cor. X7 — ✗ not formalised" is out of date. Suggested rows for
§3:

> | `hW : AbVar.Thm11KappaX7 LA` | W88 §5d for `A^{3r} × E^{3r} × G_a²` (A = Jac(y⁷ = x(1−x)), E with lattice `B(1/7,2/7)ℤ[(−1+√−7)/2]`), every adapted `K ∋ ζ₇` | `CM4E/AbVar/X7.lean` (model `gmX7`) | Same source; hand-written model with logarithm parameter `LA` (review pending). |
> | `AbVar.WuestholzBeta7` | `1, P₁, P₂, P₃, Ω` are `ℚ̄`-linearly independent (`P_j = (1−ζ₇^j)B(j/7,j/7)`, `Ω = B(1/7,2/7)`); equivalently `1, B(1/7,1/7), B(2/7,2/7), B(3/7,3/7), B(1/7,2/7)` | `CM4E/AbVar/X7.lean` | Wüstholz 1989 on `G_a × A × E` at `(1, γ, Ω)`. A is simple (primitive CM type {1,2,3}), `Hom(A,E) = 0`, `P_j = ∫_γ dx/y^{7−j}` for one cycle γ, and `Ω` is a period of E (Chowla–Selberg). Review: `reviews/REFEREE_INPUTS_X7.md` (TRUE). |
> | `AbVar.WuestholzX7 LA` | slot splitting: `z₁(v) + u + q = cP₁ + c'Ω ⇒ q = 0, z₁(v) = cP₁, u = c'Ω`, and `z₃(v') + z₂(v) + q = cP₃ + c'P₂ ⇒ q = 0, z₃(v') = cP₃, z₂(v) = c'P₂` (`q, c, c' ∈ ℚ̄`, `u ∈ 𝓛_E`) | `CM4E/AbVar/X7.lean` | Wüstholz 1989 on `G_a × A² × E²`, resp. `G_a × A³`. True for `LA ⊂ LA_A` (defined below). Review: `reviews/REFEREE_INPUTS_X7.md` (TRUE WITH NOTES). |

And a paragraph under the table:

> **The parameter `LA`.** Lean has no Jacobians, so the logarithms of `A` enter `thmX7` as a set `LA ⊂ ℂ³`. The
> intended instantiation is any subset of
> `LA_A = {(z₁(v), z₂(v), z₃(v)) : v ∈ Lie A, exp_A(v) ∈ A(ℚ̄)}`, where `z_s(v) = ∫_v dx/y^{7−s}` are the Abel–Jacobi
> eigen-coordinates. These are the coordinates in which the period triple `perT = (P₁, P₂, P₃)` of the cycle γ is
> written. `thmX7` is proved for every `LA`. For a set that is not of this form, the hypotheses `Thm11KappaX7 LA` and
> `WuestholzX7 LA` can be false (for example `WuestholzX7 {(1,0,0)}` is false), and the theorem is then vacuous rather
> than wrong. Reading `thmX7` as the paper's Theorem X7 requires accepting that `LA_A` is the intended set. The
> facts that `g₂, g₃` of `B(1/7,2/7)ℤ[α]` are algebraic and that `P_j` are periods of A are part of this soundness
> statement; neither is proved in Lean.

---

## Verdicts

- `WuestholzBeta7`: **TRUE AS STATED** (Wüstholz 1989 on `G_a × A × E`; A simple, `Hom(A,E) = 0`,
  `z_s(γ) = perA s` exactly, `Ω` a period by Chowla–Selberg; PSLQ/LLL finds no relation in 6 coefficient fields up to
  600 digits).
- `WuestholzX7 LA`: **TRUE WITH NOTES**. It is true for every `LA ⊂ LA_A` (and for its ℚ̄-span), including different
  points `v ≠ v'`. The `q = 0` splitting is correct, and the E7 lattice is over ℚ̄ (`j = −3375`, cubic `g₂, g₃`). The
  notes are documentation only: fix the normalisation of `LA` in TRUST.md, and update the out-of-date coverage row.
