# Referee report: the hypotheses of `CM4E.MainQi.main` / `CM4E.TwoThree.two_three`

Referee: adversarial AI reviewer (Claude), 2026-10-30. No project file was edited. Scratch Lean checks are in
`C:\Users\SHAWNK~1\AppData\Local\Temp\claude\C--Users-Shawn-Krisman-math\9bf70abd-7b4c-4b52-88e0-7fbce744eb82\scratchpad\leanref\`
(`D0.lean`, `Strong.lean`). Both compile against the built project with standard axioms only.

**Note.** The project changed while this review was running. `hg₃` was removed from `main` and `two_three`, and
`g₃_lemniscatic : lemniscatic.g₃ = 0` is now proved in `Lattice.lean`. This report covers the current state:
the hypotheses are `hW`, `hg₂` and `hS`. `Thm11Kappa` itself did not change.

## Verdict

As far as I can check, the conditional theorem is a **faithful reduction to W88 §5d plus true facts**. I found no
encoding bug in `Thm11Kappa`, and no reason to think it is false or trivially refutable in Lean.

There is one improvement (item 4): the extra hypothesis "2πi, a, b ℚ-independent" is unnecessary. Dropping it gives
exactly `FourExpAt (cϖ/π)` for every c ∈ ℚ(i)ˣ. I checked this in Lean.

The real residual risk is not the encoding. It is whether W88's κ-refined Theorem 4.1 (§6–7, 1988 proceedings, one
source) is correct. That proof was outside this review (see item 1(k)).

| item | verdict |
|---|---|
| 1. Fidelity of `Thm11Kappa` to W88 Thm 1.1 + (5.4) | CORRECT (remarks only) |
| 2. Falsification attempts | no counterexample found; no trivial inconsistency |
| 3. Other hypotheses (`hg₂`, `hS`, and `g₃`) | CORRECT (true) |
| 4. Use in `main` / `two_three` | CORRECT; CORRECT WITH FIX for the claimed scope (drop 2πi) |

## 1. Fidelity of `Thm11Kappa`

I read the source pages myself: w88-01 (Thm 1.1, p. 375), w88-02 (p. 376), w88-06/07/08 (Thm 4.1 and Cor 4.3,
pp. 385–389), w88-10 (Lemma 5.2, p. 393) and w88-11 (§5d, (5.4), p. 394).

(a) **Hyperplane.** dim T_G = d₁ + 1, and `finrank ℂ V = d₁` is the right condition. d = d₁ + 1 ≥ 1, as Thm 1.1
requires. ✔

(b) **W.** Thm 1.1 asks for "W a subspace of V of dimension t ≥ 0, defined over ℚ̄". Lean has `W ≤ V` and
`RationalOverQbar W`, i.e. W is spanned by vectors with algebraic coordinates. That is the standard meaning. ✔

(c) **ℚ̄-structure on T_G.** On E: y² = 4x³ − g₂x − g₃ with x = ℘(z), y = ℘′(z), the invariant differential dx/y
pulls back to dz. So the coordinate z is ℚ̄-rational for the ℚ̄-structure that E/ℚ̄ induces on Lie E. On G_m, dX/X
pulls back to dt. So `AlgVec` (algebraic coordinates in (t, z)) is the right ℚ̄-structure. ✔

(d) **Y as a ℚ-span.** The source's Y is ℤy₁ + … + ℤy_m ⊂ V, of rank m. This is torsion-free inside a ℂ-space.
* rk_ℤ(ℤ-span) = dim_ℚ(ℚ-span). ✔
* κ = rk_ℤ(Y_ℤ ∩ Ker exp) equals dim_ℚ(Y_ℚ ∩ Ω_ℚ). Here Ker exp = 2πiℤ^{d₁} × L, and Ω_ℚ is its ℚ-span, so every
  element of Ω_ℚ is (1/N)·ω for some period ω.
  - "≤": Y_ℤ ∩ Ker ⊂ Y_ℚ ∩ Ω_ℚ.
  - "≥": for v ∈ Y_ℚ ∩ Ω_ℚ, some N·v lies in Y_ℤ ∩ Ker. So Y_ℤ ∩ Ker spans Y_ℚ ∩ Ω_ℚ over ℚ. ✔
* `ExpAlg` is required only of the generators. That suffices, because G(ℚ̄) is a group: E is defined over ℚ̄ since
  g₂, g₃ ∈ ℚ̄, and the addition law is ℚ̄-rational. Y ⊂ V is imposed through `y i ∈ V`. ✔
* The `⊓` is of two ℚ-submodules of the same ℚ-module `T d₁` (scalars restricted from ℂ). There is no mixing of
  scalar rings. ✔

(e) **κ convention.** The scan prints "κ = rk(Y ∩ Ker exp_G) = ℓ − m". The definition κ = rk(Y ∩ Ker), and
rk Y = rk Γ + κ in the proof of Lemma 5.2 (p. 393), show that ℓ − m is a misprint for m − ℓ. Lean uses the
definition. ✔ (Also, (5.5) is printed with "≥", but (5.4) gives it strictly, and §5d needs the strict form. This is
harmless.)

(f) **`ExpAlg`.** The G_m part is e^{y_j} ∈ ℚ̄, which is automatically nonzero. The E part is "z ∈ L (origin) or
(℘(z), ℘′(z)) ∈ ℚ̄²".
* Mathlib's ℘ is `∑' l, (1/(z−l)² − 1/l²)`, with the l = 0 term equal to 1/z² because `0⁻¹ = 0`. So off L it is the
  true ℘.
* `G n = ∑' l, (l^n)⁻¹` over the whole lattice, and its l = 0 term is 0, so G n is the usual Σ′. So `g₂ = 60 G₄` and
  `g₃ = 140 G₆` are the classical invariants.
* `derivWeierstrassP_sq` gives ℘′² = 4℘³ − g₂℘ − g₃ off L. So the E of the statement is exactly the curve uniformised
  by Mathlib's ℘.
* Junk values: ℘(l) = ℘′(l) = 0 for l ∈ L (`weierstrassP_coe`, `derivWeierstrassP_coe`, checked in `D0.lean`). These
  are algebraic, so the lattice disjunct is redundant but harmless. The junk can only make `ExpAlg` true at points
  where it is true anyway (the origin). ✔

(g) **Conclusion.** Here is why the connected algebraic subgroups of G_m^{d₁} × E are exactly T_ℒ × 0 and T_ℒ × E.
* Let H be connected and let T₁ be its image in the torus. If H ∩ (0 × E) were finite, Goursat would give an
  isogeny between a quotient torus of T₁ and E/finite, which is impossible.
* So either H ⊂ torus × 0, giving a subtorus, or H ⊃ 0 × E, giving H = T₁ × E.
* Lie T_ℒ = ℒ ⊗ ℂ in log coordinates, with ℒ ⊂ ℚ^{d₁}. Every such subgroup is defined over ℚ̄.

So "V contains a nonzero algebraic Lie subalgebra defined over ℚ̄" ⇔ ∃ ℒ, b with (ℒ ≠ ⊥ ∨ b) and
`tangentSub ℒ b ≤ V`. The proof's own endpoint (p. 395, "V ⊃ T_{G′}") confirms this reading. ✔

(h) **Maximality of d₀ and d₁.** G = G_m^{d₁} × E has no G_a factor, and Hom(E, G_m) = 0, so d₀ = 0, d₁ is maximal
and d₂ = 1. The quantity d₁ + 2d₂ = 2d − 2d₀ − d₁ decreases as d₁ grows, so the maximal d₁ is the strongest
legitimate choice. ✔

(i) **Arithmetic.** m > (d₁ + 2d₂ − κ)(d − 1 − t) becomes m > (d₁ + 2 − κ)(d₁ − t). Lean computes this in ℤ with
casts on each factor. Since κ ≤ dim Ω_ℚ = d₁ + 2 and t ≤ d₁, there are no sign surprises. ✔

(j) **Premises.** `IsAlgebraic ℚ L.g₂`, `IsAlgebraic ℚ L.g₃` ⇔ E is defined over ℚ̄. ✔

(k) **Not verified (scope).** W88 §5d derives (5.4) from Cor 5.3, i.e. Thm 4.1 with κ = rk(Y ∩ Ker exp), and from
Lemma 5.2. I checked the §5d deduction line by line, including Lemma 5.2's rank count with
rk Ω′ ≤ (d₁ + 2d₂) − (d₁′ + 2d₂′). It is correct given Thm 4.1.

The κ-term in Thm 4.1 itself (§6–7) was not reviewed. This matters: without κ, the instance in `main` fails
(6 > 6 is false). So the whole result rests on that κ-term.

Heuristic plausibility check (mine) on G_m × E, V = ℂ(2πi, ω), Y = ⟨period, u, v⟩:
* With rank 3 and κ = 1 the Siegel/Schwarz count closes: there are S² algebraic conditions but S³ analytic zeros,
  with L₁ = S^{3/2}, L₂ = S^{1/2}.
* Without the period, the same count needs rank 4.

This agrees with (5.4) and Cor 4.3, and periods saving cost in Schneider's method is a standard mechanism. Still,
**before publication, cross-check the κ version of Thm 4.1 against a second source or an expert.** This is the
single point of failure.

**Recommended doc fix:** say explicitly in `Waldschmidt.lean` that the instance depends on the κ-term of W88
Thm 4.1, whose proof is in §6–7, and that without κ the needed inequality is 6 > 6 (false).

## 2. Falsification attempts

* **d₁ = 0.** `Thm11Kappa L 0` is *provable* for every L, vacuously: V = ⊥ forces Y = 0, and then 0 > 0 is false.
  Done in `D0.lean`. So the d₁ = 0 instance creates no inconsistency.
* **d₁ = 1, V = ℂ(1, β).**
  - With V ℚ̄-rational, W = V: the condition is m > 0, and a period in V forces ω/π ∈ ℚ̄. That is false (Schneider),
    unless V is a coordinate line, and then the conclusion holds.
  - A non-period point gives a ℚ̄-linear relation among logarithms, and the conclusion is then Baker–Wüstholz.
  - With V generic, κ ≤ 1. This is consistent with the Schneider–Lang count (rank ≤ ρn = 2, including the period).
* **General V.** Write V = ker(λ·z + μw).
  - μ = 0 makes V ⊃ 0 × ℂ, so the conclusion holds.
  - Otherwise r ↦ 2πiλ·r is injective on ℚ^{d₁} (unless V contains a rational vector), and its preimage of ℚL has
    dimension ≤ 2. So κ ≤ 2 for every V where the conclusion fails.
  - So κ cannot be inflated: no "many periods" counterexample exists.
* **Encoding traps checked:**
  - ℚ vs ℤ (equivalent, 1(d));
  - lattice vs ℚ-span in `OmegaQ` (span of the lattice, correct);
  - Y ⊂ V (present);
  - coordinates over ℂ vs ℚ̄ (only W and the conclusion need ℚ̄, both correct);
  - `(ℒ ≠ ⊥ ∨ b = true)` (exactly "nonzero");
  - junk values (harmless, 1(f));
  - `finrank` of an infinite-dimensional module (cannot occur: every module involved is finite-dimensional).

  None gives a counterexample.
* **Converse risk.** I found no route to proving `¬ Thm11Kappa lemniscatic 4` in Lean. All the junk values are
  algebraic, and every degenerate V satisfies the conclusion.

## 3. The other hypotheses

* **`hg₂`: g₂(ϖℤ[i]) = 4. True.** mpmath at 50 digits, with τ = i, q = e^{−2π}:
  - G₄ = 2ζ(4)E₄(i)/ϖ⁴ gives g₂ = 60G₄ = 4.000…0 (50 digits);
  - a direct lattice sum (|a|, |b| ≤ 200) gives 3.99999 (truncation error);
  - g₃ = 140G₆ ≈ 2·10⁻⁵¹, i.e. 0.

  Mathlib's G is Σ′ l^{−k} (1(f)), so g₂ = 4 holds in Mathlib's normalisation, with
  `varpi = Γ(1/4)²/(2√(2π)) = 2.62205755429211981…`.
* **g₃ = 0** is now proved in Lean (`g₃_lemniscatic`, via l ↦ il). ✔
* **`hS`: ϖ/π ∉ ℚ. True.** ϖ/π = Γ(1/4)²/(2√2·π^{3/2}) = 0.834626841674073…, and it is transcendental. Chudnovsky
  (1976, π and Γ(1/4) algebraically independent) certainly suffices, as does Nesterenko (1996).

  **Doc fix:** the docstrings attribute this to "Schneider 1937". Either check that attribution (Schneider's 1937
  results concern ω, η and their combinations) or cite Chudnovsky.

## 4. The proof's use of the hypothesis (`main`, `two_three`)

**Argument.** The setting is G = G_m⁴ × E (d = 5) and V = ker φ, with φ = z₂ + iz₃ + w − t(z₀ + iz₁) and
t = (p + qi)ϖ/(Dπ). I checked the following by hand, independently of Lean.
* The period vectors lie in V: t·2πiD = 2i(p + qi)ϖ, which is matched by the E-coordinates (−2q + 2pi)ϖ and
  (−2p − 2qi)ϖ.
* The four data vectors lie in V. Their E-coordinates are 0, so they do not use E at all; only the periods do.
* W = span of the three vectors in `wv` is 3-dimensional, algebraic and contained in V.
* κ ≥ 1, in fact κ = 2: both period vectors lie in Y ∩ Ω_ℚ. So 6 > (6 − κ)·1 holds. (Five generators would already
  suffice.)
* Endpoint b = true: φ(0, 1) = 1 ≠ 0.
* Endpoint b = false: a rational l ≠ 0 with l₂ + il₃ = t(l₀ + il₁) gives ϖ/π ∈ ℚ, by taking real and imaginary parts
  with u, v as in `key_contra`.

The argument is correct. `two_three` instantiates c = 1, a = log 2, b = log 3, and uses the principal branch
`exp((ϖ/π)·log 2)`. ✔

**Scope gap (fixable): CORRECT WITH FIX.** `main` assumes `LinearIndependent ℚ ![2πi, a, b]`, while `FourExpAt`
assumes only that a and b are ℚ-independent. So as stated, `main` is strictly weaker than `FourExpAt (cϖ/π)`.

The 2πi assumption is used only for the ℚ-independence of the six generators, and it is not needed there. The two
period vectors have E-coordinates (−2q + 2pi)ϖ and (−2p − 2qi)ϖ.
* Their real and imaginary parts give the linear system with determinant 4(p² + q²) ≠ 0. So g₀ = g₁ = 0.
* The G_m-coordinates 0 and 1 then give g₂a + g₄b = 0 and g₃a + g₅b = 0. So everything vanishes once a and b are
  ℚ-independent.

If 2πi ∈ ℚa + ℚb, κ only grows, which helps.

Verified in Lean (`Strong.lean`, axioms propext/choice/Quot.sound):
* `yv_linearIndependent'`: (p, q) ≠ 0 and a, b ℚ-independent imply the six generators are ℚ-independent;
* `main'`: `main` with `hind : LinearIndependent ℚ ![a, b]`; the proof is otherwise verbatim;
* `fourExpAt_Qi : … → FourExpAt (tExp p q D)`.

**Recommended:** adopt `main'` and `fourExpAt_Qi`. Then the conditional result is literally
`Target.fourExp_varpi_div_pi` restricted to c ∈ ℚ(i)ˣ. Also update the MainQi docstring, which still mentions 2πi.

## Concrete fixes (summary)

1. Replace `hind` in `main` by `LinearIndependent ℚ ![a, b]` (proof in `Strong.lean`), and add the corollary
   `FourExpAt (tExp p q D)`.
2. Doc: state the dependence on W88's κ-term in Thm 4.1 (§6–7) as the single point of failure, and get an expert or
   second-source check of it.
3. Doc: fix the attribution for "ϖ/π transcendental" (Chudnovsky 1976 / Nesterenko 1996), or check Schneider 1937.
4. README.md still says "scaffolding" and does not mention the conditional theorems in MainQi and TwoThree. Update it.
5. Optional: drop the redundant `y.2 ∈ L.lattice ∨` disjunct, or keep it with a comment that the junk values are 0.
