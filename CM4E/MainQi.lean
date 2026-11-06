/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs
import CM4E.Waldschmidt
import CM4E.Lattice
import CM4E.Common

/-!
# Conditional main theorem: four exponentials at `t = c ϖ / π`, `c ∈ ℚ(i)`

**Theorem** (`CM4E.MainQi.main`). Assume
* (H1) Waldschmidt's κ-refined hyperplane theorem for `G_m⁴ × E`, with `E` the curve of the lattice `ϖℤ[i]`
  (`Thm11Kappa lemniscatic 4`, a published theorem, stated in `CM4E/Waldschmidt.lean`);
* (H2) the invariant `g₂` of `ϖℤ[i]` is algebraic (true: `g₂ = 4`; `g₃ = 0` is proved in `CM4E/Lattice.lean`);
* (H3) `ϖ/π` is irrational (Schneider's theorem; H2 and H3 are proved in `lean_lsg` and discharged in
  `CM4E/Final.lean`).

Let `c = (p + qi)/D ≠ 0`, `t = cϖ/π`, and let `a, b` be `ℚ`-linearly independent logarithms of algebraic numbers.
Then `e^{ta}` and `e^{tb}` are not both algebraic (`main`); i.e. `FourExpAt (cϖ/π)` (`fourExpAt_Qi`).

This is Theorem MG of the paper for `K = ℚ(i)` (`n = 2`), via W88 §5d.
* Take `G = G_m⁴ × E` (`d = 5`), `Ψ''(t, z) = (t₀ + it₁, t₂ + it₃ + z)` and `V = Ψ''⁻¹(ℂ(1, t))`, a hyperplane.
* `W ⊂ ker Ψ''` has dimension 3.
* `Y` is spanned by six vectors: two periods (lifts of `D(2πi, 2icϖ)` and its `i`-multiple) and four
  data vectors (lifts of `(a, ta)`, `(b, tb)` and their `i`-multiples).
* (5.4) reads `6 > (4 + 2 − κ)·1`, which holds since `κ ≥ 1` (in fact `κ = 2`).
* A nonzero algebraic Lie subalgebra of `V` would force `t ∈ ℚ(i)`, hence `ϖ/π ∈ ℚ`.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.MainQi

/-- The exponent `t = c ϖ / π` with `c = (p + qi)/D`. -/
noncomputable def tExp (p q : ℤ) (D : ℕ) : ℂ := ((p + q * I) / D) * varpi / Real.pi

/-- The linear form `t₂ + i t₃ + z − s (t₀ + i t₁)`; its kernel is `V = Ψ''⁻¹(ℂ(1, s))`. -/
noncomputable def phi (s : ℂ) : T 4 →ₗ[ℂ] ℂ where
  toFun v := v.1 2 + I * v.1 3 + v.2 - s * (v.1 0 + I * v.1 1)
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma phi_apply (s : ℂ) (v : T 4) :
    phi s v = v.1 2 + I * v.1 3 + v.2 - s * (v.1 0 + I * v.1 1) := rfl

lemma finrank_ker_phi (s : ℂ) : finrank ℂ (LinearMap.ker (phi s)) = 4 := by
  have hsurj : Function.Surjective (phi s) := fun w => ⟨(0, w), by simp [phi_apply]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (phi s)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
  have h5 : finrank ℂ (T 4) = 5 := by simp [T, Module.finrank_prod]
  omega

/-- Three algebraic vectors spanning (a part of) `ker Ψ''`. -/
noncomputable def wv : Fin 3 → T 4 :=
  ![(![-I, 1, 0, 0], 0), (![0, 0, -I, 1], 0), (![0, 0, -1, 0], 1)]

lemma wv_linearIndependent : LinearIndependent ℂ wv := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 := congrArg (fun v : T 4 => v.1 1) hg
  have h3 := congrArg (fun v : T 4 => v.1 3) hg
  have h4 := congrArg (fun v : T 4 => v.2) hg
  simp [Fin.sum_univ_three, wv] at h1 h3 h4
  intro i
  fin_cases i <;> simp_all

lemma finrank_W : finrank ℂ (Submodule.span ℂ (Set.range wv)) = 3 := by
  rw [finrank_span_eq_card wv_linearIndependent]; simp

lemma W_le_V (s : ℂ) : Submodule.span ℂ (Set.range wv) ≤ LinearMap.ker (phi s) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [wv, phi_apply]

lemma W_rational : (gmE lemniscatic 4).Rational (Submodule.span ℂ (Set.range wv)) := by
  refine ⟨Set.range wv, ?_, rfl⟩
  rintro _ ⟨i, rfl⟩
  have hnI : IsAlgebraic ℚ (-I) := isAlgebraic_I.neg
  fin_cases i <;>
    refine ⟨fun j => ?_, ?_⟩ <;> (try fin_cases j) <;>
    simp [wv, hnI, isAlgebraic_zero, isAlgebraic_one, isAlgebraic_one.neg]

/-! ### The six data vectors -/

/-- The period `2πi D` (a lattice multiple of `2πi`). -/
noncomputable def per (D : ℕ) : ℂ := 2 * Real.pi * I * D

/-- The six generators of `Y`: two periods and four data vectors. -/
noncomputable def yv (p q : ℤ) (D : ℕ) (a b : ℂ) : Fin 6 → T 4 :=
  let t := tExp p q D
  ![(![per D, 0, 0, 0], (((-2 * q : ℤ) : ℂ) + ((2 * p : ℤ) : ℂ) * I) * varpi),
    (![0, per D, 0, 0], (((-2 * p : ℤ) : ℂ) + ((-2 * q : ℤ) : ℂ) * I) * varpi),
    (![a, 0, t * a, 0], 0), (![0, a, 0, t * a], 0),
    (![b, 0, t * b, 0], 0), (![0, b, 0, t * b], 0)]

lemma yv_mem_V (p q : ℤ) (D : ℕ) (hD : 0 < D) (a b : ℂ) (i : Fin 6) :
    yv p q D a b i ∈ LinearMap.ker (phi (tExp p q D)) := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hpi := pi_ne_zero'
  rw [LinearMap.mem_ker, phi_apply]
  fin_cases i <;> simp [yv, tExp, per] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]

lemma exp_per (D : ℕ) : Complex.exp (per D) = 1 := by
  rw [per, show (2 * (Real.pi : ℂ) * I * D) = D * (2 * Real.pi * I) by ring]
  exact Complex.exp_nat_mul_two_pi_mul_I D

lemma yv_expAlg (p q : ℤ) (D : ℕ) (a b : ℂ) (ha : a ∈ logAlg) (hb : b ∈ logAlg)
    (hta : IsAlgebraic ℚ (Complex.exp (tExp p q D * a)))
    (htb : IsAlgebraic ℚ (Complex.exp (tExp p q D * b))) (i : Fin 6) :
    ExpAlg lemniscatic (yv p q D a b i) := by
  have h1 : IsAlgebraic ℚ (1 : ℂ) := isAlgebraic_one
  have hz1 := gaussian_mem_lattice (-2 * q) (2 * p)
  have hz2 := gaussian_mem_lattice (-2 * p) (-2 * q)
  push_cast at hz1 hz2
  fin_cases i <;> refine ⟨fun j => ?_, Or.inl ?_⟩ <;> (try fin_cases j) <;>
    simp [yv, exp_per, h1, hta, htb] <;>
    first
    | exact ha
    | exact hb
    | (convert hz1 using 2; ring1)
    | (convert hz2 using 2; ring1)

/-! ### Rank and period rank of `Y` -/

/-- The first generator is a period: it lies in `Ω_ℚ`. -/
lemma yv0_mem_Omega (p q : ℤ) (D : ℕ) (a b : ℂ) : yv p q D a b 0 ∈ OmegaQ lemniscatic 4 := by
  have hdecomp : yv p q D a b 0 =
      (D : ℚ) • ((Pi.single 0 (2 * Real.pi * I) : Fin 4 → ℂ), (0 : ℂ)) +
        ((0 : Fin 4 → ℂ), (((-2 * q : ℤ) : ℂ) + ((2 * p : ℤ) : ℂ) * I) * varpi) := by
    refine Prod.ext ?_ ?_
    · funext j; fin_cases j <;> simp [yv, per, Rat.smul_def] ; ring
    · simp [yv]
  rw [hdecomp]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨0, rfl⟩)))
    (Submodule.subset_span (Or.inr ⟨_, gaussian_mem_lattice _ _, rfl⟩))

/-! ### The final contradiction: a rational vector in `V` forces `ϖ/π ∈ ℚ` -/

lemma tExp_eq (p q : ℤ) (D : ℕ) :
    tExp p q D = ((p : ℂ) + q * I) / D * ((varpi / Real.pi : ℝ) : ℂ) := by
  simp only [tExp]; push_cast; ring

lemma key_contra (hS : Irrational (varpi / Real.pi)) (p q : ℤ) (D : ℕ) (hD : 0 < D)
    (hpq : p ≠ 0 ∨ q ≠ 0) (l : Fin 4 → ℚ) (hl0 : l ≠ 0)
    (h : ((l 2 : ℚ) : ℂ) + I * ((l 3 : ℚ) : ℂ) + 0 -
      tExp p q D * (((l 0 : ℚ) : ℂ) + I * ((l 1 : ℚ) : ℂ)) = 0) : False := by
  set x : ℝ := varpi / Real.pi with hxdef
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have h' : (((l 2 : ℚ) : ℂ) + I * ((l 3 : ℚ) : ℂ)) * D =
      (x : ℂ) * (((p : ℂ) + q * I) * (((l 0 : ℚ) : ℂ) + I * ((l 1 : ℚ) : ℂ))) := by
    rw [tExp_eq] at h
    field_simp at h
    linear_combination h
  have hre := congrArg Complex.re h'
  have him := congrArg Complex.im h'
  simp [Complex.mul_re, Complex.mul_im] at hre him
  -- hre : l2 * D = x * (p * l0 - q * l1),  him : l3 * D = x * (p * l1 + q * l0)  (as reals)
  set u : ℚ := p * l 0 - q * l 1 with hu
  set v : ℚ := p * l 1 + q * l 0 with hv
  have hre' : ((l 2 * D : ℚ) : ℝ) = x * (u : ℝ) := by push_cast [hu]; linarith
  have him' : ((l 3 * D : ℚ) : ℝ) = x * (v : ℝ) := by push_cast [hv]; linarith
  by_cases hu0 : u = 0
  · by_cases hv0 : v = 0
    · -- then `l = 0`
      have hD'' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
      have h2 : l 2 = 0 := by
        have : ((l 2 * D : ℚ) : ℝ) = 0 := by rw [hre', hu0]; simp
        have : l 2 * D = 0 := by exact_mod_cast this
        simpa [hD''] using this
      have h3 : l 3 = 0 := by
        have : ((l 3 * D : ℚ) : ℝ) = 0 := by rw [him', hv0]; simp
        have : l 3 * D = 0 := by exact_mod_cast this
        simpa [hD''] using this
      have hpq2 : ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) ≠ 0 := by
        rcases hpq with hp | hq
        · have : (0 : ℚ) < (p : ℚ) ^ 2 := by positivity
          positivity
        · have : (0 : ℚ) < (q : ℚ) ^ 2 := by positivity
          positivity
      have h0 : l 0 = 0 := by
        have : ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * l 0 = p * u + q * v := by rw [hu, hv]; ring
        rw [hu0, hv0] at this
        simpa [hpq2] using this
      have h1 : l 1 = 0 := by
        have : ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * l 1 = p * v - q * u := by rw [hu, hv]; ring
        rw [hu0, hv0] at this
        simpa [hpq2] using this
      exact hl0 (by funext j; fin_cases j <;> simp [h0, h1, h2, h3])
    · exact hS ⟨l 3 * D / v, by
        rw [show ((l 3 * D / v : ℚ) : ℝ) = ((l 3 * D : ℚ) : ℝ) / (v : ℝ) by push_cast; ring, him']
        field_simp [show (v : ℝ) ≠ 0 by exact_mod_cast hv0]⟩
  · exact hS ⟨l 2 * D / u, by
      rw [show ((l 2 * D / u : ℚ) : ℝ) = ((l 2 * D : ℚ) : ℝ) / (u : ℝ) by push_cast; ring, hre']
      field_simp [show (u : ℝ) ≠ 0 by exact_mod_cast hu0]⟩

/-! ### The conditional main theorem -/

/-- The six generators are ℚ-independent as soon as `a, b` are (2πi not needed). -/
lemma yv_linearIndependent_ab (p q : ℤ) (D : ℕ) (hpq : p ≠ 0 ∨ q ≠ 0) (a b : ℂ)
    (hind : LinearIndependent ℚ ![a, b]) :
    LinearIndependent ℚ (yv p q D a b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hli := Fintype.linearIndependent_iff.mp hind
  have h0 := congrArg (fun v : T 4 => v.1 0) hg
  have h1 := congrArg (fun v : T 4 => v.1 1) hg
  have hE := congrArg (fun v : T 4 => v.2) hg
  simp [Fin.sum_univ_succ, yv, per, Rat.smul_def] at h0 h1 hE
  have hv := varpi_ne_zero'
  have hE' : ((g 0 : ℂ) * ((-2 * q : ℂ) + 2 * p * I) + (g 1 : ℂ) * ((-2 * p : ℂ) + (-2 * q) * I)) = 0 := by
    have : ((g 0 : ℂ) * ((-2 * q : ℂ) + 2 * p * I) + (g 1 : ℂ) * ((-2 * p : ℂ) + (-2 * q) * I)) * varpi = 0 := by
      linear_combination hE
    simpa [hv] using this
  have hre := congrArg Complex.re hE'
  have him := congrArg Complex.im hE'
  simp at hre him
  have hre' : (g 0 : ℝ) * q + (g 1 : ℝ) * p = 0 := by linarith
  have him' : (g 0 : ℝ) * p - (g 1 : ℝ) * q = 0 := by linarith
  have hpq2 : (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ≠ 0 := by
    rcases hpq with hp | hq
    · have : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      positivity
    · have : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      positivity
  have g0 : g 0 = 0 := by
    have : ((g 0 : ℝ)) * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) = 0 := by linear_combination q * hre' + p * him'
    have : (g 0 : ℝ) = 0 := by simpa [hpq2] using this
    exact_mod_cast this
  have g1 : g 1 = 0 := by
    have : ((g 1 : ℝ)) * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) = 0 := by linear_combination p * hre' - q * him'
    have : (g 1 : ℝ) = 0 := by simpa [hpq2] using this
    exact_mod_cast this
  rw [g0] at h0; rw [g1] at h1
  have e0 := hli ![g 2, g 4] (by simp [Fin.sum_univ_succ, Rat.smul_def]; linear_combination h0)
  have e1 := hli ![g 3, g 5] (by simp [Fin.sum_univ_succ, Rat.smul_def]; linear_combination h1)
  have a0 := e0 0; have a1 := e0 1; have b0 := e1 0; have b1 := e1 1
  simp at a0 a1 b0 b1
  intro i
  fin_cases i <;> simp [g0, g1, a0, a1, b0, b1]

/-- **Conditional main theorem** (four exponentials at `t = cϖ/π`, `c = (p + qi)/D ≠ 0`). Hypotheses:
Waldschmidt's κ-refined hyperplane theorem on `G_m⁴ × E` (`hW`), the algebraicity of `g₂` for `ϖℤ[i]` (`hg₂`;
`g₃ = 0` is proved, `g₃_lemniscatic`), and the irrationality of `ϖ/π` (`hS`). Only `ℚ`-independence of `a, b` is
assumed: the two period vectors are already independent through their `E`-coordinates (observation and proof of
reviews/REFEREE_HYP.md). -/
theorem main (hW : Thm11Kappa lemniscatic 4)
    (hg₂ : IsAlgebraic ℚ lemniscatic.g₂) (hS : Irrational (varpi / Real.pi))
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0)
    (a b : ℂ) (ha : a ∈ logAlg) (hb : b ∈ logAlg)
    (hind : LinearIndependent ℚ ![a, b]) :
    ¬ (IsAlgebraic ℚ (Complex.exp (tExp p q D * a)) ∧
        IsAlgebraic ℚ (Complex.exp (tExp p q D * b))) := by
  rintro ⟨hta, htb⟩
  have hliY := yv_linearIndependent_ab p q D hpq a b hind
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range (yv p q D a b))) = 6 := by
    rw [finrank_span_eq_card hliY]; simp
  have : FiniteDimensional ℚ (Submodule.span ℚ (Set.range (yv p q D a b))) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hk_pos : 1 ≤ finrank ℚ ↥(Submodule.span ℚ (Set.range (yv p q D a b)) ⊓ OmegaQ lemniscatic 4) := by
    have hmem : yv p q D a b 0 ∈ Submodule.span ℚ (Set.range (yv p q D a b)) ⊓ OmegaQ lemniscatic 4 :=
      ⟨Submodule.subset_span ⟨0, rfl⟩, yv0_mem_Omega p q D a b⟩
    have hne : yv p q D a b 0 ≠ 0 := by
      intro h0
      have := congrArg (fun v : T 4 => v.1 0) h0
      simp [yv, per, Real.pi_ne_zero, hD.ne'] at this
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    rw [h0] at hmem
    exact hne (by simpa using hmem)
  have hT5 : finrank ℂ (T 4) = 5 := by simp [T, Module.finrank_prod]
  obtain ⟨S, ⟨ℒ, bb, rfl⟩, hne, hle⟩ := hW hg₂ g₃_lemniscatic_isAlgebraic (LinearMap.ker (phi (tExp p q D)))
    (Submodule.span ℂ (Set.range wv)) 6 (yv p q D a b) (by rw [finrank_ker_phi, hT5]) (W_le_V _) W_rational
    (fun i => ⟨yv_mem_V p q D hD a b i, yv_expAlg p q D a b ha hb hta htb i⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range (yv p q D a b))) : ℤ) >
        ((4 : ℤ) + 2 * 1 - finrank ℚ ↥(Submodule.span ℚ (Set.range (yv p q D a b)) ⊓ OmegaQ lemniscatic 4)) *
          ((finrank ℂ (T 4) : ℤ) - 1 - finrank ℂ (Submodule.span ℂ (Set.range wv))))
      rw [hfinY, finrank_W, hT5]; push_cast; omega)
  cases bb with
  | true =>
    have hmem : ((0 : Fin 4 → ℂ), (1 : ℂ)) ∈ tangentSub ℒ true := by
      rw [tangentSub, Submodule.mem_prod]
      exact ⟨Submodule.zero_mem _, by simp⟩
    have := hle hmem
    simp [LinearMap.mem_ker, phi_apply] at this
  | false =>
    have hℒ : ℒ ≠ ⊥ := by
      rintro rfl; exact hne tangentSub_bot_false
    obtain ⟨l, hl, hl0⟩ := Submodule.ne_bot_iff _ |>.mp hℒ
    have hmem : ((fun j => ((l j : ℚ) : ℂ)), (0 : ℂ)) ∈ tangentSub ℒ false := by
      rw [tangentSub, Submodule.mem_prod]
      exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, by simp⟩
    have hV := hle hmem
    rw [LinearMap.mem_ker, phi_apply] at hV
    exact key_contra hS p q D hD hpq l hl0 hV


/-- **Theorem 1(b) for `c ∈ ℚ(i)ˣ`, conditional:** `FourExpAt (c ϖ / π)` with `c = (p + qi)/D`. -/
theorem fourExpAt_Qi (hW : Thm11Kappa lemniscatic 4)
    (hg₂ : IsAlgebraic ℚ lemniscatic.g₂) (hS : Irrational (varpi / Real.pi))
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (tExp p q D) :=
  fun a b ha hb hind => main hW hg₂ hS p q D hD hpq a b ha hb hind

end CM4E.MainQi
