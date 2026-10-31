/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Basis

/-!
# CM lattices `ω ℤ[α]` with a conjugate-eigen quasi-period

A `CMLattice` records a period pair `L = (ω, αω)` with `α` imaginary quadratic (`α² = p + qα`, `p, q ∈ ℚ`), and a number
`η₀` meant to be the conjugate-eigen quasi-period `η*(ω)`, so that `η*((m + nα)ω) = (m + nᾱ) η₀`. The only property
used in the proofs is Legendre's relation in the form `ω η₀ (α − ᾱ) = 2πi`. With `Im α > 0` this relation forces
`η₀ = η*(ω)` (for `Im α < 0` it would force `−η*(ω)`, hence the sign condition `him`). That `η₀` is the true quasi-period is a
soundness fact of the group models built from it (stated, with the instances, in `CM4E/Gen/Instances.lean`).
-/

open Complex

namespace CM4E.Gen

/-- A CM lattice `ω ℤ[α]` with quasi-period `η₀`. -/
structure CMLattice where
  /-- the period pair `(ω, αω)` -/
  pp : PeriodPair
  ω : ℂ
  α : ℂ
  η₀ : ℂ
  p : ℚ
  q : ℚ
  hω₁ : pp.ω₁ = ω
  hω₂ : pp.ω₂ = α * ω
  hquad : α ^ 2 = p + q * α
  him : 0 < α.im
  legendre : ω * η₀ * (α - starRingEnd ℂ α) = 2 * Real.pi * I

namespace CMLattice

variable (L : CMLattice)

lemma ω_ne_zero : L.ω ≠ 0 := by
  intro h
  have := L.legendre
  rw [h, zero_mul, zero_mul] at this
  exact (by simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * (Real.pi : ℂ) * I) ≠ 0) this.symm

lemma conj_α : starRingEnd ℂ L.α = L.q - L.α := by
  have h1 := L.hquad
  have h2 : (starRingEnd ℂ L.α) ^ 2 = L.p + L.q * starRingEnd ℂ L.α := by
    have := congrArg (starRingEnd ℂ) h1
    simpa [map_pow, map_add, map_mul, Complex.conj_ofReal] using this
  have hne : L.α - starRingEnd ℂ L.α ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [Complex.conj_im] at this
    linarith [L.him]
  have : (L.α - starRingEnd ℂ L.α) * (L.α + starRingEnd ℂ L.α - L.q) = 0 := by
    linear_combination h1 - h2
  have h3 := (mul_eq_zero.mp this).resolve_left hne
  linear_combination h3

lemma isAlgebraic_α : IsAlgebraic ℚ L.α := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C L.q * Polynomial.X - Polynomial.C L.p, ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_X, Polynomial.coeff_C] at this
  · simp [L.hquad]

/-- `α K ⊂ K` for an adapted basis. -/
lemma α_mul_mem {r : ℕ} {b : Fin r → ℂ} {x : ℂ} (hx : x ∈ Kspan L.α b) : L.α * x ∈ Kspan L.α b := by
  have hgen : ∀ p, L.α * theta L.α b p ∈ Kspan L.α b := by
    rintro ⟨j, k⟩
    fin_cases k
    · exact Submodule.subset_span ⟨(j, 1), by simp [theta]⟩
    · show L.α * theta L.α b (j, 1) ∈ Kspan L.α b
      have : L.α * theta L.α b (j, 1) = (L.p : ℚ) • theta L.α b (j, 0) + (L.q : ℚ) • theta L.α b (j, 1) := by
        simp only [theta, Rat.smul_def]; simp
        linear_combination (b j) * L.hquad
      rw [this]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  refine Submodule.span_induction (fun y ⟨p, hp⟩ => hp ▸ hgen p) (by simp) (fun y z _ _ hy hz => ?_)
    (fun c y _ hy => ?_) hx
  · rw [mul_add]; exact add_mem hy hz
  · rw [Rat.smul_def, mul_left_comm, ← Rat.smul_def]; exact Submodule.smul_mem _ _ hy

lemma α_mem {r : ℕ} {b : Fin r → ℂ} (hb : IsAdaptedFieldBasis L.α b) : L.α ∈ Kspan L.α b := by
  simpa using L.α_mul_mem hb.one_mem

lemma conj_α_mem {r : ℕ} {b : Fin r → ℂ} (hb : IsAdaptedFieldBasis L.α b) :
    starRingEnd ℂ L.α ∈ Kspan L.α b := by
  rw [L.conj_α]
  refine sub_mem ?_ (L.α_mem hb)
  have := Submodule.smul_mem _ L.q hb.one_mem
  simpa [Rat.smul_def] using this

end CMLattice

lemma theta_isAlgebraic {α : ℂ} (hα : IsAlgebraic ℚ α) {r : ℕ} {b : Fin r → ℂ}
    (hb : ∀ j, IsAlgebraic ℚ (b j)) (p : Fin r × Fin 2) : IsAlgebraic ℚ (theta α b p) := by
  unfold theta; split_ifs
  · exact hb _
  · exact hα.mul (hb _)

/-- Coordinates in the basis `θ`. -/
lemma exists_coords {α : ℂ} {r : ℕ} {b : Fin r → ℂ} {x : ℂ} (hx : x ∈ Kspan α b) :
    ∃ m : Fin r × Fin 2 → ℚ, ∑ j, (m j : ℂ) * theta α b j = x := by
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  exact ⟨m, by simpa [Rat.smul_def] using hm⟩

end CM4E.Gen
