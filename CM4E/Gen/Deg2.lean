/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MXP

/-!
# The degree-two period statements (paper [I], Corollary `cor:deg2`)

(ii) `1, ϖ, Ω_ρ, ϖΩ_ρ/π` are linearly independent over `ℚ̄`. It follows from Theorem MX (`K`-form, `CM4E.Gen.mx_K`)
applied to `X = (ϖ, η_i + t) ∈ Λ(E_i^♮)`, `Y = 0`, together with the `ℚ̄`-independence of `1, π, ϖ, η_i, Ω_ρ, η_ρ`
(Wüstholz's analytic subgroup theorem on `E_i^♮ × E_ρ^♮ × G_m × G_a`), a named input.

(i) `π, ϖ, Ω_ρ, ϖΩ_ρ` are linearly independent over `ℚ̄`. It follows from Proposition D′ (`CM4E.Gen.mxP_K`).
If the `π`-coefficient `c₀` is nonzero, take `β = −c₃/c₀`, `X = (ϖ, π/ϖ)`, `Y = 0`. If `c₀ = 0` and `c₃ ≠ 0`, take
`β = √3/2`, `X = (ϖ, π/ϖ)`, `Y = (Ω_ρ, η_ρ)`. The paper's proof of (i) treats only the first case; the second is an
addition here.
-/

open Complex Module CM4E.Waldschmidt CM4E.MX

namespace CM4E.Gen

/-- **Named input (Wüstholz 1989).** `1, π, ϖ, η_i = π/ϖ, Ω_ρ, η_ρ` are linearly independent over `ℚ̄`. -/
def WuestholzSix : Prop :=
  ∀ c : Fin 6 → ℂ, (∀ k, IsAlgebraic ℚ (c k)) →
    c 0 + c 1 * Real.pi + c 2 * varpi + c 3 * (Real.pi / varpi) + c 4 * omegaRho + c 5 * etaRho = 0 →
    ∀ k, c k = 0

lemma six_zero (h6 : WuestholzSix) (c0 c1 c2 c3 c4 c5 : ℂ) (h0 : IsAlgebraic ℚ c0) (h1 : IsAlgebraic ℚ c1)
    (h2 : IsAlgebraic ℚ c2) (h3 : IsAlgebraic ℚ c3) (h4 : IsAlgebraic ℚ c4) (h5 : IsAlgebraic ℚ c5)
    (h : c0 + c1 * Real.pi + c2 * varpi + c3 * (Real.pi / varpi) + c4 * omegaRho + c5 * etaRho = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 := by
  have := h6 ![c0, c1, c2, c3, c4, c5] (by intro k; fin_cases k <;> assumption) (by simpa using h)
  exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2, by simpa using this 3,
    by simpa using this 4, by simpa using this 5⟩

/-- **Corollary deg2 (ii)**: `1, ϖ, Ω_ρ, ϖΩ_ρ/π` are linearly independent over `ℚ̄`. -/
theorem deg2_ii (hW : Thm11KappaMXG) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (h6 : WuestholzSix)
    (c0 c1 c2 c3 : ℂ) (h0 : IsAlgebraic ℚ c0) (h1 : IsAlgebraic ℚ c1) (h2 : IsAlgebraic ℚ c2)
    (h3 : IsAlgebraic ℚ c3)
    (hrel : c0 + c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho / Real.pi) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have hv := varpi_ne_zero'
  have hO := omegaRho_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr := r3_ne_zero
  have hη : etaRho * omegaRho = 2 * r3 * Real.pi / 3 := etaRho_mul
  have hr3 := r3_sq
  have hM : Transcendental ℚ ((omegaRho : ℂ) / varpi) := by
    intro halg
    obtain ⟨-, -, -, -, h4, -⟩ := six_zero h6 0 0 (-((omegaRho : ℂ) / varpi)) 0 1 0 isAlgebraic_zero
      isAlgebraic_zero halg.neg isAlgebraic_zero isAlgebraic_one isAlgebraic_zero (by field_simp; ring)
    exact one_ne_zero h4
  by_cases hc3 : c3 = 0
  · subst hc3
    obtain ⟨e0, -, e2, -, e4, -⟩ := six_zero h6 c0 0 c1 0 c2 0 h0 isAlgebraic_zero h1 isAlgebraic_zero h2
      isAlgebraic_zero (by linear_combination hrel)
    exact ⟨e0, e2, e4, rfl⟩
  · exfalso
    -- `ϖΩ/π = a + bϖ + cΩ`
    set a := -c0 / c3
    set b := -c1 / c3
    set c := -c2 / c3
    have ha : IsAlgebraic ℚ a := by simp only [a, div_eq_mul_inv]; exact h0.neg.mul h3.inv
    have hb : IsAlgebraic ℚ b := by simp only [b, div_eq_mul_inv]; exact h1.neg.mul h3.inv
    have hc : IsAlgebraic ℚ c := by simp only [c, div_eq_mul_inv]; exact h2.neg.mul h3.inv
    have hrelπ : c0 * Real.pi + c1 * varpi * Real.pi + c2 * omegaRho * Real.pi + c3 * (varpi * omegaRho) = 0 := by
      have e : c3 * (varpi * omegaRho / Real.pi) * Real.pi = c3 * (varpi * omegaRho) := by field_simp
      linear_combination (Real.pi : ℂ) * hrel - e
    have hrel' : (varpi : ℂ) * omegaRho / Real.pi = a + b * varpi + c * omegaRho := by
      rw [div_eq_iff hpi]; simp only [a, b, c]; field_simp
      linear_combination hrelπ
    by_cases hc0 : c = 0
    · -- `Ω = a η_i + b π`
      rw [hc0, zero_mul, add_zero] at hrel'
      have : (1 : ℂ) * omegaRho + (-b) * Real.pi + (-a) * (Real.pi / varpi) = 0 := by
        field_simp at hrel' ⊢; linear_combination hrel'
      obtain ⟨-, -, -, -, e4, -⟩ := six_zero h6 0 (-b) 0 (-a) 1 0 isAlgebraic_zero hb.neg isAlgebraic_zero
        ha.neg isAlgebraic_one isAlgebraic_zero (by linear_combination this)
      exact one_ne_zero e4
    by_cases hb0 : b = 0
    · -- `(2/√3) ϖ = a η_ρ + (2c/√3) π`
      rw [hb0, zero_mul, add_zero] at hrel'
      have e : (varpi : ℂ) * (2 * r3 / 3) = a * etaRho + c * (2 * r3 / 3) * Real.pi := by
        have := congrArg (· * etaRho) hrel'
        have e1 : (varpi : ℂ) * omegaRho / Real.pi * etaRho = varpi * (2 * r3 / 3) := by
          rw [div_mul_eq_mul_div, mul_assoc, mul_comm (omegaRho : ℂ), hη]; field_simp
        rw [e1, add_mul, mul_assoc c, mul_comm (omegaRho : ℂ), hη] at this
        linear_combination this
      have halg23 : IsAlgebraic ℚ (2 * r3 / 3) := by
        rw [← mem_algebraicClosure_iff]
        exact div_mem (mul_mem (by simp) (mem_algebraicClosure_iff.mpr isAlgebraic_r3)) (by simp)
      have h23 : (2 * r3 / 3 : ℂ) ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hr) three_ne_zero
      obtain ⟨-, -, e2, -, -, -⟩ := six_zero h6 0 (-(c * (2 * r3 / 3))) (2 * r3 / 3) 0 0 (-a)
        isAlgebraic_zero (hc.mul halg23).neg halg23 isAlgebraic_zero isAlgebraic_zero ha.neg
        (by linear_combination e)
      exact h23 e2
    -- the main case: Theorem MX at `X = (ϖ, η_i + t)`
    set t := -1 / c
    set β := -(r3 * b) / (2 * c)
    set a₁ := a / b
    have ht : IsAlgebraic ℚ t := by simp only [t, div_eq_mul_inv]; exact isAlgebraic_one.neg.mul hc.inv
    have hβ : IsAlgebraic ℚ β := by
      rw [← mem_algebraicClosure_iff]
      exact div_mem (neg_mem (mul_mem (mem_algebraicClosure_iff.mpr isAlgebraic_r3)
        (mem_algebraicClosure_iff.mpr hb))) (mul_mem (by simp) (mem_algebraicClosure_iff.mpr hc))
    have hβ0 : β ≠ 0 := div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hr hb0)) (mul_ne_zero two_ne_zero hc0)
    have ha₁ : IsAlgebraic ℚ a₁ := by simp only [a₁, div_eq_mul_inv]; exact ha.mul hb.inv
    have hX : LogNat lemniscatic etaLem varpi (Real.pi / varpi + t) :=
      Or.inl ⟨1, 0, by simp [lemniscatic], by
        have : Real.pi / varpi + t - etaLem 1 0 = t := by simp [etaLem]
        rw [this]; exact ht⟩
    have hY : LogNat equianharmonic etaR 0 0 :=
      Or.inl ⟨0, 0, by simp, isAlg_zero_of (by simp [etaR])⟩
    have hrelX : (varpi + 0 + a₁) * (β * etaRho) = (Real.pi / varpi + t + 0 + 0) * varpi := by
      have e : (varpi + 0 + a₁) * (β * etaRho) = -((b * varpi + a) * Real.pi) / (c * omegaRho) := by
        simp only [a₁, β, etaRho]; field_simp; ring
      rw [e]
      have : (Real.pi / varpi + t + 0 + 0) * varpi = Real.pi - varpi / c := by
        simp only [t]; field_simp; ring
      rw [this, div_eq_iff (mul_ne_zero hc0 hO),
        show (Real.pi - varpi / c) * (c * omegaRho) = Real.pi * c * omegaRho - varpi * omegaRho by
          field_simp]
      have h' := hrel'
      rw [div_eq_iff hpi] at h'
      linear_combination h'
    obtain ⟨x, x', hx, hx', hxx⟩ := mx_K hW hg₂ hg₃ hg₂' hg₃' hΓ hM β hβ hβ0 varpi
      (Real.pi / varpi + t) 0 0 a₁ 0 hX hY ha₁ isAlgebraic_zero hrelX
    -- `ϖ + a₁ = xϖ + x'Ω` forces `a₁ = 0`
    obtain ⟨e0, -, -, -, -, -⟩ := six_zero h6 a₁ 0 (1 - x) 0 (-x') 0 ha₁ isAlgebraic_zero
      (isAlgebraic_one.sub hx) isAlgebraic_zero hx'.neg isAlgebraic_zero (by linear_combination hxx)
    -- then `βη_ρ = η_i + t`, against the independence of `1, η_i, η_ρ`
    rw [e0, add_zero, add_zero] at hrelX
    have : t + 0 * Real.pi + 0 * varpi + 1 * (Real.pi / varpi) + 0 * omegaRho + (-β) * etaRho = 0 := by
      have := congrArg (· / (varpi : ℂ)) hrelX
      field_simp at this ⊢
      linear_combination -this
    obtain ⟨-, -, -, e3, -, -⟩ := six_zero h6 t 0 0 1 0 (-β) ht isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_one isAlgebraic_zero hβ.neg this
    exact one_ne_zero e3

lemma transcendental_omegaRho_div_varpi_of_six (h6 : WuestholzSix) :
    Transcendental ℚ ((omegaRho : ℂ) / varpi) := by
  intro halg
  have hv := varpi_ne_zero'
  obtain ⟨-, -, -, -, h4, -⟩ := six_zero h6 0 0 (-((omegaRho : ℂ) / varpi)) 0 1 0 isAlgebraic_zero
    isAlgebraic_zero halg.neg isAlgebraic_zero isAlgebraic_one isAlgebraic_zero (by field_simp; ring)
  exact one_ne_zero h4

/-- **Corollary deg2 (i)**: `π, ϖ, Ω_ρ, ϖΩ_ρ` are linearly independent over `ℚ̄`. From Proposition D′ (`mxP_K`).
The case where `π` has coefficient `0` (`c₁ϖ + c₂Ω_ρ + c₃ϖΩ_ρ = 0`) uses `Y = (Ω_ρ, η_ρ)` and `β = √3/2`. -/
theorem deg2_i (hW : Thm11KappaMXP) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (h6 : WuestholzSix)
    (c0 c1 c2 c3 : ℂ) (h0 : IsAlgebraic ℚ c0) (h1 : IsAlgebraic ℚ c1) (h2 : IsAlgebraic ℚ c2)
    (h3 : IsAlgebraic ℚ c3)
    (hrel : c0 * Real.pi + c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have hv := varpi_ne_zero'
  have hO := omegaRho_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr := r3_ne_zero
  have hr3 := r3_sq
  have hM := transcendental_omegaRho_div_varpi_of_six h6
  have hX : LogNat lemniscatic etaLem varpi (Real.pi / varpi) :=
    Or.inl ⟨1, 0, by simp [lemniscatic], isAlg_zero_of (by simp [etaLem])⟩
  by_cases hc3 : c3 = 0
  · subst hc3
    obtain ⟨-, e1, e2, -, e4, -⟩ := six_zero h6 0 c0 c1 0 c2 0 isAlgebraic_zero h0 h1 isAlgebraic_zero h2
      isAlgebraic_zero (by linear_combination hrel)
    exact ⟨e1, e2, e4, rfl⟩
  exfalso
  by_cases hc0 : c0 = 0
  · -- `c₁ϖ + c₂Ω + c₃ϖΩ = 0`
    subst hc0
    set k := (r3 / 2 - 1) / c3 with hk
    have hk0 : k ≠ 0 := by
      refine div_ne_zero ?_ hc3
      intro h0
      have : r3 = 2 := by linear_combination 2 * h0
      rw [this] at hr3; norm_num at hr3
    have halgr : IsAlgebraic ℚ (r3 / 2) := by
      rw [← mem_algebraicClosure_iff]
      exact div_mem (mem_algebraicClosure_iff.mpr isAlgebraic_r3) (by simp)
    have hkalg : IsAlgebraic ℚ k := by
      rw [hk, div_eq_mul_inv]; exact (halgr.sub isAlgebraic_one).mul h3.inv
    have hY : LogNat equianharmonic etaR omegaRho etaRho :=
      Or.inl ⟨1, 0, by simp [equianharmonic], isAlg_zero_of (by simp [etaR])⟩
    set a := 2 * k * c2 / r3
    have ha : IsAlgebraic ℚ a := by
      simp only [a, div_eq_mul_inv]
      exact ((by simpa using (isAlgebraic_algebraMap (2 : ℚ) : IsAlgebraic ℚ ((2 : ℚ) : ℂ)) :
        IsAlgebraic ℚ (2 : ℂ)).mul hkalg |>.mul h2).mul isAlgebraic_r3.inv
    have hrelP : (varpi + etaRho + a) * (r3 / 2 * omegaRho) =
        (Real.pi / varpi + omegaRho + -(k * c1)) * varpi := by
      have hη : etaRho * omegaRho = 2 * r3 * Real.pi / 3 := etaRho_mul
      have e : k * (c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho)) = 0 := by
        rw [show c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho) = 0 by linear_combination hrel,
          mul_zero]
      have hkc3 : k * c3 = r3 / 2 - 1 := by rw [hk]; field_simp
      simp only [a]
      have hpv : Real.pi / varpi * varpi = (Real.pi : ℂ) := by field_simp
      have hri : r3 * r3⁻¹ = 1 := mul_inv_cancel₀ hr
      linear_combination e + (r3 / 2) * hη + (Real.pi / 3) * hr3 - hpv +
        k * c2 * omegaRho * hri - (varpi * omegaRho) * hkc3
    obtain ⟨x, x', hx, hx', hxx⟩ := mxP_K hW hg₂ hg₃ hg₂' hg₃' hΓ hM (r3 / 2) halgr
      (div_ne_zero hr two_ne_zero) varpi (Real.pi / varpi) omegaRho etaRho a (-(k * c1)) hX hY ha
      (hkalg.mul h1).neg hrelP
    obtain ⟨ea, -, -, -, -, -⟩ := six_zero h6 a 0 (1 - x) 0 0 (1 - x') ha isAlgebraic_zero
      (isAlgebraic_one.sub hx) isAlgebraic_zero isAlgebraic_zero (isAlgebraic_one.sub hx')
      (by linear_combination hxx)
    have hc2 : c2 = 0 := by
      have : 2 * k * c2 = 0 := by
        have := ea; simp only [a] at this
        rcases div_eq_zero_iff.mp this with h | h
        · exact h
        · exact absurd h hr
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hk0)
      · exact h
    subst hc2
    have : varpi * (c1 + c3 * omegaRho) = 0 := by linear_combination hrel
    have h' := (mul_eq_zero.mp this).resolve_left hv
    obtain ⟨-, -, -, -, e4, -⟩ := six_zero h6 c1 0 0 0 c3 0 h1 isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_zero h3 isAlgebraic_zero (by linear_combination h')
    exact hc3 e4
  · -- `π = AϖΩ + Bϖ + CΩ` with `A ≠ 0`
    set A := -c3 / c0
    set B := -c1 / c0
    set C := -c2 / c0
    have hA : IsAlgebraic ℚ A := by simp only [A, div_eq_mul_inv]; exact h3.neg.mul h0.inv
    have hB : IsAlgebraic ℚ B := by simp only [B, div_eq_mul_inv]; exact h1.neg.mul h0.inv
    have hC : IsAlgebraic ℚ C := by simp only [C, div_eq_mul_inv]; exact h2.neg.mul h0.inv
    have hA0 : A ≠ 0 := div_ne_zero (neg_ne_zero.mpr hc3) hc0
    have hπ : (Real.pi : ℂ) = A * (varpi * omegaRho) + B * varpi + C * omegaRho := by
      simp only [A, B, C]; field_simp; linear_combination hrel
    have hY : LogNat equianharmonic etaR 0 0 :=
      Or.inl ⟨0, 0, by simp, isAlg_zero_of (by simp [etaR])⟩
    have hrelP : (varpi + 0 + C / A) * (A * omegaRho) = (Real.pi / varpi + 0 + -B) * varpi := by
      have hpv : Real.pi / varpi * varpi = (Real.pi : ℂ) := by field_simp
      have e : (varpi + 0 + C / A) * (A * omegaRho) = A * (varpi * omegaRho) + C * omegaRho := by
        field_simp; ring
      rw [e, add_mul, add_mul, hpv]
      linear_combination -hπ
    obtain ⟨x, x', hx, hx', hxx⟩ := mxP_K hW hg₂ hg₃ hg₂' hg₃' hΓ hM A hA hA0 varpi (Real.pi / varpi)
      0 0 (C / A) (-B) hX hY (by rw [div_eq_mul_inv]; exact hC.mul hA.inv) hB.neg hrelP
    have hCA : IsAlgebraic ℚ (C / A) := by rw [div_eq_mul_inv]; exact hC.mul hA.inv
    obtain ⟨eC, -, -, -, -, -⟩ := six_zero h6 (C / A) 0 (1 - x) 0 0 (-x') hCA isAlgebraic_zero
      (isAlgebraic_one.sub hx) isAlgebraic_zero isAlgebraic_zero hx'.neg (by linear_combination hxx)
    -- then `π/ϖ − B = AΩ`
    rw [eC] at hrelP
    have hdiv : (Real.pi / varpi + -B) = A * omegaRho :=
      mul_right_cancel₀ hv (by linear_combination -hrelP)
    obtain ⟨-, -, -, e3, -, -⟩ := six_zero h6 (-B) 0 0 1 (-A) 0 hB.neg isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_one hA.neg isAlgebraic_zero (by linear_combination hdiv)
    exact one_ne_zero e3

end CM4E.Gen
