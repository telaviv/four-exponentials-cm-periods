/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.SMG
import CM4E.Gen.PiTranscendental

/-!
# Corollaries MG1 and MG3 (paper)

Both follow from Theorem SMG (`CM4E/Gen/SMG.lean`, slope `s = ω/π`), whose data may lie in `𝓛̃ ⊃ ℚ̄𝓛`.

* **MG1**: for `a, b, c ∈ ℚ̄ˣ`, one of `e^{aπ²}`, `e^{bπω}`, `e^{cπ²/ω}` is transcendental. Data `(π², π²/ω)`; the
  `ℚ̄`-independence of `2πi, π², π²/ω` uses the transcendence of `π` (proved: `transcendental_pi`), of `ω` and `ω/π` (Schneider) and
  `ω ∉ 𝓛̃` (`NotLtilde`).
* **MG3**: if `e^{π²}` and `e^{cπω}` are algebraic, then `α^{ω/π} = e^{(ω/π) log α} ∉ ℚ̄` whenever `2πi, π², log α` are
  `ℚ`-independent. The step from `ℚ`- to `ℚ̄`-independence of these logarithms is Baker's theorem.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

/-- **Named input (Baker 1966).** Logarithms of algebraic numbers that are linearly independent over `ℚ` are linearly
independent over `ℚ̄` (stated for three of them). -/
def Baker3 : Prop :=
  ∀ x : Fin 3 → ℂ, (∀ k, IsAlgebraic ℚ (Complex.exp (x k))) → LinearIndependent ℚ x →
    ∀ a : Fin 3 → ℂ, (∀ k, IsAlgebraic ℚ (a k)) → ∑ k, a k * x k = 0 → ∀ k, a k = 0

lemma mem_Ltilde_of_log {z c : ℂ} (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (hz : IsAlgebraic ℚ (Complex.exp (c * z))) : z ∈ Ltilde :=
  ⟨1, 0, fun _ => c⁻¹, fun _ => c * z, isAlgebraic_zero, fun _ => hc.inv, fun _ => hz, by
    simp; field_simp⟩

lemma pi_mem_Ltilde : (Real.pi : ℂ) ∈ Ltilde := by
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  refine mem_Ltilde_of_log hI Complex.I_ne_zero ?_
  rw [mul_comm, Complex.exp_pi_mul_I]
  exact isAlgebraic_one.neg

variable (L : CMLattice)

lemma isAlg_two_I_mul {a : ℂ} (ha : IsAlgebraic ℚ a) : IsAlgebraic ℚ (2 * I * a) := by
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  rw [← mem_algebraicClosure_iff]
  exact mul_mem (mul_mem (by simp) (mem_algebraicClosure_iff.mpr hI)) (mem_algebraicClosure_iff.mpr ha)

/-- **Corollary MG1** for a CM lattice: for `a, b, c ∈ ℚ̄ˣ`, `e^{aπ²}`, `e^{bπω}`, `e^{cπ²/ω}` are not all algebraic. -/
theorem mg1 (hW : Thm11KappaSMG L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hTω : Transcendental ℚ L.ω) (hTωπ : Transcendental ℚ (L.ω / Real.pi)) (hNot : NotLtilde L)
    (a b c : ℂ) (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) (hb : IsAlgebraic ℚ b)
    (hb0 : b ≠ 0) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (b * Real.pi * L.ω)) ∧
      IsAlgebraic ℚ (Complex.exp (c * Real.pi ^ 2 / L.ω))) := by
  rintro ⟨h1, h2, h3⟩
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπω : (Real.pi : ℂ) * L.ω ∈ Ltilde := mem_Ltilde_of_log hb hb0 (by rwa [← mul_assoc])
  have hy : ∀ k, ![(Real.pi : ℂ) ^ 2, (Real.pi : ℂ) ^ 2 / L.ω] k ∈ Ltilde := Fin.forall_fin_two.mpr
    ⟨mem_Ltilde_of_log ha ha0 h1, mem_Ltilde_of_log hc hc0 (by rwa [mul_div_assoc] at h3)⟩
  have hsy : ∀ k, 1 * L.ω / Real.pi * ![(Real.pi : ℂ) ^ 2, (Real.pi : ℂ) ^ 2 / L.ω] k ∈ Ltilde := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · have : 1 * L.ω / Real.pi * ![(Real.pi : ℂ) ^ 2, (Real.pi : ℂ) ^ 2 / L.ω] 0 = Real.pi * L.ω := by
        simp; field_simp
      rw [this]; exact hπω
    · have : 1 * L.ω / Real.pi * ![(Real.pi : ℂ) ^ 2, (Real.pi : ℂ) ^ 2 / L.ω] 1 = Real.pi := by
        simp; field_simp
      rw [this]; exact pi_mem_Ltilde
  refine smg_false L hW hg₂ hg₃ hTωπ 1 isAlgebraic_one one_ne_zero _ hy hsy ?_
  intro a₀ a₁ a₂ h₀ h₁ h₂ hrel
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hrel
  -- divide by `π`
  have h' : 2 * I * a₀ + a₁ * Real.pi + a₂ * (Real.pi / L.ω) = 0 := by
    have : (Real.pi : ℂ) * (2 * I * a₀ + a₁ * Real.pi + a₂ * (Real.pi / L.ω)) = 0 := by
      rw [← hrel]; ring
    exact (mul_eq_zero.mp this).resolve_left hpi
  by_cases ha₂ : a₂ = 0
  · subst ha₂
    by_cases ha₁ : a₁ = 0
    · subst ha₁
      have : 2 * I * a₀ = 0 := by linear_combination h'
      refine ⟨?_, rfl, rfl⟩
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      · exact h
    · exfalso; apply transcendental_pi
      have : (Real.pi : ℂ) = -(2 * I * a₀) / a₁ := by
        rw [eq_div_iff ha₁]; linear_combination h'
      rw [this]
      exact isAlg_div (isAlg_two_I_mul h₀).neg h₁
  · exfalso
    set A := -(2 * I * a₀) / a₂
    set B := -a₁ / a₂
    have hAalg : IsAlgebraic ℚ A := isAlg_div (isAlg_two_I_mul h₀).neg h₂
    have hBalg : IsAlgebraic ℚ B := isAlg_div h₁.neg h₂
    have hAB : (Real.pi : ℂ) = (A + B * Real.pi) * L.ω := by
      have e : A + B * Real.pi = (-(2 * I * a₀) - a₁ * Real.pi) / a₂ := by
        simp only [A, B]; field_simp; ring
      rw [e, div_mul_eq_mul_div, eq_div_iff ha₂]
      have e2 : a₂ * Real.pi = (-(2 * I * a₀) - a₁ * Real.pi) * L.ω := by
        have h3 : a₂ * (Real.pi / L.ω) * L.ω = a₂ * Real.pi := by field_simp
        linear_combination L.ω * h' - h3
      linear_combination e2
    by_cases hB : B = 0
    · apply hTωπ
      rw [hB, zero_mul, add_zero] at hAB
      have hA0 : A ≠ 0 := by intro h0; rw [h0, zero_mul] at hAB; exact hpi hAB
      have : L.ω / Real.pi = A⁻¹ := by
        rw [div_eq_iff hpi, hAB]; field_simp
      rw [this]; exact hAalg.inv
    · by_cases hA : A = 0
      · apply hTω
        rw [hA, zero_add] at hAB
        have e1 : (Real.pi : ℂ) * (1 - B * L.ω) = 0 := by linear_combination hAB
        have e2 : B * L.ω = 1 := by
          have := (mul_eq_zero.mp e1).resolve_left hpi; linear_combination -this
        have : L.ω = B⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact e2)
        rw [this]; exact hBalg.inv
      · apply hNot.1
        have e1 : A * L.ω = Real.pi + (-B) * (Real.pi * L.ω) := by linear_combination -hAB
        have : L.ω = A⁻¹ * (Real.pi + (-B) * (Real.pi * L.ω)) := by rw [← e1]; field_simp
        rw [this]
        exact Ltilde_smul hAalg.inv (Ltilde_add pi_mem_Ltilde (Ltilde_smul hBalg.neg hπω))

/-- **Corollary MG3** for a CM lattice: if `e^{π²}` and `e^{cπω}` are algebraic (`c ∈ ℚ̄ˣ`) and `2πi, π², log α` are
`ℚ`-linearly independent (`e^{log α} = α` algebraic), then `e^{(ω/π) log α}` is transcendental. -/
theorem mg3 (hW : Thm11KappaSMG L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hTωπ : Transcendental ℚ (L.ω / Real.pi)) (hBaker : Baker3) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (hπω : IsAlgebraic ℚ (Complex.exp (c * Real.pi * L.ω))) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x))
    (hind : LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]) :
    Transcendental ℚ (Complex.exp (L.ω / Real.pi * x)) := by
  intro hsx
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hy : ∀ k, ![(Real.pi : ℂ) ^ 2, x] k ∈ Ltilde := Fin.forall_fin_two.mpr
    ⟨mem_Ltilde_of_log isAlgebraic_one one_ne_zero (by simpa using hπ2),
      mem_Ltilde_of_log isAlgebraic_one one_ne_zero (by simpa using hx)⟩
  have hsy : ∀ k, 1 * L.ω / Real.pi * ![(Real.pi : ℂ) ^ 2, x] k ∈ Ltilde := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · have : 1 * L.ω / Real.pi * ![(Real.pi : ℂ) ^ 2, x] 0 = Real.pi * L.ω := by simp; field_simp
      rw [this]; exact mem_Ltilde_of_log hc hc0 (by rwa [← mul_assoc])
    · have : 1 * L.ω / Real.pi * ![(Real.pi : ℂ) ^ 2, x] 1 = 1 * (L.ω / Real.pi * x) := by simp
      rw [this]; exact mem_Ltilde_of_log isAlgebraic_one one_ne_zero (by simpa using hsx)
  refine smg_false L hW hg₂ hg₃ hTωπ 1 isAlgebraic_one one_ne_zero _ hy hsy ?_
  intro a₀ a₁ a₂ h₀ h₁ h₂ hrel
  have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
    rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  have := hBaker ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]
    (by intro k; fin_cases k; exacts [h2pi, hπ2, hx]) hind ![a₀, a₁, a₂]
    (by intro k; fin_cases k; exacts [h₀, h₁, h₂])
    (by simpa [Fin.sum_univ_three] using hrel)
  exact ⟨by simpa using this 0, by simpa using this 1, by simpa using this 2⟩

end CM4E.Gen
