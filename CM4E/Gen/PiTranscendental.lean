/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Ext.Interface
import CM4E.Ext.Schneider
import CM4E.Ext.SchneiderLang.Main

/-!
# Lindemann: `π` is transcendental

`CM4E.Gen.transcendental_pi : Transcendental ℚ (Real.pi : ℂ)`, from the vendored Schneider–Lang criterion
`CM4E.Ext.schneiderLang`.

If `π` were algebraic, so would be `πi`; over `K = ℚ(πi)` the entire functions `z` and `e^z` (order `≤ 2`,
denominator `h = 1`) satisfy `z' = 1`, `(e^z)' = e^z`, and are algebraically independent over `K` (a polynomial
`P(x, y)` vanishing at all `(z, e^z)` has, for each of the infinitely many values `y = e^{x₀}`, the infinitely many
roots `x = x₀ + 2πik`). Both take values in `K` at the infinitely many points `2πik` (`k ∈ ℕ`), contradicting
Schneider–Lang.
-/

open Complex Real

namespace CM4E.Gen

/-- `z` and `e^z` are algebraically independent over any field `K → ℂ`. -/
theorem algIndep_id_exp {K : Type*} [Field K] [Algebra K ℂ] (P : MvPolynomial (Fin 2) K)
    (hP : ∀ z : ℂ, MvPolynomial.aeval ![z, cexp z] P = 0) : P = 0 := by
  have hY : (Set.range fun n : ℕ => cexp n).Infinite := by
    refine Set.infinite_range_of_injective fun m n hmn => ?_
    have h := congrArg Complex.re hmn
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_exp, Complex.ofReal_re] at h
    exact_mod_cast Real.exp_injective h
  refine CM4E.Ext.Weierstrass.mvPoly_eq_zero_of_infinite_fibres P hY ?_
  rintro _ ⟨n, rfl⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℤ => (n : ℂ) + k * (2 * π * I)) ?_ ?_
  · intro k l hkl
    have h2 : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp only [add_right_inj] at hkl
    exact_mod_cast mul_right_cancel₀ h2 hkl
  · intro k
    have := hP ((n : ℂ) + k * (2 * π * I))
    rwa [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one] at this

/-- **Lindemann (1882).** `π` is transcendental. -/
theorem transcendental_pi : Transcendental ℚ (Real.pi : ℂ) := by
  intro halg
  have hπI : IsAlgebraic ℚ ((Real.pi : ℂ) * I) := halg.mul CM4E.Ext.Schneider.isAlgebraic_I
  set K := IntermediateField.adjoin ℚ ({(Real.pi : ℂ) * I} : Set ℂ)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro x rfl
    exact hπI.isIntegral)
  have mπI : (Real.pi : ℂ) * I ∈ K := IntermediateField.subset_adjoin _ _ (by simp)
  have hfin := CM4E.Ext.schneiderLang K 2 ![fun z => z, fun z => cexp z] (fun _ => 1) 2
    (by
      intro i
      fin_cases i
      · exact differentiable_id
      · exact Complex.differentiable_exp)
    (differentiable_const _)
    (by
      intro i
      fin_cases i
      · exact ⟨1, CM4E.Ext.Schneider.norm_le_exp_sq⟩
      · refine ⟨1, fun z => ?_⟩
        simpa using CM4E.Ext.Schneider.norm_cexp_le_exp_sq 1 z)
    ⟨0, fun z => by simp⟩
    (by
      intro i
      fin_cases i
      · refine ⟨1, fun z _ => ?_⟩
        convert hasDerivAt_id' z using 1 <;> simp
      · refine ⟨MvPolynomial.X 1, fun z _ => ?_⟩
        simpa using Complex.hasDerivAt_exp z)
    ⟨0, 1, fun P hP => algIndep_id_exp P fun z => by simpa using hP z one_ne_zero⟩
  refine (Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (k : ℂ) * (2 * π * I)) ?_ ?_) hfin
  · intro k l hkl
    have h2 : (2 * (π : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact_mod_cast mul_right_cancel₀ h2 hkl
  · intro k
    refine ⟨one_ne_zero, fun i => ?_⟩
    fin_cases i
    · refine ⟨⟨(k : ℂ) * (2 * π * I), ?_⟩, ?_⟩
      · have : (k : ℂ) * (2 * π * I) = ((2 * k : ℕ) : ℂ) * ((Real.pi : ℂ) * I) := by
          push_cast; ring
        rw [this]
        exact K.mul_mem (K.natCast_mem _) mπI
      · simp
    · refine ⟨1, ?_⟩
      simp [Complex.exp_nat_mul_two_pi_mul_I]

end CM4E.Gen
