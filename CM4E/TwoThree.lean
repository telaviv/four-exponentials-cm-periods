/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import CM4E.MainQi

/-!
# Headline instance: `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic (conditional)

From `CM4E.MainQi.main` with `c = 1`, `a = log 2`, `b = log 3`. The only extra input is that `2πi, log 2, log 3`
are linearly independent over `ℚ` (proved below: parity of `2^m = 3^k`).
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.TwoThree

/-- If `A log 2 + B log 3 = 0` with integers `A, B`, then `A = B = 0`. -/
lemma int_log_two_three (A B : ℤ) (h : (A : ℝ) * Real.log 2 + B * Real.log 3 = 0) :
    A = 0 ∧ B = 0 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- |A| log 2 = |B| log 3, hence 2^|A| = 3^|B|
  have habs : (A.natAbs : ℝ) * Real.log 2 = (B.natAbs : ℝ) * Real.log 3 := by
    have e := congrArg abs (show (A : ℝ) * Real.log 2 = -((B : ℝ) * Real.log 3) by linarith)
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hl2, abs_of_pos hl3] at e
    rw [Nat.cast_natAbs, Nat.cast_natAbs]; push_cast; exact e
  have hpow : (2 : ℝ) ^ A.natAbs = (3 : ℝ) ^ B.natAbs := by
    have := congrArg Real.exp habs
    rwa [mul_comm, ← Real.log_rpow (by norm_num), mul_comm, ← Real.log_rpow (by norm_num),
      Real.exp_log (by positivity), Real.exp_log (by positivity), Real.rpow_natCast,
      Real.rpow_natCast] at this
  have hnat : 2 ^ A.natAbs = 3 ^ B.natAbs := by exact_mod_cast hpow
  have hA0 : A.natAbs = 0 := by
    by_contra hne
    have h2 : 2 ^ A.natAbs % 2 = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [hk, pow_succ]; simp
    have h3 : 3 ^ B.natAbs % 2 = 1 := by rw [Nat.pow_mod]; simp
    omega
  have hB0 : B.natAbs = 0 := by
    rw [hA0, pow_zero] at hnat
    exact (Nat.pow_eq_one.mp hnat.symm).resolve_left (by norm_num)
  exact ⟨Int.natAbs_eq_zero.mp hA0, Int.natAbs_eq_zero.mp hB0⟩

/-- `2πi, log 2, log 3` are linearly independent over `ℚ`. -/
lemma linearIndependent_two_three :
    LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, Complex.log 2, Complex.log 3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp [Fin.sum_univ_succ, MainQi.rat_smul_eq] at hg
  have hl2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  have hl3 : Complex.log 3 = (Real.log 3 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  rw [hl2, hl3] at hg
  generalize hr2 : Real.log 2 = r2 at hg
  generalize hr3 : Real.log 3 = r3 at hg
  have him := congrArg Complex.im hg
  have hre := congrArg Complex.re hg
  simp at him hre
  have g0 : g 0 = 0 := by
    first
    | exact him
    | exact_mod_cast him
    | (rcases him with h | h
       · exact_mod_cast h
       · exact absurd h Real.pi_ne_zero)
  rw [← hr2, ← hr3] at hre
  -- clear denominators in `g 1 log 2 + g 2 log 3 = 0`
  set d : ℕ := (g 1).den * (g 2).den with hd
  have hdpos : (0 : ℚ) < d := by positivity
  have hA : ((g 1 * d : ℚ) : ℝ) = (((g 1).num * (g 2).den : ℤ) : ℝ) := by
    have : g 1 * d = ((g 1).num * (g 2).den : ℤ) := by
      rw [hd]; push_cast
      rw [show (g 1) * ((g 1).den * (g 2).den) = ((g 1) * (g 1).den) * (g 2).den by ring,
        Rat.mul_den_eq_num]
    rw [this]; push_cast; ring
  have hB : ((g 2 * d : ℚ) : ℝ) = (((g 2).num * (g 1).den : ℤ) : ℝ) := by
    have : g 2 * d = ((g 2).num * (g 1).den : ℤ) := by
      rw [hd]; push_cast
      rw [show (g 2) * ((g 1).den * (g 2).den) = ((g 2) * (g 2).den) * (g 1).den by ring,
        Rat.mul_den_eq_num]
    rw [this]; push_cast; ring
  have hint : (((g 1).num * (g 2).den : ℤ) : ℝ) * Real.log 2 +
      (((g 2).num * (g 1).den : ℤ) : ℝ) * Real.log 3 = 0 := by
    rw [← hA, ← hB]; push_cast
    have : ((g 1 : ℝ) * Real.log 2 + (g 2 : ℝ) * Real.log 3) * d = 0 := by rw [hre]; ring
    linarith
  obtain ⟨h1, h2⟩ := int_log_two_three _ _ hint
  have g1 : g 1 = 0 := by
    have : (g 1).num = 0 := by
      rcases Int.mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (by exact_mod_cast (g 2).den_nz)
    exact Rat.zero_of_num_zero this
  have g2 : g 2 = 0 := by
    have : (g 2).num = 0 := by
      rcases Int.mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h (by exact_mod_cast (g 1).den_nz)
    exact Rat.zero_of_num_zero this
  intro i; fin_cases i <;> simp [g0, g1, g2]

/-- **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic**, conditional on the published theorem `Thm11Kappa` for
`G_m⁴ × E_i`, on `g₂(ϖℤ[i]) ∈ ℚ̄`, and on the irrationality of `ϖ/π`. -/
theorem two_three (hW : Thm11Kappa lemniscatic 4)
    (hg₂ : IsAlgebraic ℚ lemniscatic.g₂) (hS : Irrational (varpi / Real.pi)) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 3))) := by
  have ht : MainQi.tExp 1 0 1 = (varpi / Real.pi : ℂ) := by simp [MainQi.tExp]
  have halg : ∀ n : ℕ, IsAlgebraic ℚ (n : ℂ) := fun n =>
    ⟨Polynomial.X - Polynomial.C (n : ℚ), Polynomial.X_sub_C_ne_zero _, by simp⟩
  have h2 : Complex.log 2 ∈ logAlg := by
    change IsAlgebraic ℚ (Complex.exp (Complex.log 2))
    rw [Complex.exp_log (by norm_num)]; exact_mod_cast halg 2
  have h3 : Complex.log 3 ∈ logAlg := by
    change IsAlgebraic ℚ (Complex.exp (Complex.log 3))
    rw [Complex.exp_log (by norm_num)]; exact_mod_cast halg 3
  rw [← ht]
  have hind : LinearIndependent ℚ ![Complex.log 2, Complex.log 3] := by
    have := linearIndependent_two_three.comp Fin.succ (Fin.succ_injective _)
    convert this using 1
    funext i; fin_cases i <;> rfl
  exact MainQi.main hW hg₂ hS 1 0 1 one_pos (Or.inl one_ne_zero) _ _ h2 h3 hind

end CM4E.TwoThree
