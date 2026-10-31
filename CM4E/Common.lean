/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs

/-!
# Small shared facts

Algebraicity of `i` and `√n`, `π ≠ 0`, and the `ℚ`-independence of `1, i, s, is` for an irrational real `s`
(used for the bases `θ = (1, i, √2, i√2)` of `ℚ(i, √2)` and `(1, i, √3, i√3)` of `ℚ(i, √3)`), and the
`ℚ`-independence of `log 2, log 3` (parity of `2^m = 3^k`).
-/

open Complex

namespace CM4E

lemma isAlgebraic_I : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)

lemma isAlgebraic_sqrt_nat (n : ℕ) : IsAlgebraic ℚ ((Real.sqrt n : ℝ) : ℂ) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), ?_, ?_⟩
  · intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp at this
  · simp [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

lemma pi_ne_zero' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- For irrational real `s`, `x + iy + su + isv = 0` with rational coefficients forces all of them to vanish. -/
lemma quad_inj {s : ℝ} (hs : Irrational s) (x y u v : ℚ)
    (h : (x : ℂ) + I * y + (s : ℂ) * u + I * (s : ℂ) * v = 0) :
    x = 0 ∧ y = 0 ∧ u = 0 ∧ v = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  have key : ∀ a b : ℚ, (a : ℝ) + s * b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb; simp at hab; exact ⟨by exact_mod_cast hab, rfl⟩
    · exfalso
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      exact hs ⟨-a / b, by push_cast; field_simp; linarith⟩
  obtain ⟨hx, hu⟩ := key x u (by linarith)
  obtain ⟨hy, hv⟩ := key y v (by linarith)
  exact ⟨hx, hy, hu, hv⟩

/-- `x + iy + su + isv` with rational coefficients is algebraic when `s` is. -/
lemma quad_mem_alg {s : ℂ} (hs : IsAlgebraic ℚ s) (x y u v : ℚ) :
    (x : ℂ) + I * y + s * u + I * s * v ∈ algebraicClosure ℚ ℂ := by
  have hr : s ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr hs
  have hI : I ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr isAlgebraic_I
  have hq : ∀ r : ℚ, (r : ℂ) ∈ algebraicClosure ℚ ℂ := fun r =>
    mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap r)
  exact add_mem (add_mem (add_mem (hq _) (mul_mem hI (hq _))) (mul_mem hr (hq _)))
    (mul_mem (mul_mem hI hr) (hq _))

/-! ## `log 2` and `log 3` -/

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

/-- `log 2, log 3` are linearly independent over `ℚ`. -/
lemma linearIndependent_two_three : LinearIndependent ℚ ![Complex.log 2, Complex.log 3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp [Fin.sum_univ_succ, Rat.smul_def] at hg
  have hre : (g 0 : ℝ) * Real.log 2 + (g 1 : ℝ) * Real.log 3 = 0 := by
    have := congrArg Complex.re hg
    simpa [Complex.log_re] using this
  -- clear denominators in `g 0 log 2 + g 1 log 3 = 0`
  set d : ℕ := (g 0).den * (g 1).den with hd
  have hA : ((g 0 * d : ℚ) : ℝ) = (((g 0).num * (g 1).den : ℤ) : ℝ) := by
    have : g 0 * d = ((g 0).num * (g 1).den : ℤ) := by
      rw [hd]; push_cast
      rw [show (g 0) * ((g 0).den * (g 1).den) = ((g 0) * (g 0).den) * (g 1).den by ring,
        Rat.mul_den_eq_num]
    rw [this]; push_cast; ring
  have hB : ((g 1 * d : ℚ) : ℝ) = (((g 1).num * (g 0).den : ℤ) : ℝ) := by
    have : g 1 * d = ((g 1).num * (g 0).den : ℤ) := by
      rw [hd]; push_cast
      rw [show (g 1) * ((g 0).den * (g 1).den) = ((g 1) * (g 1).den) * (g 0).den by ring,
        Rat.mul_den_eq_num]
    rw [this]; push_cast; ring
  have hint : (((g 0).num * (g 1).den : ℤ) : ℝ) * Real.log 2 +
      (((g 1).num * (g 0).den : ℤ) : ℝ) * Real.log 3 = 0 := by
    rw [← hA, ← hB]; push_cast
    have : ((g 0 : ℝ) * Real.log 2 + (g 1 : ℝ) * Real.log 3) * d = 0 := by rw [hre]; ring
    linarith
  obtain ⟨h1, h2⟩ := int_log_two_three _ _ hint
  have g0 : g 0 = 0 := by
    have : (g 0).num = 0 := by
      rcases Int.mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (by exact_mod_cast (g 1).den_nz)
    exact Rat.zero_of_num_zero this
  have g1 : g 1 = 0 := by
    have : (g 1).num = 0 := by
      rcases Int.mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h (by exact_mod_cast (g 0).den_nz)
    exact Rat.zero_of_num_zero this
  intro i; fin_cases i <;> simp [g0, g1]

/-- `log n` is the logarithm of an algebraic number. -/
lemma log_mem_logAlg (n : ℕ) (hn : n ≠ 0) : Complex.log n ∈ logAlg := by
  change IsAlgebraic ℚ (Complex.exp (Complex.log n))
  rw [Complex.exp_log (by exact_mod_cast hn)]
  exact isAlgebraic_natCast n

end CM4E
