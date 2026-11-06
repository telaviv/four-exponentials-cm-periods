/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The level-seven numbers: `ζ₇`, Beta values, and the first-kind relation

Data of the paper, §`sec:X7`, for the curve `C : y⁷ = x(1 − x)` (genus 3; `A = Jac(C)` has CM by `F = ℚ(ζ₇)` with
type `{1, 2, 3}`) and the CM elliptic curve `E` with CM by `ℚ(√−7)`:
* `zeta7 = e^{2πi/7}`; `alpha7 = ζ + ζ² + ζ⁴ = (−1 + √−7)/2` (`alpha7_sq : α² + α + 2 = 0`, `alpha7_im_ne : Im α ≠ 0`);
  `zeta_pow_three/four/five`: `ζ³, ζ⁴, ζ⁵` in the `k`-basis `1, ζ, ζ²` of `F` (`k = ℚ(α)`);
* `betaG a b = Γ(a)Γ(b)/Γ(a + b)` (`= B(a, b)`, `betaG_eq_betaIntegral`);
* `perA j = (1 − ζ^j) B(j/7, j/7)` (`j = 1, 2, 3`): the integrals of `dx/y^{7−j}` over one fixed cycle `γ` of `C`
  (paper); `omega7 = B(1/7, 2/7)`, a period of `E` up to `ℚ̄ˣ` (Chowla–Selberg);
* **the first-kind relation** `perA 1 · perA 2 = mu7' · perA 3 · omega7` with `mu7'` algebraic (`relation_R`), proved
  from the Beta cocycle and Euler's reflection formula: `μ = Γ(1/7)Γ(6/7)/(Γ(3/7)Γ(4/7)) = sin(3π/7)/sin(π/7) =
  1 + ζ + ζ⁶`.
The identification of `perA j` and `omega7` with periods (Rohrlich, Chowla–Selberg) is a soundness fact of the group
model of `CM4E/AbVar/X7.lean`, not used in any proof here.
-/

open Complex Polynomial

namespace CM4E.AbVar

/-- `ζ = e^{2πi/7}`. -/
noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * I / 7)

lemma zeta7_prim : IsPrimitiveRoot zeta7 7 := by
  have := Complex.isPrimitiveRoot_exp 7 (by norm_num)
  simpa [zeta7] using this

lemma zeta7_pow_seven : zeta7 ^ 7 = 1 := zeta7_prim.pow_eq_one

lemma zeta7_sum : 1 + zeta7 + zeta7 ^ 2 + zeta7 ^ 3 + zeta7 ^ 4 + zeta7 ^ 5 + zeta7 ^ 6 = 0 := by
  have := zeta7_prim.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using this

lemma isAlgebraic_zeta7 : IsAlgebraic ℚ zeta7 :=
  ⟨X ^ 7 - 1, by
    intro h
    have := congrArg (Polynomial.coeff · 7) h
    simp [Polynomial.coeff_one] at this, by simp [zeta7_pow_seven]⟩

lemma one_sub_zeta7_pow_ne {j : ℕ} (h0 : 0 < j) (h7 : j < 7) : 1 - zeta7 ^ j ≠ 0 := by
  intro h
  exact zeta7_prim.pow_ne_one_of_pos_of_lt (Nat.pos_iff_ne_zero.mp h0) h7 (by linear_combination -h)

/-- `α = ζ + ζ² + ζ⁴ = (−1 + √−7)/2`. -/
noncomputable def alpha7 : ℂ := zeta7 + zeta7 ^ 2 + zeta7 ^ 4

lemma alpha7_sq : alpha7 ^ 2 + alpha7 + 2 = 0 := by
  have h7 := zeta7_pow_seven
  simp only [alpha7]
  linear_combination 2 * zeta7_sum + zeta7 * h7

lemma isAlgebraic_alpha7 : IsAlgebraic ℚ alpha7 :=
  ((isAlgebraic_zeta7.add (isAlgebraic_zeta7.pow 2)).add (isAlgebraic_zeta7.pow 4))

lemma alpha7_im_ne : alpha7.im ≠ 0 := by
  intro h
  have hre : alpha7 = (alpha7.re : ℂ) := by
    apply Complex.ext <;> simp [h]
  have := alpha7_sq
  rw [hre] at this
  have h2 : (alpha7.re ^ 2 + alpha7.re + 2 : ℝ) = 0 := by exact_mod_cast this
  nlinarith [sq_nonneg (alpha7.re + 1 / 2)]

/-- `ζ³ = αζ² + (1 + α)ζ + 1`. -/
lemma zeta_pow_three : zeta7 ^ 3 = alpha7 * zeta7 ^ 2 + (1 + alpha7) * zeta7 + 1 := by
  simp only [alpha7]; linear_combination -zeta7_sum

/-- `ζ⁴ = −ζ² − ζ + α`. -/
lemma zeta_pow_four : zeta7 ^ 4 = -zeta7 ^ 2 - zeta7 + alpha7 := by
  simp only [alpha7]; ring

/-- `ζ⁵ = −(1 + α)ζ² − ζ − 1`. -/
lemma zeta_pow_five : zeta7 ^ 5 = -(1 + alpha7) * zeta7 ^ 2 - zeta7 - 1 := by
  simp only [alpha7]; linear_combination zeta7_sum

/-! ## Beta values -/

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`. -/
noncomputable def betaG (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

lemma Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gamma s ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hs

lemma betaG_eq_betaIntegral {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) : betaG a b = betaIntegral a b := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hne : Gamma (a + b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [betaG, h]; field_simp

/-- `Γ(k/7)`. -/
noncomputable def g7 (k : ℕ) : ℂ := Gamma ((k : ℂ) / 7)

lemma g7_ne {k : ℕ} (hk : 0 < k) : g7 k ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by simp; positivity)

/-- `perA j = (1 − ζ^j) B(j/7, j/7)`. -/
noncomputable def perA (j : ℕ) : ℂ := (1 - zeta7 ^ j) * betaG ((j : ℂ) / 7) ((j : ℂ) / 7)

/-- `Ω = B(1/7, 2/7)`. -/
noncomputable def omega7 : ℂ := betaG (1 / 7) (2 / 7)

/-- `μ = 1 + ζ + ζ⁶ = sin(3π/7)/sin(π/7)`. -/
noncomputable def mu7 : ℂ := 1 + zeta7 + zeta7 ^ 6

/-- The algebraic constant of the first-kind relation. -/
noncomputable def mu7' : ℂ := (1 - zeta7) * (1 - zeta7 ^ 2) * mu7 / (1 - zeta7 ^ 3)

lemma isAlgebraic_mu7' : IsAlgebraic ℚ mu7' := by
  have hz := isAlgebraic_zeta7
  rw [mu7', mu7, ← mem_algebraicClosure_iff]
  have hz' := mem_algebraicClosure_iff.mpr hz
  exact div_mem (mul_mem (mul_mem (sub_mem (one_mem _) hz') (sub_mem (one_mem _) (pow_mem hz' 2)))
    (add_mem (add_mem (one_mem _) hz') (pow_mem hz' 6))) (sub_mem (one_mem _) (pow_mem hz' 3))

/-- `sin(3π/7) = (1 + ζ + ζ⁶) sin(π/7)`. -/
lemma sin_three_pi_seven : Complex.sin (Real.pi * (3 / 7)) = mu7 * Complex.sin (Real.pi * (1 / 7)) := by
  set u := Complex.exp (Real.pi / 7 * I)
  set v := Complex.exp (-(Real.pi / 7 * I))
  have huv : u * v = 1 := by rw [← Complex.exp_add]; simp
  have hz : zeta7 = u ^ 2 := by
    rw [zeta7, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h14 : u ^ 14 = 1 := by
    rw [show u ^ 14 = (u ^ 2) ^ 7 by ring, ← hz, zeta7_pow_seven]
  have hv : v = u ^ 13 := by
    have hu0 : u ≠ 0 := Complex.exp_ne_zero _
    apply mul_left_cancel₀ hu0
    rw [huv]; linear_combination -h14
  have e3 : Complex.exp (-(Real.pi * (3 / 7) * I)) = v ^ 3 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e3' : Complex.exp (Real.pi * (3 / 7) * I) = u ^ 3 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e1 : Complex.exp (-(Real.pi * (1 / 7) * I)) = v := by congr 1; ring
  have e1' : Complex.exp (Real.pi * (1 / 7) * I) = u := by congr 1; ring
  rw [Complex.sin, Complex.sin, neg_mul, neg_mul, e3, e3', e1, e1', mu7, hz, hv]
  linear_combination (I / 2) * (u ^ 25 - u) * h14

lemma sin_pi_seven_ne (k : ℕ) (hk0 : 0 < k) (hk : k < 7) : Complex.sin (Real.pi * ((k : ℂ) / 7)) ≠ 0 := by
  rw [show (Real.pi : ℂ) * ((k : ℂ) / 7) = ((Real.pi * (k / 7) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin]
  exact Complex.ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by have : (k : ℝ) < 7 := by exact_mod_cast hk
        nlinarith [Real.pi_pos])).ne'

lemma mu7_ne : mu7 ≠ 0 := by
  intro h
  have := sin_three_pi_seven
  rw [h, zero_mul] at this
  exact sin_pi_seven_ne 3 (by norm_num) (by norm_num) (by simpa using this)

lemma mu7'_ne : mu7' ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (by simpa using one_sub_zeta7_pow_ne (j := 1) (by norm_num) (by norm_num))
    (one_sub_zeta7_pow_ne (by norm_num) (by norm_num))) mu7_ne) (one_sub_zeta7_pow_ne (by norm_num) (by norm_num))

lemma betaG_seven (a b : ℕ) : betaG ((a : ℂ) / 7) ((b : ℂ) / 7) = g7 a * g7 b / g7 (a + b) := by
  simp only [betaG, g7]; congr 2; push_cast; ring

lemma g7_reflect (k : ℕ) (hk : k ≤ 7) : g7 k * g7 (7 - k) = Real.pi / Complex.sin (Real.pi * ((k : ℂ) / 7)) := by
  rw [g7, g7, ← Complex.Gamma_mul_Gamma_one_sub]
  congr 2
  rw [Nat.cast_sub hk]; push_cast; ring

/-- **The first-kind relation** `P₁P₂ = μ' P₃ Ω` (Beta cocycle and reflection). -/
theorem relation_R : perA 1 * perA 2 = mu7' * perA 3 * omega7 := by
  have hΩ : omega7 = g7 1 * g7 2 / g7 3 := by
    rw [omega7, show (1 / 7 : ℂ) = ((1 : ℕ) : ℂ) / 7 by simp, show (2 / 7 : ℂ) = ((2 : ℕ) : ℂ) / 7 by simp,
      betaG_seven]
  have h1 := g7_reflect 1 (by norm_num)
  have h3 := g7_reflect 3 (by norm_num)
  have hs3 := sin_three_pi_seven
  have hs1 := sin_pi_seven_ne 1 (by norm_num) (by norm_num)
  have hs3' := sin_pi_seven_ne 3 (by norm_num) (by norm_num)
  simp only [Nat.cast_one, Nat.cast_ofNat] at h1 h3 hs1 hs3'
  norm_num at h1 h3
  have hmu : g7 1 * g7 6 = mu7 * (g7 3 * g7 4) := by
    rw [h1, h3, show (Real.pi : ℂ) * (3 / 7) = Real.pi * (3 / 7) from rfl, hs3]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hm := mu7_ne
    rw [show (Real.pi : ℂ) * (1 / 7) = Real.pi * 7⁻¹ by ring] at *
    field_simp
  have hz3 := one_sub_zeta7_pow_ne (j := 3) (by norm_num) (by norm_num)
  have g2 := g7_ne (k := 2) (by norm_num)
  have g3 := g7_ne (k := 3) (by norm_num)
  have g4 := g7_ne (k := 4) (by norm_num)
  have g6 := g7_ne (k := 6) (by norm_num)
  have e1 : perA 1 = (1 - zeta7) * (g7 1 * g7 1 / g7 2) := by rw [perA, betaG_seven]; norm_num
  have e2 : perA 2 = (1 - zeta7 ^ 2) * (g7 2 * g7 2 / g7 4) := by rw [perA, betaG_seven]
  have e3 : perA 3 = (1 - zeta7 ^ 3) * (g7 3 * g7 3 / g7 6) := by rw [perA, betaG_seven]
  have hq : g7 1 / g7 4 = mu7 * g7 3 / g7 6 := by
    rw [div_eq_div_iff g4 g6]; linear_combination hmu
  rw [e1, e2, e3, hΩ, mu7']
  calc (1 - zeta7) * (g7 1 * g7 1 / g7 2) * ((1 - zeta7 ^ 2) * (g7 2 * g7 2 / g7 4))
      = (1 - zeta7) * (1 - zeta7 ^ 2) * g7 1 * g7 2 * (g7 1 / g7 4) := by field_simp
    _ = (1 - zeta7) * (1 - zeta7 ^ 2) * g7 1 * g7 2 * (mu7 * g7 3 / g7 6) := by rw [hq]
    _ = _ := by field_simp

end CM4E.AbVar
