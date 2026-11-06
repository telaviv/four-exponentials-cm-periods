/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.ThmM
import CM4E.Gen.Instances
import LSG.Weierstrass.Addition

/-!
# Arithmetic of elliptic logarithms

`Gen.LogE P u` (`u ∈ Λ`, or `℘(u)`, `℘'(u)` algebraic) is the `E`-coordinate condition of the logarithms of algebraic
points. For the bridges of the models with elliptic logarithms (`gmMGK`, `gmM`) two facts are needed:

* `logE_neg`, `logE_add`: if `g₂` is algebraic, the elliptic logarithms of algebraic points are closed under negation
  and addition (the addition and duplication formulas of `LSG.Weierstrass`);
* `CMMulLogE L`: `LogE` is stable under multiplication by `α`. Proved for `ϖℤ[i]` (`℘(iz) = −℘(z)`,
  `℘'(iz) = i℘'(z)`) and `Ω_ρℤ[ρ]` (`℘(ρz) = ρ℘(z)`, `℘'(ρz) = ℘'(z)`) by reindexing the lattice sums.
-/

open Complex CM4E.Gen LSG.Weierstrass
open scoped PeriodPair

namespace CM4E.Bridge

variable (P : PeriodPair)

lemma alg_mem {x : ℂ} : IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.symm

lemma logE_neg {u : ℂ} (h : LogE P u) : LogE P (-u) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (neg_mem h)
  · right; rw [PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg]; exact ⟨h1, h2.neg⟩

lemma logE_add_mem {u ω : ℂ} (h : LogE P u) (hω : ω ∈ P.lattice) : LogE P (u + ω) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (add_mem h hω)
  · right; rw [weierstrassP_add_mem P u hω, derivWeierstrassP_add_mem P u hω]; exact ⟨h1, h2⟩

lemma logE_two_mul (hg₂ : IsAlgebraic ℚ P.g₂) {z : ℂ} (h1 : IsAlgebraic ℚ (℘[P] z))
    (h2 : IsAlgebraic ℚ (℘'[P] z)) : LogE P (2 * z) := by
  by_cases h : 2 * z ∈ P.lattice
  · exact Or.inl h
  have ht : IsAlgebraic ℚ (tangentSlope P z) := by
    unfold tangentSlope
    rw [alg_mem] at h1 h2 hg₂ ⊢
    exact div_mem (sub_mem (mul_mem (by simp) (pow_mem h1 2)) (div_mem hg₂ (by simp))) h2
  have hp : IsAlgebraic ℚ (℘[P] (2 * z)) := by
    rw [weierstrassP_two_mul P h]
    rw [alg_mem] at h1 ht ⊢
    exact add_mem (mul_mem (by simp) h1) (div_mem (pow_mem ht 2) (by simp))
  refine Or.inr ⟨hp, ?_⟩
  rw [derivWeierstrassP_two_mul P h]
  rw [alg_mem] at h1 h2 ht hp ⊢
  exact sub_mem (mul_mem (neg_mem ht) (sub_mem hp h1)) h2

/-- **Elliptic logarithms of algebraic points are closed under addition** (`g₂` algebraic). -/
lemma logE_add (hg₂ : IsAlgebraic ℚ P.g₂) {z w : ℂ} (hz : LogE P z) (hw : LogE P w) : LogE P (z + w) := by
  rcases hz with hz | ⟨hz1, hz2⟩
  · rw [add_comm]; exact logE_add_mem P hw hz
  rcases hw with hw | ⟨hw1, hw2⟩
  · exact logE_add_mem P (Or.inr ⟨hz1, hz2⟩) hw
  by_cases hzL : z ∈ P.lattice
  · rw [add_comm]; exact logE_add_mem P (Or.inr ⟨hw1, hw2⟩) hzL
  by_cases hwL : w ∈ P.lattice
  · exact logE_add_mem P (Or.inr ⟨hz1, hz2⟩) hwL
  by_cases hs : z + w ∈ P.lattice
  · exact Or.inl hs
  by_cases hd : z - w ∈ P.lattice
  · -- `z + w = 2z − (z − w)`
    have e : z + w = 2 * z + -(z - w) := by ring
    rw [e]; exact logE_add_mem P (logE_two_mul P hg₂ hz1 hz2) (neg_mem hd)
  have hm : IsAlgebraic ℚ (chordSlope P z w) := by
    unfold chordSlope
    rw [alg_mem] at hz1 hz2 hw1 hw2 ⊢
    exact div_mem (sub_mem hz2 hw2) (sub_mem hz1 hw1)
  have hp : IsAlgebraic ℚ (℘[P] (z + w)) := by
    rw [weierstrassP_add P hzL hwL hs hd]
    rw [alg_mem] at hz1 hw1 hm ⊢
    exact add_mem (sub_mem (neg_mem hz1) hw1) (div_mem (pow_mem hm 2) (by simp))
  refine Or.inr ⟨hp, ?_⟩
  rw [derivWeierstrassP_add P hzL hwL hs hd]
  rw [alg_mem] at hz1 hz2 hm hp ⊢
  exact sub_mem (mul_mem (neg_mem hm) (sub_mem hp hz1)) hz2

/-- Complex multiplication on elliptic logarithms of algebraic points. -/
def CMMulLogE (L : CMLattice) : Prop := ∀ u, LogE L.pp u → LogE L.pp (L.α * u)

lemma summand_I (a b : ℂ) : 1 / (I * a) ^ 2 - 1 / (I * b) ^ 2 = -(1 / a ^ 2 - 1 / b ^ 2) := by
  rw [mul_pow, mul_pow, I_sq]; ring

lemma dsummand_I (a : ℂ) : 2 / (I * a) ^ 3 = I * (2 / a ^ 3) := by
  rw [mul_pow, show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]
  have : (-I)⁻¹ = I := by rw [inv_neg, Complex.inv_I, neg_neg]
  rw [div_eq_mul_inv, mul_inv, this, div_eq_mul_inv]; ring

lemma summand_cube {r : ℂ} (h3 : r ^ 3 = 1) (a b : ℂ) :
    1 / (r * a) ^ 2 - 1 / (r * b) ^ 2 = r * (1 / a ^ 2 - 1 / b ^ 2) := by
  have h2 : (r ^ 2)⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact h3)
  rw [mul_pow, mul_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, h2]; ring

/-- `℘(iz) = −℘(z)` and `℘'(iz) = i℘'(z)` on `ϖℤ[i]`. -/
lemma weierstrassP_I_mul (z : ℂ) :
    ℘[lemniscatic] (I * z) = -℘[lemniscatic] z ∧ ℘'[lemniscatic] (I * z) = I * ℘'[lemniscatic] z := by
  constructor
  · rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, ← mulI.tsum_eq, ← tsum_neg]
    congr with l
    simp only [mulI, Equiv.coe_fn_mk]
    rw [show I * z - I * (l : ℂ) = I * (z - l) by ring, summand_I]
  · rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, ← mulI.tsum_eq, mul_neg, neg_inj,
      ← tsum_mul_left]
    congr with l
    simp only [mulI, Equiv.coe_fn_mk]
    rw [show I * z - I * (l : ℂ) = I * (z - l) by ring, dsummand_I]

/-- `℘(ρz) = ρ℘(z)` and `℘'(ρz) = ℘'(z)` on `Ω_ρℤ[ρ]`. -/
lemma weierstrassP_rho_mul (z : ℂ) :
    ℘[MX.equianharmonic] (MX.rho * z) = MX.rho * ℘[MX.equianharmonic] z ∧
      ℘'[MX.equianharmonic] (MX.rho * z) = ℘'[MX.equianharmonic] z := by
  have h3 := MX.rho_cube
  constructor
  · rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, ← MX.mulRho.tsum_eq, ← tsum_mul_left]
    congr with l
    simp only [MX.mulRho, Equiv.coe_fn_mk]
    rw [show MX.rho * z - MX.rho * (l : ℂ) = MX.rho * (z - l) by ring, summand_cube h3]
  · rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, ← MX.mulRho.tsum_eq]
    congr 1
    congr with l
    simp only [MX.mulRho, Equiv.coe_fn_mk]
    rw [show MX.rho * z - MX.rho * (l : ℂ) = MX.rho * (z - l) by ring, mul_pow, h3, one_mul]

lemma cmMulLogE_latI : CMMulLogE latI := by
  rintro u (hu | ⟨h1, h2⟩)
  · exact Or.inl (I_mul_mem_lattice hu)
  · right
    show IsAlgebraic ℚ (℘[lemniscatic] (I * u)) ∧ IsAlgebraic ℚ (℘'[lemniscatic] (I * u))
    rw [(weierstrassP_I_mul u).1, (weierstrassP_I_mul u).2]
    exact ⟨h1.neg, isAlgebraic_I.mul h2⟩

lemma cmMulLogE_latRho : CMMulLogE latRho := by
  rintro u (hu | ⟨h1, h2⟩)
  · exact Or.inl (MX.rho_mul_mem_lattice hu)
  · right
    show IsAlgebraic ℚ (℘[MX.equianharmonic] (MX.rho * u)) ∧
      IsAlgebraic ℚ (℘'[MX.equianharmonic] (MX.rho * u))
    rw [(weierstrassP_rho_mul u).1, (weierstrassP_rho_mul u).2]
    exact ⟨latRho.isAlgebraic_α.mul h1, h2⟩

end CM4E.Bridge
