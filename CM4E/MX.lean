/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs
import CM4E.Waldschmidt
import CM4E.Lattice
import CM4E.Common
import LSG.Weierstrass.ZetaDef

/-!
# Theorem MX: the two curves, `Λ(E^♮)`, and quasi-periods

Definitions shared by the proof of Theorem MX (`CM4E/Gen/MXGen.lean`) and the general MG instances
(`CM4E/Gen/Instances.lean`):
* `E_ρ : y² = 4x³ − 4` with lattice `Ω_ρ ℤ[ρ]` (`equianharmonic`), `ρ = (−1 + i√3)/2`, `η(Ω_ρ) = 2π/(√3 Ω_ρ)`;
* the quasi-periods `etaR` (and `etaLem` for `ϖℤ[i]`, in `CM4E/Lattice.lean`);
* `LogNat`: the logarithms `Λ(E^♮)` of algebraic points of the universal vector extension, in coordinates with
  `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))`, `ζ = LSG.Weierstrass.zeta`.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.MX

/-! ## The equianharmonic lattice `Ω_ρ ℤ[ρ]` -/

lemma omegaRho_pos : 0 < omegaRho := by
  unfold omegaRho
  have h1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ ((4 : ℝ) / 3) := by positivity
  have h3 := Real.pi_pos
  positivity

lemma omegaRho_ne_zero : (omegaRho : ℂ) ≠ 0 := by exact_mod_cast omegaRho_pos.ne'

/-- `√3` as a complex number. -/
noncomputable def r3 : ℂ := (Real.sqrt 3 : ℂ)

lemma r3_sq : r3 ^ 2 = 3 := by
  simp [r3, ← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma r3_ne_zero : r3 ≠ 0 := by
  intro h; have := r3_sq; rw [h] at this; norm_num at this

/-- `ρ = (−1 + i√3)/2`. -/
noncomputable def rho : ℂ := (-1 + I * r3) / 2
/-- `ρ̄ = (−1 − i√3)/2`. -/
noncomputable def rhoBar : ℂ := (-1 - I * r3) / 2

lemma linearIndependent_rho : LinearIndependent ℝ ![(omegaRho : ℂ), rho * omegaRho] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hO := omegaRho_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have e1 : (s • (omegaRho : ℂ) + t • (rho * omegaRho)).im = t * (Real.sqrt 3 / 2 * omegaRho) := by
    simp [rho, r3]
  have e2 : (s • (omegaRho : ℂ) + t • (rho * omegaRho)).re = s * omegaRho - t * (omegaRho / 2) := by
    simp [rho, r3]; ring
  rw [e1] at him; rw [e2] at hre
  simp only [Complex.zero_im, Complex.zero_re] at him hre
  have ht : t = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exfalso; have : 0 < Real.sqrt 3 / 2 * omegaRho := by positivity
      linarith
  subst ht
  refine ⟨?_, rfl⟩
  rcases mul_eq_zero.mp (by linarith : s * omegaRho = 0) with h1 | h1
  · exact h1
  · linarith

/-- The period pair `(Ω_ρ, ρΩ_ρ)` of `y² = 4x³ − 4`. -/
noncomputable def equianharmonic : PeriodPair where
  ω₁ := omegaRho
  ω₂ := rho * omegaRho
  indep := linearIndependent_rho

lemma rho_sq : rho ^ 2 = -1 - rho := by simp only [rho]; ring_nf; rw [Complex.I_sq, r3_sq]; ring

/-- `ρ` times a point of `Ω_ρℤ[ρ]` is a point of `Ω_ρℤ[ρ]`. -/
lemma rho_mul_mem_lattice {x : ℂ} (hx : x ∈ equianharmonic.lattice) : rho * x ∈ equianharmonic.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  refine PeriodPair.mem_lattice.mpr ⟨-n, m - n, ?_⟩
  simp only [equianharmonic]; push_cast
  linear_combination (-(n : ℂ) * omegaRho) * rho_sq

lemma rho_cube : rho ^ 3 = 1 := by linear_combination (rho - 1) * rho_sq

lemma rho_ne_zero : rho ≠ 0 := by
  intro h; have := rho_cube; rw [h] at this; norm_num at this

lemma rho_inv : rho⁻¹ = starRingEnd ℂ rho := by
  apply inv_eq_of_mul_eq_one_right
  have hr : starRingEnd ℂ r3 = r3 := by simp [r3, Complex.conj_ofReal]
  simp only [rho, map_div₀, map_add, map_neg, map_one, map_mul, Complex.conj_I, Complex.conj_ofNat, hr]
  linear_combination (-(r3 ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * r3_sq

/-- Multiplication by `ρ` as a permutation of the lattice `Ω_ρℤ[ρ]`. -/
noncomputable def mulRho : equianharmonic.lattice ≃ equianharmonic.lattice where
  toFun l := ⟨rho * l, rho_mul_mem_lattice l.2⟩
  invFun l := ⟨rho * (rho * l), rho_mul_mem_lattice (rho_mul_mem_lattice l.2)⟩
  left_inv l := Subtype.ext (by simp only; linear_combination (l : ℂ) * rho_cube)
  right_inv l := Subtype.ext (by simp only; linear_combination (l : ℂ) * rho_cube)

lemma rho_ne_one : rho ≠ 1 := by
  intro h; have := congrArg Complex.re h; simp [rho, r3] at this; norm_num at this

/-- **`g₂(Ω_ρℤ[ρ]) = 0`**: `G₄` vanishes because `(ρl)⁻⁴ = ρ⁻¹ l⁻⁴` and `ρ ≠ 1`. -/
lemma g₂_equianharmonic : equianharmonic.g₂ = 0 := by
  have h : equianharmonic.G 4 = rho⁻¹ * equianharmonic.G 4 := by
    conv_lhs => rw [PeriodPair.G, ← mulRho.tsum_eq]
    rw [PeriodPair.G, ← tsum_mul_left]
    congr with l
    simp only [mulRho, Equiv.coe_fn_mk, mul_pow, mul_inv]
    rw [show rho ^ 4 = rho by linear_combination rho * rho_cube]
  have hG : equianharmonic.G 4 = 0 := by
    have h1 : (1 - rho⁻¹) * equianharmonic.G 4 = 0 := by linear_combination h
    refine (mul_eq_zero.mp h1).resolve_left ?_
    rw [sub_eq_zero, eq_comm, inv_eq_one]; exact rho_ne_one
  simp [PeriodPair.g₂, hG]

lemma g₂_equianharmonic_isAlgebraic : IsAlgebraic ℚ equianharmonic.g₂ := by
  rw [g₂_equianharmonic]; exact isAlgebraic_zero

/-! ## Quasi-periods and `Λ(E^♮)` -/

/-- `η(Ω_ρ) = 2π/(√3 Ω_ρ)`. -/
noncomputable def etaRho : ℂ := 2 * Real.pi / (r3 * omegaRho)

/-- `η((m + nρ)Ω_ρ) = (m + nρ̄) η(Ω_ρ)`. -/
noncomputable def etaR (m n : ℤ) : ℂ := ((m : ℂ) + n * rhoBar) * etaRho

/-- `(z, w) ∈ Λ(E^♮)`, for the coordinates with `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))`: either `z = mω₁ + nω₂` is a
period and `w − η(z) ∈ ℚ̄`, or `exp_E(z)` is an algebraic affine point and `w − ζ(z) ∈ ℚ̄`. Here `ζ` is
`LSG.Weierstrass.zeta`, the standard series, with `ζ' = −℘` proved there (`hasDerivAt_zeta`). -/
def LogNat (L : PeriodPair) (eta : ℤ → ℤ → ℂ) (z w : ℂ) : Prop :=
  (∃ m n : ℤ, z = m * L.ω₁ + n * L.ω₂ ∧ IsAlgebraic ℚ (w - eta m n)) ∨
    (z ∉ L.lattice ∧ IsAlgebraic ℚ (L.weierstrassP z) ∧ IsAlgebraic ℚ (L.derivWeierstrassP z) ∧
      IsAlgebraic ℚ (w - LSG.Weierstrass.zeta L z))

/-! ## Small facts used by the general proof (`CM4E/Gen/MXGen.lean`) -/

lemma isAlg_zero_of {x : ℂ} (h : x = 0) : IsAlgebraic ℚ x := h ▸ isAlgebraic_zero

lemma isAlgebraic_r3 : IsAlgebraic ℚ r3 := by simpa [r3] using isAlgebraic_sqrt_nat 3

lemma etaRho_mul : etaRho * omegaRho = 2 * r3 * Real.pi / 3 := by
  have h3 := r3_sq
  have hO := omegaRho_ne_zero
  have hr := r3_ne_zero
  rw [etaRho]
  field_simp
  linear_combination (-1 : ℂ) * h3

lemma etaRho_ne_zero : etaRho ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [etaRho]
  exact div_ne_zero (mul_ne_zero two_ne_zero hpi) (mul_ne_zero r3_ne_zero omegaRho_ne_zero)

end CM4E.MX
