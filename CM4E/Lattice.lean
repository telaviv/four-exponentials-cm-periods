/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs

/-!
# The lemniscatic lattice `ϖ ℤ[i]`

`CM4E.lemniscatic : PeriodPair` is the period pair `(ϖ, iϖ)` (Mathlib's `PeriodPair`, with its Weierstrass `℘`).
Its curve is `y² = 4x³ − 4x`, i.e. `g₂ = 4`, `g₃ = 0`. Here `g₃ = 0` is proved (`g₃_lemniscatic`); `g₂ = 4` is proved in
`LSG.LemniscateIndep` and used in `CM4E/Final.lean`. `etaLem` records the quasi-periods used by the group
models.
-/

open Complex Real

namespace CM4E

lemma varpi_pos : 0 < varpi := by
  unfold varpi
  have h1 : 0 < Real.Gamma (1 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  positivity

lemma varpi_ne_zero : varpi ≠ 0 := varpi_pos.ne'

lemma varpi_ne_zero' : (varpi : ℂ) ≠ 0 := by exact_mod_cast varpi_ne_zero

/-- The quasi-period `η((m + ni)ϖ) = (m − ni) π/ϖ` of `ϖℤ[i]` (Legendre's relation `ϖ η(ϖ) = π` and
`η(iλ) = −iη(λ)`). It enters the group models `gmQ`, `gmMGn`, `gmXG` as a stated soundness fact, not as a Lean proof. -/
noncomputable def etaLem (m n : ℤ) : ℂ := ((m : ℂ) - n * I) * (Real.pi / varpi)

/-- `ϖ` and `iϖ` are linearly independent over `ℝ`. -/
lemma linearIndependent_varpi : LinearIndependent ℝ ![(varpi : ℂ), I * varpi] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  exact ⟨by simpa [varpi_ne_zero] using hre, by simpa [varpi_ne_zero] using him⟩

/-- The period pair `(ϖ, iϖ)` of the lemniscatic curve `y² = 4x³ − 4x`. -/
noncomputable def lemniscatic : PeriodPair where
  ω₁ := varpi
  ω₂ := I * varpi
  indep := linearIndependent_varpi

/-- Gaussian-integer multiples of `ϖ` lie in the lattice. -/
lemma gaussian_mem_lattice (p q : ℤ) : ((p : ℂ) + q * I) * varpi ∈ lemniscatic.lattice := by
  have h1 : (varpi : ℂ) ∈ lemniscatic.lattice := lemniscatic.ω₁_mem_lattice
  have h2 : I * (varpi : ℂ) ∈ lemniscatic.lattice := lemniscatic.ω₂_mem_lattice
  have : ((p : ℂ) + q * I) * varpi = p • (varpi : ℂ) + q • (I * varpi) := by
    simp [zsmul_eq_mul]; ring
  rw [this]
  exact add_mem (Submodule.smul_mem _ p h1) (Submodule.smul_mem _ q h2)

/-- `iΛ = Λ` for `Λ = ϖℤ[i]`. -/
lemma I_mul_mem_lattice {x : ℂ} (hx : x ∈ lemniscatic.lattice) : I * x ∈ lemniscatic.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  refine PeriodPair.mem_lattice.mpr ⟨-n, m, ?_⟩
  simp only [lemniscatic]; push_cast; ring_nf; rw [Complex.I_sq]; ring

/-- Multiplication by `i` as a permutation of the lattice `ϖℤ[i]`. -/
noncomputable def mulI : lemniscatic.lattice ≃ lemniscatic.lattice where
  toFun l := ⟨I * l, I_mul_mem_lattice l.2⟩
  invFun l := ⟨-I * l, by
    have h := I_mul_mem_lattice (I_mul_mem_lattice (I_mul_mem_lattice l.2))
    convert h using 1; ring_nf; rw [show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]; ring⟩
  left_inv l := by ext; simp only; ring_nf; rw [Complex.I_sq]; ring
  right_inv l := by ext; simp only; ring_nf; rw [Complex.I_sq]; ring

/-- **`g₃(ϖℤ[i]) = 0`**: `G₆` vanishes because `(il)⁻⁶ = −l⁻⁶`. -/
lemma g₃_lemniscatic : lemniscatic.g₃ = 0 := by
  have hG : lemniscatic.G 6 = 0 := by
    rw [← CharZero.eq_neg_self_iff, PeriodPair.G, ← tsum_neg, ← mulI.tsum_eq]
    congr with l
    simp only [mulI, Equiv.coe_fn_mk, mul_pow]
    rw [show I ^ 6 = -1 by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]; norm_num]
    rw [neg_one_mul, inv_neg]
  simp [PeriodPair.g₃, hG]

lemma g₃_lemniscatic_isAlgebraic : IsAlgebraic ℚ lemniscatic.g₃ := by
  rw [g₃_lemniscatic]; exact isAlgebraic_zero

end CM4E
