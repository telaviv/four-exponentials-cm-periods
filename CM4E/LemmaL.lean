/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Lemma L (algebraic part): two parallel periods

Paper `pilot_thmM/paper/paper.tex`, proof of Proposition D, Step 1 (`MX_DIRECT.md` §5).

With `ϖ η_i = π` and `Ω_ρ η_ρ = 2π/√3` (Legendre on `E_i` and `E_ρ`), the vectors
`w₁ = (ϖ, β η_ρ)` and `w₂ = (Ω_ρ, β (2/√3) η_i)` are parallel, and a multiple `s w₁` whose first
(resp. second) coordinate lies in `Kϖ + KΩ_ρ` (resp. `Kη_ρ + Kη_i`) is a `K`-combination of
`w₁, w₂`. Here only the algebra is formalised: the Legendre relations enter through the single
hypothesis `hleg : vp * ei * q = om * er`, where `q = 2/√3`.
-/

namespace CM4E.LemmaL

variable {F : Type*} [Field F]

/-- `w₁ = (ϖ, β η_ρ)`. -/
def w₁ (vp er β : F) : F × F := (vp, β * er)

/-- `w₂ = (Ω_ρ, β q η_i)`. -/
def w₂ (om ei β q : F) : F × F := (om, β * q * ei)

/-- `w₁` and `w₂` are parallel: their `2 × 2` determinant vanishes. -/
theorem det_eq_zero {vp om ei er β q : F} (hleg : vp * ei * q = om * er) :
    (w₁ vp er β).1 * (w₂ om ei β q).2 - (w₁ vp er β).2 * (w₂ om ei β q).1 = 0 := by
  simp only [w₁, w₂]
  linear_combination β * hleg

/-- **Case `L = 0` or `L = ℂ(0,1)`.** If the first coordinate of `s w₁` is `x ϖ + x' Ω_ρ`, then
`s w₁ = x w₁ + x' w₂`. -/
theorem first_coord {vp om ei er β q s x x' : F} (hvp : vp ≠ 0) (hleg : vp * ei * q = om * er)
    (h : s * vp = x * vp + x' * om) :
    s • w₁ vp er β = x • w₁ vp er β + x' • w₂ om ei β q := by
  simp only [w₁, w₂, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨by linear_combination h, mul_left_cancel₀ hvp ?_⟩
  linear_combination (β * er) * h - (x' * β) * hleg

/-- **Case `L = ℂ(1,0)`.** If the second coordinate of `s w₁` is `β (x η_ρ + x' η_i)`, then
`s w₁ = x w₁ + (x'/q) w₂`. -/
theorem second_coord {vp om ei er β q s x x' : F} (her : er ≠ 0) (hq : q ≠ 0)
    (hleg : vp * ei * q = om * er) (h : s * er = x * er + x' * ei) :
    s • w₁ vp er β = x • w₁ vp er β + (x' / q) • w₂ om ei β q := by
  simp only [w₁, w₂, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  have key : s * vp * q = x * vp * q + x' * om := by
    refine mul_left_cancel₀ her ?_
    linear_combination (q * vp) * h + x' * hleg
  constructor
  · field_simp
    linear_combination key
  · field_simp
    linear_combination β * h

end CM4E.LemmaL
