/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MG
import CM4E.MX

/-!
# The two CM lattices of the paper

* `latI`: `ϖ ℤ[i]` (`y² = 4x³ − 4x`), `η₀ = η(ϖ) = π/ϖ`.
* `latRho`: `Ω_ρ ℤ[ρ]` (`y² = 4x³ − 4`), `η₀ = η(Ω_ρ) = 2π/(√3 Ω_ρ)`.

Soundness fact (not checked by Lean): `η₀` is the quasi-period `η(ω)` of the Weierstrass `ζ` of the lattice, and
`η(αλ) = ᾱ η(λ)` (`κ₁ = 0` for these two curves). Legendre's relation `ω η₀ (α − ᾱ) = 2πi` is proved below. The
quasi-period values were checked numerically against `LSG.Weierstrass.zeta` (`reviews/REFEREE_HYP_MX.md`).
-/

open Complex

namespace CM4E.Gen

/-- `ϖ ℤ[i]`. -/
noncomputable def latI : CMLattice where
  pp := lemniscatic
  ω := varpi
  α := I
  η₀ := Real.pi / varpi
  p := -1
  q := 0
  hω₁ := rfl
  hω₂ := rfl
  hquad := by push_cast; simp
  him := by simp
  legendre := by
    have hv := varpi_ne_zero'
    simp only [Complex.conj_I]
    field_simp
    ring

/-- `Ω_ρ ℤ[ρ]`. -/
noncomputable def latRho : CMLattice where
  pp := MX.equianharmonic
  ω := omegaRho
  α := MX.rho
  η₀ := MX.etaRho
  p := -1
  q := -1
  hω₁ := rfl
  hω₂ := rfl
  hquad := by
    simp only [MX.rho]; push_cast
    ring_nf; rw [Complex.I_sq, MX.r3_sq]; ring
  him := by
    simp [MX.rho, MX.r3]
  legendre := by
    have hO := MX.omegaRho_ne_zero
    have hr := MX.r3_ne_zero
    have hc : starRingEnd ℂ MX.rho = (-1 - I * MX.r3) / 2 := by
      simp [MX.rho, MX.r3, map_div₀, Complex.conj_ofReal, map_ofNat]
      ring
    rw [hc, MX.etaRho, MX.rho]
    field_simp
    ring

end CM4E.Gen
