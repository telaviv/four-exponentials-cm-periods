/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Ext.Bridge.Lemniscatic
import CM4E.Ext.SchneiderMain
import CM4E.MainQi
import CM4E.TwoThree
import CM4E.MainNat
import CM4E.MX
import CM4E.Gen.Instances

/-!
# The main theorems with every hypothesis except W88 discharged

`CM4E/Ext/` (a copy of the needed part of the sibling project `lean_lsg`; see `CM4E/Ext/PROVENANCE.md`) proves, with
standard axioms only:
* `g₂(ϖℤ[i])` is algebraic (`CM4E.Ext.Bridge.isAlgebraic_g₂`; it proves `g₂ = 4` from the Γ-formula for `ϖ`);
* Schneider's theorem: a nonzero period of a lattice with algebraic `g₂, g₃` is transcendental, and so is the period
  divided by `π` (`CM4E.Ext.Schneider.period_transcendental`, `CM4E.Ext.Bridge.irrational_varpi_div_pi_of`).

`CM4E.Ext.LemniscateIndep.varpi` has the same body as `CM4E.varpi`, so the two are equal by `rfl` (used implicitly
below). This file feeds these facts into the conditional theorems. What remains assumed is the hyperplane hypothesis
`hW` (W88 §5d for the relevant group model) and, for Theorem MX, the inputs about the second curve (`hg₂'`, `hg₃'`,
`hΓ`, `hM`).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Final

/-- `g₂(ϖℤ[i]) ∈ ℚ̄` (`CM4E/Ext`). -/
theorem hg₂ : IsAlgebraic ℚ lemniscatic.g₂ := CM4E.Ext.Bridge.isAlgebraic_g₂ lemniscatic rfl rfl

/-- `ϖ/π ∉ ℚ` (`CM4E/Ext`: Schneider). -/
theorem hS : Irrational (varpi / Real.pi) := CM4E.Ext.Bridge.irrational_varpi_div_pi_of lemniscatic rfl rfl

/-- `ϖ` is transcendental (`CM4E/Ext`: Schneider). -/
theorem hT : Transcendental ℚ (varpi : ℂ) :=
  CM4E.Ext.Schneider.period_transcendental hg₂ g₃_lemniscatic_isAlgebraic lemniscatic.ω₁_mem_lattice
    (by exact_mod_cast varpi_ne_zero)

/-- **Theorem 1(b) for `c ∈ ℚ(i)ˣ`**: four exponentials at `t = ((p + qi)/D)·ϖ/π`, assuming only W88 §5d for
`G_m⁴ × E_i`. -/
theorem fourExpAt_Qi (hW : Thm11Kappa lemniscatic 4)
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (MainQi.tExp p q D) :=
  MainQi.fourExpAt_Qi hW hg₂ hS p q D hD hpq

/-- **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic**, assuming only W88 §5d for `G_m⁴ × E_i`. -/
theorem two_three (hW : Thm11Kappa lemniscatic 4) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 3))) :=
  TwoThree.two_three hW hg₂ hS

/-- **Theorem 1(a) for `c ∈ ℚ(i)ˣ`**: four exponentials at `t = Dϖ/(p + qi)`, assuming only W88 §5d for
`G_m⁸ × Q''`. -/
theorem fourExpAt_varpi (hW : MainNat.Thm11KappaNat)
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (MainNat.tN p q D) :=
  MainNat.main hW hg₂ hT p q D hD hpq

/-- **`2^ϖ` and `3^ϖ` are not both algebraic**, assuming only W88 §5d for `G_m⁸ × Q''`. -/
theorem two_three_varpi (hW : MainNat.Thm11KappaNat) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 3))) :=
  MainNat.two_three_varpi hW hg₂ hT

/-- **Theorem MX, `K`-form**, with `hg₂` for `ϖℤ[i]` discharged. -/
theorem mx (hW : MX.Thm11KappaMX)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi))
    (b : Fin 4 → ℚ) (hb : b ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : MX.LogNat lemniscatic etaLem zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (MX.beta b * MX.etaRho) = (wX + wY + t) * varpi) :
    ∃ x ∈ MX.K, ∃ x' ∈ MX.K, zX + zY + a = x * varpi + x' * omegaRho :=
  MX.main hW hg₂ hg₂' hg₃' hΓ hM b hb zX wX zY wY a t hX hY ha ht hrel

/-! ## Theorem 1 for every algebraic `c` (general `K`; `CM4E/Gen/`) -/

/-- **Theorem 1(a) for `Ω = ϖ` and every algebraic `c ≠ 0`**: `FourExpAt (cϖ)`, assuming only W88 §5d for the groups
`G_m^{2n} × Q''` (`Gen.Thm11KappaMGn Gen.latI`). -/
theorem fourExpAt_varpi_all (hW : Gen.Thm11KappaMGn Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) : FourExpAt (c * varpi) :=
  Gen.fourExpAt_MGn Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic hT c hc hc0

/-- **Theorem 1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`**: `FourExpAt (cϖ/π)`, assuming only W88 §5d for the groups
`G_m^{2n} × A''` (`Gen.Thm11KappaMG Gen.latI`). -/
theorem fourExpAt_varpi_div_pi_all (hW : Gen.Thm11KappaMG Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) : FourExpAt (c * varpi / Real.pi) :=
  Gen.fourExpAt_MG Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) c hc hc0

/-- **Theorem 1(a) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**: `FourExpAt (cΩ_ρ)`, assuming W88 §5d
(`Gen.Thm11KappaMGn Gen.latRho`) and that `g₂, g₃` of `Ω_ρ ℤ[ρ]` are algebraic. -/
theorem fourExpAt_omegaRho_all (hW : Gen.Thm11KappaMGn Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : FourExpAt (c * omegaRho) :=
  Gen.fourExpAt_MGn Gen.latRho hW hg₂' hg₃'
    (CM4E.Ext.Schneider.period_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero) c hc hc0

/-- **Theorem 1(b) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**: `FourExpAt (cΩ_ρ/π)`, assuming W88 §5d
(`Gen.Thm11KappaMG Gen.latRho`) and that `g₂, g₃` of `Ω_ρ ℤ[ρ]` are algebraic. -/
theorem fourExpAt_omegaRho_div_pi_all (hW : Gen.Thm11KappaMG Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : FourExpAt (c * omegaRho / Real.pi) :=
  Gen.fourExpAt_MG Gen.latRho hW hg₂' hg₃'
    (CM4E.Ext.Schneider.period_div_pi_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero) c hc hc0

/-- **`2^{Ω_ρ}` and `3^{Ω_ρ}` are not both algebraic**, assuming W88 §5d and `g₂, g₃(Ω_ρ ℤ[ρ]) ∈ ℚ̄`. -/
theorem two_three_omegaRho (hW : Gen.Thm11KappaMGn Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((omegaRho : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((omegaRho : ℂ) * Complex.log 3))) := by
  have h := fourExpAt_omegaRho_all hW hg₂' hg₃' 1 isAlgebraic_one one_ne_zero (Complex.log 2)
    (Complex.log 3) (by simpa using log_mem_logAlg 2 two_ne_zero)
    (by simpa using log_mem_logAlg 3 three_ne_zero) linearIndependent_two_three
  simpa using h

end CM4E.Final
