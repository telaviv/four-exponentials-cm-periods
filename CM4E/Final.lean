/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import LSG.Bridge.Lemniscatic
import LSG.SchneiderMain
import CM4E.MainQi
import CM4E.TwoThree
import CM4E.MainNat
import CM4E.MX

/-!
# The main theorems with every hypothesis except W88 discharged

The sibling project `lean_lsg` (library `LSG`, a Lake path dependency) proves, with standard axioms only:
* `g₂(ϖℤ[i])` is algebraic (`LSG.Bridge.isAlgebraic_g₂`; it proves `g₂ = 4` from the Γ-formula for `ϖ`);
* Schneider's theorem: a nonzero period of a lattice with algebraic `g₂, g₃` is transcendental, and so is the period
  divided by `π` (`LSG.Schneider.period_transcendental`, `LSG.Bridge.irrational_varpi_div_pi_of`).

`LSG.LemniscateIndep.varpi` has the same body as `CM4E.varpi`, so the two are equal by `rfl`.

This file feeds these into the conditional theorems. What remains assumed is the hyperplane hypothesis `hW` (W88 §5d
for the relevant group model), and, for Theorem MX, the inputs about the second curve (`hg₂'`, `hg₃'`, `hΓ`, `hM`).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Final

lemma varpi_eq : varpi = LSG.LemniscateIndep.varpi := rfl

/-- `g₂(ϖℤ[i]) ∈ ℚ̄` (lean_lsg). -/
theorem hg₂ : IsAlgebraic ℚ lemniscatic.g₂ := LSG.Bridge.isAlgebraic_g₂ lemniscatic rfl rfl

/-- `ϖ/π ∉ ℚ` (lean_lsg: Schneider). -/
theorem hS : Irrational (varpi / Real.pi) := LSG.Bridge.irrational_varpi_div_pi_of lemniscatic rfl rfl

/-- `ϖ` is transcendental (lean_lsg: Schneider). -/
theorem hT : Transcendental ℚ (varpi : ℂ) :=
  LSG.Schneider.period_transcendental hg₂ g₃_lemniscatic_isAlgebraic lemniscatic.ω₁_mem_lattice
    (by exact_mod_cast varpi_ne_zero)

/-- **Theorem 1(b) for `c ∈ ℚ(i)ˣ`**: four exponentials at `t = Dϖ/((p + qi)π)`, assuming only W88 §5d for
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
    (hΓ : Transcendental ℚ ((varpi : ℂ) * MX.OmegaRho / Real.pi))
    (hM : Transcendental ℚ ((MX.OmegaRho : ℂ) / varpi))
    (b : Fin 4 → ℚ) (hb : b ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : MX.LogNat lemniscatic MX.etaI zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (MX.beta b * MX.etaRho) = (wX + wY + t) * varpi) :
    ∃ x ∈ MX.K, ∃ x' ∈ MX.K, zX + zY + a = x * varpi + x' * MX.OmegaRho :=
  MX.main hW hg₂ hg₂' hg₃' hΓ hM b hb zX wX zY wY a t hX hY ha ht hrel

end CM4E.Final
