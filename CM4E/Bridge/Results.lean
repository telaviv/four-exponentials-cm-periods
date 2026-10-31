/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Final
import CM4E.Bridge.SMG

/-!
# Results conditional only on the standard-model hypothesis `HypStd`

`HypStd` (`CM4E/Bridge/Std.lean`) is W88 §5d for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m`, to be supplied by `lean_lsg` from
its proved Theorem 4.1. Through the bridges `thm11KappaMG_of_std`, `thm11KappaSMG_of_std` (all proved), Theorem 1(b) for
every algebraic `c` and Corollaries MG1, MG3 need no other form of W88:

* `fourExpAt_varpi_div_pi_all`: `FourExpAt (cϖ/π)` for every algebraic `c ≠ 0`;
* `fourExpAt_omegaRho_div_pi_all`: `FourExpAt (cΩ_ρ/π)` (with `g₂, g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`);
* `mg1_varpi`: one of `e^{π²}, e^{πϖ}, e^{π²/ϖ}` is transcendental (with `Gen.NotLtilde`);
* `mg3_varpi` (with Baker's theorem).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Bridge

lemma int_I : ∃ a c : ℤ, (Gen.latI.α) ^ 2 = a + c * Gen.latI.α :=
  ⟨-1, 0, by simp [Gen.latI]⟩

lemma int_rho : ∃ a c : ℤ, (Gen.latRho.α) ^ 2 = a + c * Gen.latRho.α :=
  ⟨-1, -1, by have h := Gen.latRho.hquad; simp only [Gen.latRho] at h ⊢; rw [h]; push_cast; ring⟩

/-- **Theorem 1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`**, from `HypStd`. -/
theorem fourExpAt_varpi_div_pi_all (hS : HypStd) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * varpi / Real.pi) :=
  Final.fourExpAt_varpi_div_pi_all (thm11KappaMG_of_std hS Gen.latI int_I) c hc hc0

/-- **Theorem 1(b) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**, from `HypStd` and `g₂, g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`. -/
theorem fourExpAt_omegaRho_div_pi_all (hS : HypStd)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : FourExpAt (c * omegaRho / Real.pi) :=
  Final.fourExpAt_omegaRho_div_pi_all (thm11KappaMG_of_std hS Gen.latRho int_rho) hg₂' hg₃' c hc hc0

/-- **Corollary MG1 for `ϖ`**, from `HypStd` and `Gen.NotLtilde Gen.latI`. -/
theorem mg1_varpi (hS : HypStd) (hNot : Gen.NotLtilde Gen.latI) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (Real.pi * varpi)) ∧
      IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2 / varpi))) :=
  Final.mg1_varpi (thm11KappaSMG_of_std hS Gen.latI int_I) hNot

/-- **Corollary MG3 for `ϖ`**, from `HypStd` and Baker's theorem. -/
theorem mg3_varpi (hS : HypStd) (hBaker : Gen.Baker3) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (hπω : IsAlgebraic ℚ (Complex.exp (c * Real.pi * varpi))) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x))
    (hind : LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]) :
    Transcendental ℚ (Complex.exp (varpi / Real.pi * x)) :=
  Final.mg3_varpi (thm11KappaSMG_of_std hS Gen.latI int_I) hBaker c hc hc0 hπ2 hπω x hx hind

end CM4E.Bridge
