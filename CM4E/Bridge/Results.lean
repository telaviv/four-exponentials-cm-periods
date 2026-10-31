/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Final
import CM4E.Bridge.SMG

/-!
# Results conditional only on the standard-model hypothesis `HypStdCM`

`HypStdCMAt L d` (`CM4E/Bridge/Std.lean`) is W88 §5d for `G_a^d × G_m^{d₁} × E^r` (`E` the curve of `L`), to be supplied by `lean_lsg` from
its proved Theorem 4.1. Through the bridges `thm11KappaMG_of_std`, `thm11KappaSMG_of_std` (all proved), Theorem 1(b) for
every algebraic `c` needs only the case `d = 0`, Corollaries MG1, MG3 the case `d = 2`:

* `fourExpAt_varpi_div_pi_all`: `FourExpAt (cϖ/π)` for every algebraic `c ≠ 0`;
* `fourExpAt_omegaRho_div_pi_all`: `FourExpAt (cΩ_ρ/π)` (with `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`; `g₂ = 0` is proved);
* `mg1_varpi`: one of `e^{π²}, e^{πϖ}, e^{π²/ϖ}` is transcendental (with `Gen.NotLtilde`);
* `mg3_varpi` (with Baker's theorem).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Bridge

lemma int_I : ∃ a c : ℤ, (Gen.latI.α) ^ 2 = a + c * Gen.latI.α :=
  ⟨-1, 0, by simp [Gen.latI]⟩

lemma int_rho : ∃ a c : ℤ, (Gen.latRho.α) ^ 2 = a + c * Gen.latRho.α :=
  ⟨-1, -1, by have h := Gen.latRho.hquad; simp only [Gen.latRho] at h ⊢; rw [h]; push_cast; ring⟩

/-- **Theorem 1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`**, from `HypStdCM`. -/
theorem fourExpAt_varpi_div_pi_all (hS : HypStdCMAt lemniscatic 0) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * varpi / Real.pi) :=
  Final.fourExpAt_varpi_div_pi_all (thm11KappaMG_of_std Gen.latI hS int_I) c hc hc0

/-- **Theorem 1(b) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**, from `HypStdCM` and `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`. -/
theorem fourExpAt_omegaRho_div_pi_all (hS : HypStdCMAt MX.equianharmonic 0)
    (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : FourExpAt (c * omegaRho / Real.pi) :=
  Final.fourExpAt_omegaRho_div_pi_all (thm11KappaMG_of_std Gen.latRho hS int_rho) hg₃' c hc hc0

/-- **Corollary MG1 for `ϖ`**, from `HypStdCM` and `Gen.NotLtilde Gen.latI`. -/
theorem mg1_varpi (hS : HypStdCMAt lemniscatic 2) (hNot : Gen.NotLtilde Gen.latI) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (Real.pi * varpi)) ∧
      IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2 / varpi))) :=
  Final.mg1_varpi (thm11KappaSMG_of_std Gen.latI hS int_I) hNot

/-- **Corollary MG3 for `ϖ`**, from `HypStdCM` and Baker's theorem. -/
theorem mg3_varpi (hS : HypStdCMAt lemniscatic 2) (hBaker : Gen.Baker3) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (hπω : IsAlgebraic ℚ (Complex.exp (c * Real.pi * varpi))) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x))
    (hind : LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]) :
    Transcendental ℚ (Complex.exp (varpi / Real.pi * x)) :=
  Final.mg3_varpi (thm11KappaSMG_of_std Gen.latI hS int_I) hBaker c hc hc0 hπ2 hπω x hx hind

/-- **Corollary MG1 for `ϖ`** (main-text form, `a, b, c ∈ ℚ̄ˣ`): one of `e^{aπ²}, e^{bπϖ}, e^{cπ²/ϖ}` is transcendental.
From `HypStdCMAt lemniscatic 2` and `Gen.NotLtilde Gen.latI`. -/
theorem mg1_varpi_abc (hS : HypStdCMAt lemniscatic 2) (hNot : Gen.NotLtilde Gen.latI) (a b c : ℂ)
    (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) (hb : IsAlgebraic ℚ b) (hb0 : b ≠ 0) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (b * Real.pi * varpi)) ∧
      IsAlgebraic ℚ (Complex.exp (c * Real.pi ^ 2 / varpi))) :=
  Gen.mg1 Gen.latI (thm11KappaSMG_of_std Gen.latI hS int_I) Final.hg₂ g₃_lemniscatic_isAlgebraic Final.hT
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hNot a b c ha ha0 hb hb0 hc hc0

end CM4E.Bridge
