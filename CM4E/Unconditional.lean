/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CM4E.Final
import CM4E.Bridge.Results
import LSG.W88.Main
import LSG.W88.K5dMain

/-!
# Unconditional results: W88 discharged by `lean_lsg`

The sibling project `lean_lsg` (Lake path dependency `../lean_lsg`) proves Waldschmidt's subgroup theorem with period
term (W88, Thm 4.1, under (NR)) for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` (`LSG.W88.theorem41Abelian`) and deduces from it
the §5d statement for `G_m^{d₁} × E`, verbatim our hypothesis `Thm11Kappa` (`LSG.W88.thm11Kappa`, stated for a verbatim
copy `LSG.W88.MStarCopy.Thm11Kappa` of `CM4E.Waldschmidt.Thm11Kappa`; the two unfold to the same term). Hence the
results that need only `Thm11Kappa lemniscatic 4` hold with **no hypotheses**:

* `fourExpAt_Qi`: the four exponentials statement at `t = ((p + qi)/D)·ϖ/π` for every `p + qi ∈ ℚ(i)ˣ`;
* `two_three`: `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic.

`lean_lsg` also proves the §5d statement for the standard model of `G_a^{d₀} × G_m^{d₁} × E^r`, one curve repeated, for
every period pair with algebraic invariants (`LSG.W88.hypStdCMAt`, stated for a verbatim copy of our
`CM4E.Bridge.HypStdCMAt`). Through the bridges of `CM4E/Bridge/` (proved) this gives, with no form of W88 assumed:

* `fourExpAt_varpi_div_pi_all`: **Theorem 1(b) for `Ω = ϖ`**: `FourExpAt (cϖ/π)` for every algebraic `c ≠ 0`
  (e.g. `2^{cϖ/π}, 3^{cϖ/π}` are not both algebraic);
* `fourExpAt_omegaRho_div_pi_all`: Theorem 1(b) for `Ω = Ω_ρ`, assuming only that `g₂, g₃(Ω_ρℤ[ρ])` are algebraic;
* `mg1_varpi_abc`: Corollary MG1 (one of `e^{aπ²}, e^{bπϖ}, e^{cπ²/ϖ}` is transcendental), assuming the named input
  `Gen.NotLtilde Gen.latI` (Wüstholz);
* `mg3_varpi`: Corollary MG3, assuming Baker's theorem (`Gen.Baker3`).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Unconditional

/-- **W88 §5d for `G_m^{d₁} × E`**, proved in `lean_lsg`. -/
theorem thm11Kappa (L : PeriodPair) (d₁ : ℕ) : Thm11Kappa L d₁ :=
  LSG.W88.thm11Kappa L d₁

/-- **Theorem 1(b) for `c ∈ ℚ(i)ˣ`, unconditionally**: `FourExpAt (((p + qi)/D)·ϖ/π)`. -/
theorem fourExpAt_Qi (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (MainQi.tExp p q D) :=
  Final.fourExpAt_Qi (thm11Kappa lemniscatic 4) p q D hD hpq

/-- **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic** (no hypotheses). -/
theorem two_three :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 3))) :=
  Final.two_three (thm11Kappa lemniscatic 4)

/-- W88 §5d for `G_a^{d₀} × G_m^{d₁} × E^r` (one curve repeated), proved in `lean_lsg`. -/
theorem hypStdCMAt (L : PeriodPair) (d : ℕ) : Bridge.HypStdCMAt L d :=
  LSG.W88.hypStdCMAt L d

/-- **Theorem 1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`, unconditionally**: `FourExpAt (cϖ/π)`. -/
theorem fourExpAt_varpi_div_pi_all (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * varpi / Real.pi) :=
  Bridge.fourExpAt_varpi_div_pi_all (hypStdCMAt lemniscatic 0) c hc hc0

/-- **Theorem 1(b) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**, assuming only `g₂, g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`. -/
theorem fourExpAt_omegaRho_div_pi_all (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂)
    (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * omegaRho / Real.pi) :=
  Bridge.fourExpAt_omegaRho_div_pi_all (hypStdCMAt MX.equianharmonic 0) hg₂' hg₃' c hc hc0

/-- **Corollary MG1 for `ϖ`**: one of `e^{aπ²}, e^{bπϖ}, e^{cπ²/ϖ}` is transcendental (`a, b, c ∈ ℚ̄ˣ`), assuming only
the named input `Gen.NotLtilde Gen.latI` (Wüstholz 1989). -/
theorem mg1_varpi_abc (hNot : Gen.NotLtilde Gen.latI) (a b c : ℂ) (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0)
    (hb : IsAlgebraic ℚ b) (hb0 : b ≠ 0) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (b * Real.pi * varpi)) ∧
      IsAlgebraic ℚ (Complex.exp (c * Real.pi ^ 2 / varpi))) :=
  Bridge.mg1_varpi_abc (hypStdCMAt lemniscatic 2) hNot a b c ha ha0 hb hb0 hc hc0

/-- **Corollary MG3 for `ϖ`**, assuming only Baker's theorem. -/
theorem mg3_varpi (hBaker : Gen.Baker3) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (hπω : IsAlgebraic ℚ (Complex.exp (c * Real.pi * varpi))) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x))
    (hind : LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]) :
    Transcendental ℚ (Complex.exp (varpi / Real.pi * x)) :=
  Bridge.mg3_varpi (hypStdCMAt lemniscatic 2) hBaker c hc hc0 hπ2 hπω x hx hind

end CM4E.Unconditional
