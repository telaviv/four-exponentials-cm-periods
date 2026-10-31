/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CM4E.Final
import LSG.W88.Main

/-!
# Unconditional results: W88 discharged by `lean_lsg`

The sibling project `lean_lsg` (Lake path dependency `../lean_lsg`) proves Waldschmidt's subgroup theorem with period
term (W88, Thm 4.1, under (NR)) for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` (`LSG.W88.theorem41Abelian`) and deduces from it
the §5d statement for `G_m^{d₁} × E`, verbatim our hypothesis `Thm11Kappa` (`LSG.W88.thm11Kappa`, stated for a verbatim
copy `LSG.W88.MStarCopy.Thm11Kappa` of `CM4E.Waldschmidt.Thm11Kappa`; the two unfold to the same term). Hence the
results that need only `Thm11Kappa lemniscatic 4` hold with **no hypotheses**:

* `fourExpAt_Qi`: the four exponentials statement at `t = ((p + qi)/D)·ϖ/π` for every `p + qi ∈ ℚ(i)ˣ`;
* `two_three`: `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic.
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

end CM4E.Unconditional
