/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.MainQi

/-!
# Headline instance: `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic (conditional)

From `CM4E.MainQi.main` with `c = 1`, `a = log 2`, `b = log 3`; the only extra input is the `ℚ`-independence of
`log 2, log 3` (`CM4E.linearIndependent_two_three`).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.TwoThree

/-- **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic**, conditional on the published theorem `Thm11Kappa` for
`G_m⁴ × E_i`, on `g₂(ϖℤ[i]) ∈ ℚ̄`, and on the irrationality of `ϖ/π`. -/
theorem two_three (hW : Thm11Kappa lemniscatic 4)
    (hg₂ : IsAlgebraic ℚ lemniscatic.g₂) (hS : Irrational (varpi / Real.pi)) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 3))) := by
  have ht : MainQi.tExp 1 0 1 = (varpi / Real.pi : ℂ) := by simp [MainQi.tExp]
  rw [← ht]
  exact MainQi.main hW hg₂ hS 1 0 1 one_pos (Or.inl one_ne_zero) (Complex.log 2) (Complex.log 3)
    (by simpa using log_mem_logAlg 2 two_ne_zero) (by simpa using log_mem_logAlg 3 three_ne_zero)
    linearIndependent_two_three

end CM4E.TwoThree
