/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Statements: four exponentials at CM periods

The elementary definitions used in the statements of the main theorems (no elliptic curves appear in them).
Read this file first.

* `CM4E.logAlg` : `𝓛 = {ℓ ∈ ℂ | exp ℓ is algebraic}`, the logarithms of nonzero algebraic
  numbers.
* `CM4E.varpi` : the real period `ϖ = Γ(1/4)² / (2√(2π))` of `y² = 4x³ − 4x`.
* `CM4E.omegaRho` : the real period `Ω_ρ = Γ(1/3)³ / (2^{4/3} π)` of `y² = 4x³ − 4`.
* `CM4E.FourExpAt t` : the four exponentials conjecture at the exponent `t`: for `ℚ`-linearly
  independent logarithms `a, b` of algebraic numbers, `exp (t a)` and `exp (t b)` are not both
  algebraic. (With `α = exp a`, `β = exp b`, these are the determinations `α^t`, `β^t`.)

The theorems of the project (`CM4E/Final.lean`) are stated with these definitions: `FourExpAt (cϖ/π)` and
`FourExpAt (cϖ)` for `c ∈ ℚ(i)ˣ` (the paper's Theorem 1 asks for every algebraic `c ≠ 0`), and Theorem MX (`K`-form)
for the lattices `ϖℤ[i]` and `Ω_ρℤ[ρ]`.
-/

open Complex Real

namespace CM4E

/-- `𝓛`: the complex logarithms of nonzero algebraic numbers. -/
def logAlg : Set ℂ := {ℓ | IsAlgebraic ℚ (Complex.exp ℓ)}

/-- The real period of the lemniscatic curve `y² = 4x³ − 4x` (lattice `ϖ ℤ[i]`):
`ϖ = Γ(1/4)² / (2 √(2π)) = 2.62205755…`. -/
noncomputable def varpi : ℝ := Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt (2 * π))

/-- The real period of the equianharmonic curve `y² = 4x³ − 4` (lattice `Ω_ρ ℤ[ρ]`):
`Ω_ρ = Γ(1/3)³ / (2^{4/3} π) = 2.42865…`. -/
noncomputable def omegaRho : ℝ := Real.Gamma (1 / 3) ^ 3 / ((2 : ℝ) ^ ((4 : ℝ) / 3) * π)

/-- **The four exponentials conjecture at the exponent `t`.** If `a, b ∈ 𝓛` are linearly
independent over `ℚ`, then `exp (t a)` and `exp (t b)` are not both algebraic. -/
def FourExpAt (t : ℂ) : Prop :=
  ∀ a b : ℂ, a ∈ logAlg → b ∈ logAlg → LinearIndependent ℚ ![a, b] →
    ¬ (IsAlgebraic ℚ (Complex.exp (t * a)) ∧ IsAlgebraic ℚ (Complex.exp (t * b)))


end CM4E
