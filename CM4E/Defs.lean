/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Statements: four exponentials at CM periods

This file only *states* the target theorems of the project, as `Prop`s, in elementary terms
(no elliptic curves appear in the statements). Read this file first: whether the eventual
proofs prove what you care about depends only on these definitions.

* `CM4E.logAlg` : `𝓛 = {ℓ ∈ ℂ | exp ℓ is algebraic}`, the logarithms of nonzero algebraic
  numbers (same definition as `StrongSix.logAlg` in `schanuel/six_exp/lean`).
* `CM4E.varpi` : the real period `ϖ = Γ(1/4)² / (2√(2π))` of `y² = 4x³ − 4x`.
* `CM4E.omegaRho` : the real period `Ω_ρ = Γ(1/3)³ / (2^{4/3} π)` of `y² = 4x³ − 4`.
* `CM4E.FourExpAt t` : the four exponentials conjecture at the exponent `t`: for `ℚ`-linearly
  independent logarithms `a, b` of algebraic numbers, `exp (t a)` and `exp (t b)` are not both
  algebraic. (With `α = exp a`, `β = exp b`, these are the determinations `α^t`, `β^t`.)

Targets (paper `schanuel/five_exp/pilot_thmM/paper/paper.tex`, Theorem 1):
* `CM4E.Target.fourExp_varpi`       : `FourExpAt (c ϖ)` for algebraic `c ≠ 0`
  (e.g. `2^ϖ`, `3^ϖ` are not both algebraic);
* `CM4E.Target.fourExp_varpi_div_pi`: `FourExpAt (c ϖ / π)` for algebraic `c ≠ 0`;
* the same for `Ω_ρ`;
* `CM4E.Target.mg1_varpi` : one of `e^{π²}`, `e^{πϖ}`, `e^{π²/ϖ}` is transcendental.
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

namespace Target

/-- **Theorem 1(a) at `ϖ`** (target). Four exponentials at `t = c ϖ`, `c` algebraic, `c ≠ 0`.
For example `2^ϖ` and `3^ϖ` are not both algebraic. -/
def fourExp_varpi : Prop :=
  ∀ c : ℂ, IsAlgebraic ℚ c → c ≠ 0 → FourExpAt (c * (varpi : ℂ))

/-- **Theorem 1(b) at `ϖ`** (target). Four exponentials at `t = c ϖ / π`. -/
def fourExp_varpi_div_pi : Prop :=
  ∀ c : ℂ, IsAlgebraic ℚ c → c ≠ 0 → FourExpAt (c * (varpi : ℂ) / (π : ℂ))

/-- **Theorem 1(a) at `Ω_ρ`** (target). -/
def fourExp_omegaRho : Prop :=
  ∀ c : ℂ, IsAlgebraic ℚ c → c ≠ 0 → FourExpAt (c * (omegaRho : ℂ))

/-- **Theorem 1(b) at `Ω_ρ`** (target). -/
def fourExp_omegaRho_div_pi : Prop :=
  ∀ c : ℂ, IsAlgebraic ℚ c → c ≠ 0 → FourExpAt (c * (omegaRho : ℂ) / (π : ℂ))

/-- **Corollary MG1 at `ϖ`** (target). One of `e^{π²}`, `e^{πϖ}`, `e^{π²/ϖ}` is transcendental. -/
def mg1_varpi : Prop :=
  ¬ (IsAlgebraic ℚ (Real.exp (π ^ 2)) ∧ IsAlgebraic ℚ (Real.exp (π * varpi)) ∧
      IsAlgebraic ℚ (Real.exp (π ^ 2 / varpi)))

end Target

end CM4E
