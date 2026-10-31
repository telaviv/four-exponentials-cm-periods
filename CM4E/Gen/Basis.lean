/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Adapted bases of number fields containing an imaginary quadratic field

For `α ∈ ℂ` generating an imaginary quadratic field `k = ℚ(α)` and `b : Fin r → ℂ`, put `θ(j, 0) = b j`,
`θ(j, 1) = α b j`. `IsAdaptedFieldBasis α b` says that `θ` is a `ℚ`-basis of a number field `K = span_ℚ θ ⊂ ℂ`
(so `b` is a `k`-basis of `K` and `[K : ℚ] = 2r`). The general proofs of Theorems MG and MG♮ (`CM4E/Gen/`) work with
such a `θ`.
-/

open Complex

namespace CM4E.Gen

/-- `θ(j, 0) = b j`, `θ(j, 1) = α b j`. -/
def theta (α : ℂ) {r : ℕ} (b : Fin r → ℂ) : Fin r × Fin 2 → ℂ :=
  fun p => if p.2 = 0 then b p.1 else α * b p.1

/-- `K = span_ℚ θ`. -/
noncomputable def Kspan (α : ℂ) {r : ℕ} (b : Fin r → ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ (Set.range (theta α b))

/-- `θ` is a `ℚ`-basis of a subfield `K` of `ℂ` consisting of algebraic numbers. -/
structure IsAdaptedFieldBasis (α : ℂ) {r : ℕ} (b : Fin r → ℂ) : Prop where
  indep : LinearIndependent ℚ (theta α b)
  one_mem : (1 : ℂ) ∈ Kspan α b
  mul_mem : ∀ x ∈ Kspan α b, ∀ y ∈ Kspan α b, x * y ∈ Kspan α b
  inv_mem : ∀ x ∈ Kspan α b, x⁻¹ ∈ Kspan α b
  alg : ∀ j, IsAlgebraic ℚ (b j)

end CM4E.Gen
