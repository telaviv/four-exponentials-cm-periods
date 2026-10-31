import CM4E.AbVar.X7Torsion

open Complex CM4E.Waldschmidt CM4E.Gen CM4E.AbVar

#print axioms CM4E.AbVar.thmX7_torsion
#print axioms CM4E.AbVar.x7a
#print axioms CM4E.AbVar.x7b
#check @CM4E.AbVar.TorsionX7

namespace TorX7Check

/-- Sanity: the period triple is a torsion triple (x = 1). -/
example : TorsionTriple perT :=
  ⟨Pi.single 0 1, fun s => by
    rw [Finset.sum_eq_single (0 : Fin 6)]
    · simp [perT]
    · intro e _ he; simp [Pi.single_apply, he]
    · simp⟩

/-- Sanity: `0` is a torsion triple. -/
example : TorsionTriple 0 := ⟨0, fun s => by simp⟩

/-- `c = 0` is already covered by `TorsionX7` (i): a non-torsion triple in `LA` has no zero slot. -/
theorem slot_ne_zero (LA : Set (Fin 3 → ℂ)) (hTo : TorsionX7 LA) (v : Fin 3 → ℂ) (hv : v ∈ LA)
    (hnt : ¬ TorsionTriple v) (s : Fin 3) : v s ≠ 0 := fun h =>
  hnt (hTo.1 v hv s 0 isAlgebraic_zero (by simp [h]))

/-- Cor. X7 (a) in full (`ℚ̄`, including `0`; ratio defined). -/
theorem x7a_full (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (hWX : WuestholzX7 LA)
    (hTo : TorsionX7 LA) (h0 : (0 : Fin 3 → ℂ) ∈ LA) (v : Fin 3 → ℂ) (hv : v ∈ LA) (hnt : ¬ TorsionTriple v) :
    v 0 ≠ 0 ∧ ∀ c : ℂ, IsAlgebraic ℚ c → v 1 / v 0 ≠ c * (perA 3 / perA 1) := by
  have h0' := slot_ne_zero LA hTo v hv hnt 0
  refine ⟨h0', fun c hc h => ?_⟩
  by_cases hc0 : c = 0
  · subst hc0
    exact slot_ne_zero LA hTo v hv hnt 1 (by simpa [h0'] using h)
  · exact x7a LA hW hWB hWX hTo h0 v hv hnt c hc hc0 (by rw [div_eq_iff h0'] at h; rw [h]; ring)

/-! A concrete Abel–Jacobi set (sketch; elementary analysis only). A lift of a C¹ path `p` in `ℂ ∖ {0,1}` with
a continuous branch `y`, `y⁷ = p(1 − p)`, from `(x₀, y₀)` to `(x₁, y₁)`, both algebraic. -/
structure AJPath where
  p : ℝ → ℂ
  y : ℝ → ℂ
  hp : ContDiff ℝ 1 p
  hy : ContinuousOn y (Set.Icc 0 1)
  heq : ∀ t ∈ Set.Icc (0 : ℝ) 1, y t ^ 7 = p t * (1 - p t)
  hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, p t ≠ 0 ∧ p t ≠ 1
  halg : IsAlgebraic ℚ (p 0) ∧ IsAlgebraic ℚ (y 0) ∧ IsAlgebraic ℚ (p 1) ∧ IsAlgebraic ℚ (y 1)

/-- `z_s = ∫ dx / y^{6-s}` along the lift (`s = 0, 1, 2`: `dx/y⁶, dx/y⁵, dx/y⁴`). -/
noncomputable def AJPath.triple (γ : AJPath) : Fin 3 → ℂ :=
  fun s => ∫ t in (0 : ℝ)..1, deriv γ.p t / γ.y t ^ (6 - (s : ℕ))

/-- Abel–Jacobi triples of `Q − O` for affine non-branch points. -/
def AJ1 : Set (Fin 3 → ℂ) := Set.range AJPath.triple

/-- Intended `LA`: the `ℚ`-span (= `Λ(A)` by Jacobi inversion and divisibility). -/
def LAJ : Set (Fin 3 → ℂ) := Submodule.span ℚ AJ1

example : (0 : Fin 3 → ℂ) ∈ LAJ := Submodule.zero_mem _

end TorX7Check
