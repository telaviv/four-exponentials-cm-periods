/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.X7

/-!
# Theorem X7: the torsion step, and Corollary X7 (a), (b) for the parameter `LA` (paper [II])

**Torsion.** A point `exp_A(v)` is torsion iff `v ∈ ℚ ⊗ Ω(A) = F γ`, i.e. iff its eigen-coordinate triple is
`(σ_{s+1}(x) P_{s+1})_s` for some `x ∈ F = ℚ(ζ)`; with `x = Σ_e q_e ζ^e` (`q_e ∈ ℚ`) this is `TorsionTriple v`. For `E`,
`exp_E(u)` is torsion iff `u ∈ ℚ(α)Ω`. The paper's torsion step (proof of Theorem X: the smallest algebraic subgroup of
`A²` whose Lie algebra contains `(v, γ)` is the graph of some `x ∈ End⁰(A) = F`; Masser for `E`) is the named input
`TorsionX7 LA`; `thmX7_torsion` then gives the full conclusion of Theorem X7.

**Corollary X7 (a), (b)** are stated in the paper for Abel–Jacobi logarithms `v` of `Q − O` (`z_s(v) = ∫_O^Q dx/y^{7−s}`)
and elliptic logarithms. Lean has no abelian integrals on `C`, so they are stated for the parameter `LA` (`x7a`, `x7b`);
the literal statements are their instances for `LA = LA_A`, the set of Abel–Jacobi triples (see `TRUST.md`).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

/-- `v = xγ` with `x = Σ_e q_e ζ^e ∈ F`: the triple of a point of `ℚ ⊗ Ω(A)`, i.e. `exp_A(v)` is torsion. -/
def TorsionTriple (v : Fin 3 → ℂ) : Prop :=
  ∃ q : Fin 6 → ℚ, ∀ s : Fin 3, v s = ∑ e : Fin 6, (q e : ℂ) * zeta7 ^ (((s : ℕ) + 1) * (e : ℕ)) * perA ((s : ℕ) + 1)

/-- **Named input (Wüstholz 1989 on `A²`, `End⁰(A) = F`; Masser 1975 for `E`): the torsion step.** A logarithm of `A`
with one slot coordinate in `ℚ̄P_s` is a torsion triple; an elliptic logarithm of `E` in `ℚ̄Ω` lies in `ℚ(α)Ω`. -/
def TorsionX7 (LA : Set (Fin 3 → ℂ)) : Prop :=
  (∀ v ∈ LA, ∀ s : Fin 3, ∀ c : ℂ, IsAlgebraic ℚ c → v s = c * perA ((s : ℕ) + 1) → TorsionTriple v) ∧
    (∀ u : ℂ, LogE E7 u → ∀ c : ℂ, IsAlgebraic ℚ c → u = c * omega7 → ∃ p q : ℚ, u = (p + q * alpha7) * omega7)

/-- **Theorem X7** (paper [II], `thm:X7`): under its hypothesis, `q₁ = q₂ = 0` and `exp(v₁), exp(v₂), exp(v₃)`,
`exp_E(u)` are torsion points. -/
theorem thmX7_torsion (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (hWX : WuestholzX7 LA)
    (hTo : TorsionX7 LA) (v₁ v₂ v₃ : Fin 3 → ℂ) (hv₁ : v₁ ∈ LA) (hv₂ : v₂ ∈ LA) (hv₃ : v₃ ∈ LA) (u : ℂ)
    (hu : LogE E7 u) (q₁ q₂ β : ℂ) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂) (hβ : IsAlgebraic ℚ β)
    (hβ0 : β ≠ 0) (hrel : (v₁ 0 + u + q₁) * (β * perA 3) = (v₃ 2 + v₂ 1 + q₂) * perA 1) :
    q₁ = 0 ∧ q₂ = 0 ∧ TorsionTriple v₁ ∧ TorsionTriple v₂ ∧ TorsionTriple v₃ ∧
      ∃ p q : ℚ, u = (p + q * alpha7) * omega7 := by
  obtain ⟨e1, e2, ⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩, ⟨c₃, hc₃, h₃⟩, ⟨c₄, hc₄, h₄⟩⟩ :=
    thmX7 LA hW hWB hWX v₁ v₂ v₃ hv₁ hv₂ hv₃ u hu q₁ q₂ β hq₁ hq₂ hβ hβ0 hrel
  exact ⟨e1, e2, hTo.1 v₁ hv₁ 0 c₁ hc₁ (by simpa using h₁), hTo.1 v₂ hv₂ 1 c₂ hc₂ (by simpa using h₂),
    hTo.1 v₃ hv₃ 2 c₃ hc₃ (by simpa using h₃), hTo.2 u hu c₄ hc₄ h₄⟩

/-- **Corollary X7 (a)** for `LA` (paper [II], `cor:X7`(a)): if `v ∈ LA` is not a torsion triple, then
`z₂(v)/z₁(v) ∉ ℚ̄ˣ·P₃/P₁`, i.e. `z₂(v) ≠ c z₁(v) P₃/P₁` for every `c ∈ ℚ̄ˣ`. (Uses that `0 ∈ LA`, the logarithm of `O`.) -/
theorem x7a (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (hWX : WuestholzX7 LA)
    (hTo : TorsionX7 LA) (h0 : (0 : Fin 3 → ℂ) ∈ LA) (v : Fin 3 → ℂ) (hv : v ∈ LA) (hnt : ¬ TorsionTriple v)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : v 1 ≠ c * v 0 * perA 3 / perA 1 := by
  intro h
  have hP1 := perA_ne (j := 1) (by norm_num) (by norm_num)
  obtain ⟨-, -, ht, -⟩ := thmX7_torsion LA hW hWB hWX hTo v v 0 hv hv h0 0 (Or.inl (zero_mem _)) 0 0 c
    isAlgebraic_zero isAlgebraic_zero hc hc0 (by rw [h]; simp only [Pi.zero_apply]; field_simp; ring)
  exact hnt ht

/-- **Corollary X7 (b)** for `LA` (paper [II], `cor:X7`(b)): for `u ∈ 𝓛_E` with `exp_E(u)` not torsion and `v ∈ LA`,
`z₃(v)/u ∉ ℚ̄ˣ·P₃/P₁`. -/
theorem x7b (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (hWX : WuestholzX7 LA)
    (hTo : TorsionX7 LA) (h0 : (0 : Fin 3 → ℂ) ∈ LA) (v : Fin 3 → ℂ) (hv : v ∈ LA) (u : ℂ) (hu : LogE E7 u)
    (hnt : ¬ ∃ p q : ℚ, u = (p + q * alpha7) * omega7) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    v 2 ≠ c * u * perA 3 / perA 1 := by
  intro h
  have hP1 := perA_ne (j := 1) (by norm_num) (by norm_num)
  obtain ⟨-, -, -, -, -, ht⟩ := thmX7_torsion LA hW hWB hWX hTo 0 0 v h0 h0 hv u hu 0 0 c
    isAlgebraic_zero isAlgebraic_zero hc hc0 (by rw [h]; simp only [Pi.zero_apply]; field_simp; ring)
  exact hnt ht

end CM4E.AbVar
