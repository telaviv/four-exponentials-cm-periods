/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.FrameX1

/-!
# The frame of Theorem SE₀: one `G_a` slot and one fibre slot

Same tangent space and same map as `CM4E/AbVar/FrameX1.lean`: `T(G'') = Q × ℂ × ℂ ∋ (q, s₁, s₂)` with two linear forms
`μ₁, μ₂` on `Q` and `Ψ''(q, s₁, s₂) = (μ₁(q) + s₁, μ₂(q) + s₂)`. For Theorem SE₀ (paper addition seed 2, Theorem `thm:SE`
(3); `paper_cm/paper.tex` Theorem 4.12(3)) the group is `G'' = G_a × G₂` with `G₂` a vector extension: `q` is the
abelian (base) coordinate of `G₂`, `s₁` the coordinate of `G_a` and `s₂` the fibre coordinate of `G₂`. So `s₁` is in
`d₀` and `s₂` in `d₂`: `d₂ = dim Q + 1` (in `gmFX1` both `s₁, s₂` are `G_a`-coordinates and `d₂ = dim Q`).

`frameX0_false`: given `n` period lifts with `Ψ'' = θ_h(A, σA)` and `n + n` data lifts with `Ψ'' = θ_h(x_j, σx_j)`, where
`A, x₁, x₂` are linearly independent over `K = span_ℚ θ`, `σ` is transcendental and `dim Q + 1 < 2n`, the hypothesis
`HyperplaneKappa (gmFX0 …)` is contradictory: `m = 3n`, `κ ≥ n`, `d − 1 − t = 1`, and (5.4) reads
`3n > 2(dim Q + 1) − n`.

Soundness of the model (not checked by Lean): `gmFX0 algQ lamS perS μ₁ μ₂` is sound for `G'' = G_a × G₂` when `algQ` is the
`ℚ̄`-structure of `Q`, `lamS` consists of logarithms of algebraic points of `G''`, `perS` of periods, `d₁ = 0`,
`d₂ = dim G₂ = dim Q + 1` (one fibre coordinate), and every nonzero connected algebraic subgroup of `G''` has an algebraic
tangent vector outside `ker Ψ''` (the uniform subgroup condition, the field `sub`). The instance used for Theorem SE₀
(`CM4E/AbVar/SE0.lean`) is reduced to the standard model of `lean_lsg` in `CM4E/Bridge/SE0.lean`, where the subgroup
condition is proved.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- **The group model of `G_a × G₂` with `G₂` a vector extension with one fibre coordinate** (`d₁ = 0`,
`d₂ = dim Q + 1`), linear forms `μ₁, μ₂`. Coordinates `(q, s₁, s₂)`: `q` base of `G₂`, `s₁` the `G_a`-coordinate, `s₂`
the fibre coordinate. Sound when `lamS` consists of logarithms of algebraic points, `perS` of periods, and every nonzero
connected algebraic subgroup has an algebraic tangent vector outside `ker Ψ''` (the uniform subgroup condition). -/
noncomputable def gmFX0 [FiniteDimensional ℂ Q] (algQ : Q → Prop) (lamS perS : Set (TX Q))
    (μ₁ μ₂ : Q →ₗ[ℂ] ℂ) : GroupModel (TX Q) where
  d₁ := 0
  d₂ := finrank ℂ Q + 1
  alg := algX algQ
  lam := (Submodule.span ℚ lamS : Set (TX Q))
  per := Submodule.span ℚ perS
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algX algQ x ∧ PsiX μ₁ μ₂ x ≠ 0

section Main

variable (μ₁ μ₂ : Q →ₗ[ℂ] ℂ)

/-- The `3n` generators: period lifts `p`, data lifts `d₁`, `d₂`. -/
def genX0 (p d₁ d₂ : ι → TX Q) : Fin 3 × ι → TX Q := fun q => ![p q.2, d₁ q.2, d₂ q.2] q.1

/-- **The frame-X0 contradiction** (W88 §5d for `G_a × G₂^♮`, one period family, two data families). -/
theorem frameX0_false [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ) (algQ : Q → Prop)
    (lamS perS : Set (TX Q))
    (hW : HyperplaneKappa (gmFX0 algQ lamS perS μ₁ μ₂))
    (hcount : finrank ℂ Q + 1 < 2 * Fintype.card ι)
    (hμ₁ : ∀ q, algQ q → IsAlgebraic ℚ (μ₁ q)) (hμ₂ : ∀ q, algQ q → IsAlgebraic ℚ (μ₂ q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = ⊤)
    (σ : ℂ) (hσ : Transcendental ℚ σ) (A x₁ x₂ : ℂ)
    (hind : ∀ c₀ c₁ c₂ : ℂ, c₀ ∈ Submodule.span ℚ (Set.range θ) → c₁ ∈ Submodule.span ℚ (Set.range θ) →
      c₂ ∈ Submodule.span ℚ (Set.range θ) → c₀ * A + c₁ * x₁ + c₂ * x₂ = 0 → c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0)
    (p : ι → TX Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiX μ₁ μ₂ (p h) = (θ h * A, σ * (θ h * A)))
    (d₁ d₂ : ι → TX Q) (hd₁l : ∀ h, d₁ h ∈ Submodule.span ℚ lamS) (hd₂l : ∀ h, d₂ h ∈ Submodule.span ℚ lamS)
    (hd₁Ψ : ∀ h, PsiX μ₁ μ₂ (d₁ h) = (θ h * x₁, σ * (θ h * x₁)))
    (hd₂Ψ : ∀ h, PsiX μ₁ μ₂ (d₂ h) = (θ h * x₂, σ * (θ h * x₂))) : False := by
  set g0 := genX0 p d₁ d₂
  have hΨ1 : ∀ q, (PsiX μ₁ μ₂ (g0 q)).1 = θ q.2 * ![A, x₁, x₂] q.1 := by
    rintro ⟨k, h⟩
    fin_cases k
    · simp [g0, genX0, hpΨ]
    · simp [g0, genX0, hd₁Ψ]
    · simp [g0, genX0, hd₂Ψ]
  -- independence
  have hli : LinearIndependent ℚ g0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e := congrArg (fun v => (PsiX μ₁ μ₂ v).1) hg
    simp only [map_sum, Prod.fst_sum, map_zero, Prod.fst_zero] at e
    simp only [fun q => show (PsiX μ₁ μ₂ (g q • g0 q)).1 = (g q : ℂ) * (PsiX μ₁ μ₂ (g0 q)).1 by
      rw [map_rat_smul, Prod.smul_fst, Rat.smul_def], hΨ1, Fintype.sum_prod_type, Fin.sum_univ_three] at e
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e
    have hrel : dotL θ (fun h => ((g (0, h) : ℚ) : ℂ)) * A + dotL θ (fun h => ((g (1, h) : ℚ) : ℂ)) * x₁ +
        dotL θ (fun h => ((g (2, h) : ℚ) : ℂ)) * x₂ = 0 := by
      simp only [dotL_apply, Finset.sum_mul]
      rw [← e]
      congr 1
      · congr 1 <;> exact Finset.sum_congr rfl fun h _ => by ring
      · exact Finset.sum_congr rfl fun h _ => by ring
    obtain ⟨a0, a1, a2⟩ := hind _ _ _ (dot_rat_mem_span θ _) (dot_rat_mem_span θ _) (dot_rat_mem_span θ _) hrel
    have z0 := dot_rat_eq_zero hθ _ a0
    have z1 := dot_rat_eq_zero hθ _ a1
    have z2 := dot_rat_eq_zero hθ _ a2
    rintro ⟨k, h⟩
    fin_cases k
    exacts [congrFun z0 h, congrFun z1 h, congrFun z2 h]
  set e := Fintype.equivFin (Fin 3 × ι)
  set y' : Fin (Fintype.card (Fin 3 × ι)) → TX Q := g0 ∘ e.symm with hy'
  have hli' : LinearIndependent ℚ y' := hli.comp _ e.symm.injective
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y')) = 3 * Fintype.card ι := by
    rw [finrank_span_eq_card hli']; simp [Fintype.card_prod]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y')) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hmem : ∀ q, g0 q ∈ Submodule.span ℚ (Set.range y') := fun q =>
    Submodule.subset_span ⟨e q, by simp [hy']⟩
  -- `κ ≥ n`
  have hk : Fintype.card ι ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFX0 algQ lamS perS μ₁ μ₂).per) := by
    let f : ι → ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFX0 algQ lamS perS μ₁ μ₂).per) := fun h =>
      ⟨g0 (0, h), hmem _, hpp h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp
        (Submodule.span ℚ (Set.range y') ⊓ (gmFX0 algQ lamS perS μ₁ μ₂).per).subtype
      exact hli.comp (fun h : ι => ((0 : Fin 3), h)) (fun a b hab => by
        simp only [Prod.mk.injEq] at hab
        exact hab.2)
    exact hf.fintype_card_le_finrank
  -- `V''`, `W''`
  have hV : finrank ℂ (LinearMap.ker (phiX μ₁ μ₂ σ)) + 1 = finrank ℂ (TX Q) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (phiX μ₁ μ₂ σ)
    have hs : Function.Surjective (phiX μ₁ μ₂ σ) := fun w =>
      ⟨((0 : Q), (0 : ℂ), w), by simp [phiX_apply, PsiX_apply]⟩
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at h1
    omega
  set W := Submodule.span ℂ (kerX μ₁ μ₂ '' T) with hWdef
  have hWeq : W = LinearMap.range (kerX μ₁ μ₂) := by
    rw [hWdef, Submodule.span_image, hT, Submodule.map_top]
  have hWV : W ≤ LinearMap.ker (phiX μ₁ μ₂ σ) := by
    rw [hWeq]
    rintro _ ⟨q, rfl⟩
    simp [phiX_apply, PsiX_apply, kerX]
  have hinj : Function.Injective (kerX μ₁ μ₂) := fun a b h => by
    simpa [kerX] using congrArg Prod.fst h
  have hfinW : finrank ℂ W = finrank ℂ Q := by
    rw [hWeq, LinearMap.finrank_range_of_inj hinj]
  have hfinT : finrank ℂ (TX Q) = finrank ℂ Q + 2 := by
    simp [TX, Module.finrank_prod]
  have hWrat : (gmFX0 algQ lamS perS μ₁ μ₂).Rational W := by
    refine ⟨kerX μ₁ μ₂ '' T, ?_, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hTalg q hq, (hμ₁ q (hTalg q hq)).neg, (hμ₂ q (hTalg q hq)).neg⟩
  have hVmem : ∀ q, g0 q ∈ LinearMap.ker (phiX μ₁ μ₂ σ) := by
    rintro ⟨k, h⟩
    rw [LinearMap.mem_ker, phiX_apply]
    fin_cases k
    · simp [g0, genX0, hpΨ]
    · simp [g0, genX0, hd₁Ψ]
    · simp [g0, genX0, hd₂Ψ]
  have hlamMem : ∀ q, g0 q ∈ (gmFX0 algQ lamS perS μ₁ μ₂).lam := by
    rintro ⟨k, h⟩
    show g0 (k, h) ∈ Submodule.span ℚ lamS
    fin_cases k
    exacts [hpl h, hd₁l h, hd₂l h]
  -- apply W88 §5d
  obtain ⟨S, hsub, hne, hle⟩ := hW (LinearMap.ker (phiX μ₁ μ₂ σ)) W _ y'
    (by omega) hWV hWrat
    (fun i => ⟨hVmem (e.symm i), hlamMem (e.symm i)⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y')) : ℤ) >
        ((0 : ℕ) + 2 * ((finrank ℂ Q + 1 : ℕ) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFX0 algQ lamS perS μ₁ μ₂).per)) *
          ((finrank ℂ (TX Q) : ℤ) - 1 - finrank ℂ W))
      rw [hfinY, hfinW, hfinT]
      push_cast
      have : ((finrank ℂ Q : ℤ) + 2 - 1 - finrank ℂ Q) = 1 := by ring
      rw [this]
      omega)
  rcases hsub with rfl | ⟨v, hvS, ⟨hv1, hv2, hv3⟩, hv⟩
  · exact hne rfl
  · have hvV := hle hvS
    rw [LinearMap.mem_ker, phiX_apply] at hvV
    have h1 : IsAlgebraic ℚ (PsiX μ₁ μ₂ v).1 := by rw [PsiX_apply]; exact (hμ₁ _ hv1).add hv2
    have h2 : IsAlgebraic ℚ (PsiX μ₁ μ₂ v).2 := by rw [PsiX_apply]; exact (hμ₂ _ hv1).add hv3
    by_cases hP1 : (PsiX μ₁ μ₂ v).1 = 0
    · apply hv
      have hP2 : (PsiX μ₁ μ₂ v).2 = 0 := by rw [hP1, mul_zero, sub_zero] at hvV; exact hvV
      exact Prod.ext hP1 hP2
    · apply hσ
      have : σ = (PsiX μ₁ μ₂ v).2 / (PsiX μ₁ μ₂ v).1 := by field_simp; linear_combination -hvV
      rw [this, ← mem_algebraicClosure_iff]
      exact div_mem (mem_algebraicClosure_iff.mpr h2) (mem_algebraicClosure_iff.mpr h1)

end Main

end CM4E.AbVar
