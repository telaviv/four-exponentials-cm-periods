/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Frame2

/-!
# The frame of Theorem X: `Ψ''(q, s₁, s₂) = (μ₁(q) + s₁, μ₂(q) + s₂)` on `G₂ × G_a²`

The group of the paper, proof of Proposition `prop:X`, is `G'' = A'' × G_a²` with two linear forms `μ₁, μ₂` on
`Q = T(A'')` (the slot forms feeding the two target coordinates) and `Ψ'' = (μ₁ + q₁, μ₂ + q₂)`. The model `gmFX` takes
`d₁ = 0` and `d₂ = dim Q + 2 = dim G''` (the paper puts `G_a²` in `d₀`; counting it in `d₂` only weakens the
hypothesis), and the uniform subgroup condition.

`frameX_false`: given `n` period lifts with `Ψ'' = θ_h(A, σA)`, `n` with `Ψ'' = θ_h(A', σA')`, `n` data lifts with
`Ψ'' = θ_h(x, σx)`, where `A, A'` are linearly independent over `K = span_ℚ θ`, `x ∉ K A + K A'`, `σ` is transcendental and
`2 dim Q + 4 < 5n`, the hypothesis `HyperplaneKappa` is contradictory: `m = 3n`, `κ ≥ 2n`, `d − 1 − t ≤ 1`.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

/-- The tangent space `Q × ℂ × ℂ` of `G₂ × G_a²`. -/
abbrev TX (Q : Type) [AddCommGroup Q] := Q × ℂ × ℂ

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- `Ψ''(q, s₁, s₂) = (μ₁(q) + s₁, μ₂(q) + s₂)`. -/
noncomputable def PsiX (μ₁ μ₂ : Q →ₗ[ℂ] ℂ) : TX Q →ₗ[ℂ] ℂ × ℂ :=
  (μ₁ ∘ₗ LinearMap.fst ℂ _ _ + LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _).prod
    (μ₂ ∘ₗ LinearMap.fst ℂ _ _ + LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _)

omit [Module ℚ Q] in
lemma PsiX_apply (μ₁ μ₂ : Q →ₗ[ℂ] ℂ) (v : TX Q) : PsiX μ₁ μ₂ v = (μ₁ v.1 + v.2.1, μ₂ v.1 + v.2.2) := by
  simp [PsiX]

/-- Algebraic vectors of `Q × ℂ × ℂ`. -/
def algX (algQ : Q → Prop) (v : TX Q) : Prop := algQ v.1 ∧ IsAlgebraic ℚ v.2.1 ∧ IsAlgebraic ℚ v.2.2

/-- **The group model of `G₂ × G_a²`** with linear forms `μ₁, μ₂` (`d₁ = 0`, `d₂ = dim G''`). Sound when `lamS`
consists of logarithms of algebraic points, `perS` of periods, and no nonzero connected algebraic subgroup has its
tangent space in `ker Ψ''`. -/
noncomputable def gmFX [FiniteDimensional ℂ Q] (algQ : Q → Prop) (lamS perS : Set (TX Q))
    (μ₁ μ₂ : Q →ₗ[ℂ] ℂ) : GroupModel (TX Q) where
  d₁ := 0
  d₂ := finrank ℂ Q + 2
  alg := algX algQ
  lam := (Submodule.span ℚ lamS : Set (TX Q))
  per := Submodule.span ℚ perS
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algX algQ x ∧ PsiX μ₁ μ₂ x ≠ 0

section Main

variable (μ₁ μ₂ : Q →ₗ[ℂ] ℂ)

/-- `(μ₂(q) + s₂) − σ(μ₁(q) + s₁)`; its kernel is `V'' = Ψ''⁻¹(ℂ(1, σ))`. -/
noncomputable def phiX (σ : ℂ) : TX Q →ₗ[ℂ] ℂ :=
  LinearMap.snd ℂ ℂ ℂ ∘ₗ PsiX μ₁ μ₂ - σ • (LinearMap.fst ℂ ℂ ℂ ∘ₗ PsiX μ₁ μ₂)

omit [Module ℚ Q] in
lemma phiX_apply (σ : ℂ) (v : TX Q) : phiX μ₁ μ₂ σ v = (PsiX μ₁ μ₂ v).2 - σ * (PsiX μ₁ μ₂ v).1 := by
  simp [phiX]

/-- `q ↦ (q, −μ₁(q), −μ₂(q))`, whose range is `ker Ψ''`. -/
noncomputable def kerX : Q →ₗ[ℂ] TX Q :=
  LinearMap.prod LinearMap.id ((-μ₁).prod (-μ₂))

/-- The `3n` generators. -/
def genX (p p' dl : ι → TX Q) : Fin 3 × ι → TX Q := fun q => ![p q.2, p' q.2, dl q.2] q.1

/-- **The frame-X contradiction** (W88 §5d for `G₂ × G_a²`). -/
theorem frameX_false [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ) (algQ : Q → Prop) (lamS perS : Set (TX Q))
    (hW : HyperplaneKappa (gmFX algQ lamS perS μ₁ μ₂))
    (hcount : 2 * finrank ℂ Q + 4 < 5 * Fintype.card ι)
    (hμ₁ : ∀ q, algQ q → IsAlgebraic ℚ (μ₁ q)) (hμ₂ : ∀ q, algQ q → IsAlgebraic ℚ (μ₂ q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = ⊤)
    (σ : ℂ) (hσ : Transcendental ℚ σ) (A A' : ℂ)
    (hAA' : ∀ c c' : ℂ, c ∈ Submodule.span ℚ (Set.range θ) → c' ∈ Submodule.span ℚ (Set.range θ) →
      c * A + c' * A' = 0 → c = 0 ∧ c' = 0)
    (p p' : ι → TX Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hp'l : ∀ h, p' h ∈ Submodule.span ℚ lamS) (hp'p : ∀ h, p' h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiX μ₁ μ₂ (p h) = (θ h * A, σ * (θ h * A)))
    (hp'Ψ : ∀ h, PsiX μ₁ μ₂ (p' h) = (θ h * A', σ * (θ h * A')))
    (dl : ι → TX Q) (x : ℂ) (hdl : ∀ h, dl h ∈ Submodule.span ℚ lamS)
    (hdΨ : ∀ h, PsiX μ₁ μ₂ (dl h) = (θ h * x, σ * (θ h * x)))
    (hx : ∀ c₀ c c' : ℂ, c₀ ∈ Submodule.span ℚ (Set.range θ) → c ∈ Submodule.span ℚ (Set.range θ) →
      c' ∈ Submodule.span ℚ (Set.range θ) → c₀ ≠ 0 → c₀ * x ≠ c * A + c' * A') : False := by
  set g0 := genX p p' dl
  have hΨ1 : ∀ q, (PsiX μ₁ μ₂ (g0 q)).1 = θ q.2 * ![A, A', x] q.1 := by
    rintro ⟨k, h⟩
    fin_cases k
    · simp [g0, genX, hpΨ]
    · simp [g0, genX, hp'Ψ]
    · simp [g0, genX, hdΨ]
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
    have hrel : dotL θ (fun h => ((g (0, h) : ℚ) : ℂ)) * A + dotL θ (fun h => ((g (1, h) : ℚ) : ℂ)) * A' +
        dotL θ (fun h => ((g (2, h) : ℚ) : ℂ)) * x = 0 := by
      simp only [dotL_apply, Finset.sum_mul]
      rw [← e]
      congr 1
      · congr 1 <;> exact Finset.sum_congr rfl fun h _ => by ring
      · exact Finset.sum_congr rfl fun h _ => by ring
    have hc2 : dotL θ (fun h => ((g (2, h) : ℚ) : ℂ)) = 0 := by
      by_contra hne
      exact hx _ (-dotL θ (fun h => ((g (0, h) : ℚ) : ℂ))) (-dotL θ (fun h => ((g (1, h) : ℚ) : ℂ)))
        (dot_rat_mem_span θ _) (neg_mem (dot_rat_mem_span θ _)) (neg_mem (dot_rat_mem_span θ _)) hne
        (by linear_combination hrel)
    rw [hc2, zero_mul, add_zero] at hrel
    obtain ⟨a0, a1⟩ := hAA' _ _ (dot_rat_mem_span θ _) (dot_rat_mem_span θ _) hrel
    have z0 := dot_rat_eq_zero hθ _ a0
    have z1 := dot_rat_eq_zero hθ _ a1
    have z2 := dot_rat_eq_zero hθ _ hc2
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
  -- `κ ≥ 2n`
  have hk : 2 * Fintype.card ι ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFX algQ lamS perS μ₁ μ₂).per) := by
    let f : Fin 2 × ι → ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFX algQ lamS perS μ₁ μ₂).per) := fun q =>
      ⟨g0 (Fin.castSucc q.1, q.2), hmem _, by
        rcases q with ⟨k, h⟩
        fin_cases k
        · exact hpp h
        · exact hp'p h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp
        (Submodule.span ℚ (Set.range y') ⊓ (gmFX algQ lamS perS μ₁ μ₂).per).subtype
      exact hli.comp (fun q : Fin 2 × ι => (Fin.castSucc q.1, q.2))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext (Fin.castSucc_injective _ hab.1) hab.2)
    have := hf.fintype_card_le_finrank
    simpa [Fintype.card_prod] using this
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
  have hWrat : (gmFX algQ lamS perS μ₁ μ₂).Rational W := by
    refine ⟨kerX μ₁ μ₂ '' T, ?_, rfl⟩
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hTalg q hq, (hμ₁ q (hTalg q hq)).neg, (hμ₂ q (hTalg q hq)).neg⟩
  have hVmem : ∀ q, g0 q ∈ LinearMap.ker (phiX μ₁ μ₂ σ) := by
    rintro ⟨k, h⟩
    rw [LinearMap.mem_ker, phiX_apply]
    fin_cases k
    · simp [g0, genX, hpΨ]
    · simp [g0, genX, hp'Ψ]
    · simp [g0, genX, hdΨ]
  have hlamMem : ∀ q, g0 q ∈ (gmFX algQ lamS perS μ₁ μ₂).lam := by
    rintro ⟨k, h⟩
    show g0 (k, h) ∈ Submodule.span ℚ lamS
    fin_cases k
    exacts [hpl h, hp'l h, hdl h]
  -- apply W88 §5d
  obtain ⟨S, hsub, hne, hle⟩ := hW (LinearMap.ker (phiX μ₁ μ₂ σ)) W _ y'
    (by omega) hWV hWrat
    (fun i => ⟨hVmem (e.symm i), hlamMem (e.symm i)⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y')) : ℤ) >
        ((0 : ℕ) + 2 * ((finrank ℂ Q + 2 : ℕ) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFX algQ lamS perS μ₁ μ₂).per)) *
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
