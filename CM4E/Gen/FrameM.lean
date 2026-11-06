/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Frame

/-!
# A third frame: `Ψ''(q, y, s) = (μ(q), θᵀy + s)` on `G₂ × G_m^n × G_a`

The group of the first proof of Theorem M (paper, §`sec:M`) after the `K`-structure is made explicit:
`G'' = G₂ × G_m^n × G_a` with tangent space `Q × ℂ^n × ℂ`, a linear form `μ` on `Q = T(G₂)` and
`Ψ''(q, y, s) = (μ(q), θᵀy + s)`. Here `G_a` is a direct factor, so `d₀ = 1` and `d₂ = dim G₂`; `d₁ = n`.

The subgroup condition is the uniform one (a nonzero connected algebraic subgroup has an algebraic tangent vector with
`Ψ'' ≠ 0`); the instance must justify it.

`frameM_false`: given `n` period lifts with `Ψ'' = θ_h(A, σA)`, one data lift with `Ψ'' = (x, σx)`, `x ∉ ℚ̄A`, `σ`
transcendental and `2d₂ ≤ n`, the hypothesis `HyperplaneKappa` is contradictory. The count: `m = n + 1`, `κ ≥ n`,
`d − 1 − t ≤ 1`, and `n + 1 > d₁ + 2d₂ − κ`.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

/-- The tangent space `Q × ℂ^ι × ℂ` of `G₂ × G_m^n × G_a`. -/
abbrev TM (ι Q : Type) [AddCommGroup Q] := Q × (ι → ℂ) × ℂ

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- `Ψ''(q, y, s) = (μ(q), θᵀy + s)`. -/
noncomputable def PsiM (θ : ι → ℂ) (μ : Q →ₗ[ℂ] ℂ) : TM ι Q →ₗ[ℂ] ℂ × ℂ :=
  (μ ∘ₗ LinearMap.fst ℂ _ _).prod
    (dotL θ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _) + LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _)

omit [DecidableEq ι] [Module ℚ Q] in
lemma PsiM_apply (θ : ι → ℂ) (μ : Q →ₗ[ℂ] ℂ) (v : TM ι Q) :
    PsiM θ μ v = (μ v.1, dotL θ v.2.1 + v.2.2) := by
  simp [PsiM]

/-- Algebraic vectors of `Q × ℂ^ι × ℂ`. -/
def algM (algQ : Q → Prop) (v : TM ι Q) : Prop :=
  algQ v.1 ∧ (∀ j, IsAlgebraic ℚ (v.2.1 j)) ∧ IsAlgebraic ℚ v.2.2

/-- **The group model of `G₂ × G_m^n × G_a`** with linear form `μ`. Sound when `lamS` consists of logarithms of
algebraic points, `perS` of periods, `d₂ = dim G₂`, and no nonzero connected algebraic subgroup has its tangent space
in `ker Ψ''`. -/
noncomputable def gmFM (θ : ι → ℂ) (algQ : Q → Prop) (lamS perS : Set (TM ι Q)) (μ : Q →ₗ[ℂ] ℂ)
    (d₂ : ℕ) : GroupModel (TM ι Q) where
  d₁ := Fintype.card ι
  d₂ := d₂
  alg := algM algQ
  lam := (Submodule.span ℚ lamS : Set (TM ι Q))
  per := Submodule.span ℚ perS
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algM algQ x ∧ PsiM θ μ x ≠ 0

section Proof

variable (θ : ι → ℂ) (μ : Q →ₗ[ℂ] ℂ)

/-- `(θᵀy + s) − σμ(q)`; its kernel is `V'' = Ψ''⁻¹(ℂ(1, σ))`. -/
noncomputable def phiM (σ : ℂ) : TM ι Q →ₗ[ℂ] ℂ :=
  LinearMap.snd ℂ ℂ ℂ ∘ₗ PsiM θ μ - σ • (LinearMap.fst ℂ ℂ ℂ ∘ₗ PsiM θ μ)

omit [DecidableEq ι] [Module ℚ Q] in
lemma phiM_apply (σ : ℂ) (v : TM ι Q) :
    phiM θ μ σ v = (PsiM θ μ v).2 - σ * (PsiM θ μ v).1 := by
  simp [phiM]

omit [DecidableEq ι] [Module ℚ Q] in
lemma phiM_surjective (σ : ℂ) : Function.Surjective (phiM θ μ σ) :=
  fun w => ⟨((0 : Q), (0 : ι → ℂ), w), by simp [phiM_apply, PsiM_apply]⟩

/-- Algebraic vectors spanning `ker Ψ''` (`T` spans `ker μ`). -/
noncomputable def wGenM (i0 : ι) (T : Set Q) : Set (TM ι Q) :=
  ((fun q : Q => (q, (0 : ι → ℂ), (0 : ℂ))) '' T ∪
    Set.range (fun j : ι => ((0 : Q), ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ℂ)))) ∪
    {((0 : Q), (-(θ i0)⁻¹) • (Pi.single i0 1 : ι → ℂ), (1 : ℂ))}

omit [Module ℚ Q] in
lemma wGenM_le_ker (i0 : ι) (h0 : θ i0 ≠ 0) (T : Set Q) (hT : ∀ q ∈ T, μ q = 0) :
    Submodule.span ℂ (wGenM θ i0 T) ≤ LinearMap.ker (PsiM θ μ) := by
  rw [Submodule.span_le]
  rintro _ ((⟨q, hq, rfl⟩ | ⟨j, rfl⟩) | h)
  · simp [PsiM_apply, hT q hq]
  · simp [PsiM_apply, map_sub, map_smul, dotL_single, mul_comm]
  · rw [Set.mem_singleton_iff] at h
    subst h
    simp only [SetLike.mem_coe, LinearMap.mem_ker, PsiM_apply, map_smul, dotL_single, smul_eq_mul,
      map_zero, Prod.mk_eq_zero, true_and]
    field_simp
    ring

omit [Module ℚ Q] in
variable {θ} in
lemma ker_PsiM_le {i0 : ι} (h0 : θ i0 ≠ 0) (T : Set Q) (hT : LinearMap.ker μ ≤ Submodule.span ℂ T) :
    LinearMap.ker (PsiM θ μ) ≤ Submodule.span ℂ (wGenM θ i0 T) := by
  intro v hv
  rw [LinearMap.mem_ker, PsiM_apply, Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2⟩ := hv
  set W := Submodule.span ℂ (wGenM θ i0 T)
  have gq : ∀ q ∈ Submodule.span ℂ T, ((q, (0 : ι → ℂ), (0 : ℂ)) : TM ι Q) ∈ W := by
    intro q hq
    refine Submodule.span_induction (fun x hx => Submodule.subset_span (Or.inl (Or.inl ⟨x, hx, rfl⟩)))
      ?_ (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) hq
    · exact W.zero_mem
    · convert add_mem hx hy using 1; simp
    · convert W.smul_mem c hx using 1; simp
  have gy : ∀ y : ι → ℂ, dotL θ y = 0 → (((0 : Q), y, (0 : ℂ)) : TM ι Q) ∈ W := by
    intro y hy
    rw [← decomp_x h0 y hy]
    have : (((0 : Q), ∑ j, (y j / θ i0) • ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ),
        (0 : ℂ)) : TM ι Q) = ∑ j, (y j / θ i0) •
          (((0 : Q), ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ℂ)) : TM ι Q) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [Prod.fst_sum, Prod.snd_sum]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩)))
  have hs1 : (((0 : Q), (-(θ i0)⁻¹) • (Pi.single i0 1 : ι → ℂ), (1 : ℂ)) : TM ι Q) ∈ W :=
    Submodule.subset_span (Or.inr rfl)
  obtain ⟨y', hy'def⟩ : ∃ y' : ι → ℂ, y' = v.2.1 + v.2.2 • (θ i0)⁻¹ • (Pi.single i0 1 : ι → ℂ) := ⟨_, rfl⟩
  have hy' : dotL θ y' = 0 := by
    rw [hy'def]
    simp only [map_add, map_smul, dotL_single, smul_eq_mul]
    field_simp
    linear_combination h2
  have hv : v = (v.1, (0 : ι → ℂ), (0 : ℂ)) + ((0 : Q), y', (0 : ℂ)) +
      v.2.2 • (((0 : Q), (-(θ i0)⁻¹) • (Pi.single i0 1 : ι → ℂ), (1 : ℂ)) : TM ι Q) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · funext k
      simp only [hy'def, Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
    · simp
  rw [hv]
  exact add_mem (add_mem (gq _ (hT h1)) (gy _ hy')) (Submodule.smul_mem _ _ hs1)

end Proof

/-! ## The contradiction -/

section Main

/-- The `n + 1` generators: period lifts `p h` and one data lift `D`. -/
def genM (p : ι → TM ι Q) (D : TM ι Q) : Option ι → TM ι Q
  | none => D
  | some h => p h

/-- **The frame-M contradiction** (W88 §5d for `G₂ × G_m^n × G_a`). -/
theorem frameM_false [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (lamS perS : Set (TM ι Q))
    (μ : Q →ₗ[ℂ] ℂ) (d₂ : ℕ) (hW : HyperplaneKappa (gmFM θ algQ lamS perS μ d₂))
    (hd₂ : 2 * d₂ ≤ Fintype.card ι) (hcard : 0 < Fintype.card ι)
    (halg0 : algQ 0) (hμ : ∀ q, algQ q → IsAlgebraic ℚ (μ q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = LinearMap.ker μ)
    (σ : ℂ) (hσ : Transcendental ℚ σ) (A : ℂ) (hA : A ≠ 0)
    (p : ι → TM ι Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiM θ μ (p h) = (θ h * A, σ * (θ h * A)))
    (D : TM ι Q) (x : ℂ) (hDl : D ∈ Submodule.span ℚ lamS) (hDΨ : PsiM θ μ D = (x, σ * x))
    (hx : ∀ s : ℂ, IsAlgebraic ℚ s → x ≠ s * A) : False := by
  obtain ⟨i0⟩ : Nonempty ι := Fintype.card_pos_iff.mp hcard
  have h0 : θ i0 ≠ 0 := hθ.ne_zero i0
  set g0 := genM p D
  -- independence
  have hli : LinearIndependent ℚ g0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e := congrArg (fun v => (PsiM θ μ v).1) hg
    simp only [map_sum, Prod.fst_sum, map_zero, Prod.fst_zero] at e
    have hs : ∀ o, (PsiM θ μ (g o • g0 o)).1 = (g o : ℂ) * (PsiM θ μ (g0 o)).1 := fun o => by
      rw [map_rat_smul, Prod.smul_fst, Rat.smul_def]
    rw [Fintype.sum_option] at e
    simp only [hs] at e
    simp only [g0, genM, hpΨ, hDΨ] at e
    have e' : (g none : ℂ) * x + dotL θ (fun h => ((g (some h) : ℚ) : ℂ)) * A = 0 := by
      rw [dotL_apply, Finset.sum_mul, ← e]
      congr 1
      exact Finset.sum_congr rfl fun h _ => by ring
    have hc : IsAlgebraic ℚ (dotL θ (fun h => ((g (some h) : ℚ) : ℂ))) :=
      mem_algebraicClosure_iff.mp (dot_rat_mem_alg hθalg _)
    by_cases hg : g none = 0
    · have hcA : dotL θ (fun h => ((g (some h) : ℚ) : ℂ)) * A = 0 := by
        rw [hg] at e'; simpa using e'
      have z := dot_rat_eq_zero hθ _ ((mul_eq_zero.mp hcA).resolve_right hA)
      rintro (_ | h)
      · exact hg
      · exact congrFun z h
    · exfalso
      have hg' : (g none : ℂ) ≠ 0 := by exact_mod_cast hg
      refine hx (-dotL θ (fun h => ((g (some h) : ℚ) : ℂ)) / (g none : ℂ)) ?_ ?_
      · rw [← mem_algebraicClosure_iff]
        exact div_mem (neg_mem (mem_algebraicClosure_iff.mpr hc))
          (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (g none)))
      · field_simp
        linear_combination e'
  set e := Fintype.equivFin (Option ι)
  set y' : Fin (Fintype.card (Option ι)) → TM ι Q := g0 ∘ e.symm with hy'
  have hli' : LinearIndependent ℚ y' := hli.comp _ e.symm.injective
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y')) = Fintype.card ι + 1 := by
    rw [finrank_span_eq_card hli']; simp
  have hmem : ∀ o, g0 o ∈ Submodule.span ℚ (Set.range y') := fun o =>
    Submodule.subset_span ⟨e o, by simp [hy']⟩
  -- `κ ≥ n`
  have hk : Fintype.card ι ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFM θ algQ lamS perS μ d₂).per) := by
    have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y')) :=
      FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
    let f : ι → ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFM θ algQ lamS perS μ d₂).per) := fun h =>
      ⟨g0 (some h), hmem _, hpp h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp
        (Submodule.span ℚ (Set.range y') ⊓ (gmFM θ algQ lamS perS μ d₂).per).subtype
      exact hli.comp some (Option.some_injective ι)
    simpa using hf.fintype_card_le_finrank
  -- `V''`, `W''`
  have hV : finrank ℂ (LinearMap.ker (phiM θ μ σ)) + 1 = finrank ℂ (TM ι Q) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (phiM θ μ σ)
    rw [LinearMap.range_eq_top.mpr (phiM_surjective θ μ σ), finrank_top, Module.finrank_self] at h1
    omega
  set W := Submodule.span ℂ (wGenM θ i0 T) with hWdef
  have hTker : ∀ q ∈ T, μ q = 0 := fun q hq => by
    have : q ∈ Submodule.span ℂ T := Submodule.subset_span hq
    rw [hT] at this; exact this
  have hWV : W ≤ LinearMap.ker (phiM θ μ σ) := by
    intro v hv
    have := wGenM_le_ker θ μ i0 h0 T hTker hv
    rw [LinearMap.mem_ker] at this ⊢
    rw [phiM_apply, this]; simp
  have hWlo : finrank ℂ (TM ι Q) ≤ finrank ℂ W + 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (PsiM θ μ)
    have h2 : finrank ℂ (LinearMap.range (PsiM θ μ)) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range (PsiM θ μ))
      simpa [Module.finrank_prod] using this
    have h3 := Submodule.finrank_mono (ker_PsiM_le μ h0 T hT.ge)
    rw [← hWdef] at h3
    omega
  have hWhi : finrank ℂ W + 1 ≤ finrank ℂ (TM ι Q) := by
    have := Submodule.finrank_mono hWV
    omega
  have hWrat : (gmFM θ algQ lamS perS μ d₂).Rational W := by
    refine ⟨wGenM θ i0 T, ?_, rfl⟩
    rintro _ ((⟨q, hq, rfl⟩ | ⟨j, rfl⟩) | h)
    · exact ⟨hTalg q hq, fun k => isAlgebraic_zero, isAlgebraic_zero⟩
    · refine ⟨halg0, fun k => ?_, isAlgebraic_zero⟩
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      exact ((hθalg i0).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)).sub
        ((hθalg j).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero))
    · rw [Set.mem_singleton_iff] at h
      subst h
      refine ⟨halg0, fun k => ?_, isAlgebraic_one⟩
      simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      exact (hθalg i0).inv.neg.mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)
  have hVmem : ∀ o, g0 o ∈ LinearMap.ker (phiM θ μ σ) := by
    rintro (_ | h)
    · rw [LinearMap.mem_ker, phiM_apply]; simp [g0, genM, hDΨ]
    · rw [LinearMap.mem_ker, phiM_apply]; simp [g0, genM, hpΨ]
  have hlamMem : ∀ o, g0 o ∈ (gmFM θ algQ lamS perS μ d₂).lam := by
    rintro (_ | h)
    exacts [hDl, hpl h]
  -- apply W88 §5d
  obtain ⟨S, hsub, hne, hle⟩ := hW (LinearMap.ker (phiM θ μ σ)) W _ y'
    (by omega) hWV hWrat
    (fun i => ⟨hVmem (e.symm i), hlamMem (e.symm i)⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y')) : ℤ) >
        ((Fintype.card ι : ℕ) + 2 * (d₂ : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmFM θ algQ lamS perS μ d₂).per)) *
          ((finrank ℂ (TM ι Q) : ℤ) - 1 - finrank ℂ W))
      rw [hfinY]
      have hcase : ((finrank ℂ (TM ι Q) : ℤ) - 1 - finrank ℂ W) = 0 ∨
          ((finrank ℂ (TM ι Q) : ℤ) - 1 - finrank ℂ W) = 1 := by omega
      rcases hcase with hc | hc <;> rw [hc] <;> push_cast <;> omega)
  rcases hsub with rfl | ⟨v, hvS, ⟨hv1, hv2, hv3⟩, hv⟩
  · exact hne rfl
  · have hvV := hle hvS
    rw [LinearMap.mem_ker, phiM_apply] at hvV
    have h1 : IsAlgebraic ℚ (PsiM θ μ v).1 := by
      rw [PsiM_apply]; exact hμ _ hv1
    have h2 : IsAlgebraic ℚ (PsiM θ μ v).2 := by
      rw [PsiM_apply, ← mem_algebraicClosure_iff, dotL_apply]
      exact add_mem (sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
        (mem_algebraicClosure_iff.mpr (hv2 j))) (mem_algebraicClosure_iff.mpr hv3)
    by_cases hP1 : (PsiM θ μ v).1 = 0
    · apply hv
      have hP2 : (PsiM θ μ v).2 = 0 := by rw [hP1, mul_zero, sub_zero] at hvV; exact hvV
      exact Prod.ext hP1 hP2
    · apply hσ
      have : σ = (PsiM θ μ v).2 / (PsiM θ μ v).1 := by field_simp; linear_combination -hvV
      rw [this, ← mem_algebraicClosure_iff]
      exact div_mem (mem_algebraicClosure_iff.mpr h2) (mem_algebraicClosure_iff.mpr h1)

end Main

end CM4E.Gen
