/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs
import CM4E.Waldschmidt

/-!
# The common frame of Theorems MG and MG♮: `G'' = G_m^{2n} × G₂`

Both proofs (paper, Remarks 15 and 20) apply W88 §5d to a group `G'' = G_m^{2n} × G₂` with tangent space
`T = ((ι → ℂ) × (ι → ℂ)) × Q` (`ι` indexes a `ℚ`-basis `θ` of a number field `K`, `n = |ι|`, `Q = T(G₂)`), the map
`Ψ''((x, y), q) = (θᵀx, θᵀy + λ(q))` for a linear form `λ` on `Q`, and the hyperplane `V'' = Ψ''⁻¹(ℂ(1, s))`.
This file proves the contradiction once, for any `(Q, λ)`:

* `gmF` is the group model; `sub` says: a subgroup is `T_L × H` with `H = 0` or `λ ≠ 0` on `T_H`.
* `frame_false`: if `s` is transcendental, `dim Q < n`, `λ` is onto with algebraically spanned kernel, the period
  lifts `qh h` exist with `λ(qh h) = s·2πiθ_h`, and `(X_k, Y_k = sX_k)` (`k = 1, 2`) are pairs of logarithms with
  `Y₁, Y₂` `ℚ`-independent, then `HyperplaneKappa (gmF …)` is contradictory.

The count: `m = 3n`, `κ ≥ n`, `d₁ = 2n`, `d₂ = dim Q`, `d − 1 − t ≤ 1`, so `(5.4)` holds as soon as `dim Q < n`.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- The tangent space `((ι → ℂ) × (ι → ℂ)) × Q` of `G_m^{2n} × G₂`. -/
abbrev TF (ι Q : Type) [AddCommGroup Q] := ((ι → ℂ) × (ι → ℂ)) × Q

/-- `x ↦ θᵀx`. -/
noncomputable def dotL (θ : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ j, θ j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

lemma dotL_apply (θ : ι → ℂ) (x : ι → ℂ) : dotL θ x = ∑ j, θ j * x j := rfl

lemma dotL_single (θ : ι → ℂ) (j : ι) (x : ℂ) : dotL θ (Pi.single j x) = θ j * x := by
  simp [dotL_apply, Pi.single_apply]

/-- A logarithm in the first `G_m^n` block, slot `j`. -/
def tor1 (j : ι) (x : ℂ) : TF ι Q := ((Pi.single j x, 0), 0)
/-- A logarithm in the second `G_m^n` block, slot `j`. -/
def tor2 (j : ι) (x : ℂ) : TF ι Q := ((0, Pi.single j x), 0)
/-- A vector of `Q`. -/
def qv (q : Q) : TF ι Q := ((0, 0), q)

/-- Algebraic coordinates (`algQ` is the `ℚ̄`-structure of `Q`). -/
def algF (algQ : Q → Prop) (v : TF ι Q) : Prop :=
  (∀ j, IsAlgebraic ℚ (v.1.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.1.2 j)) ∧ algQ v.2

/-- Generators of `lam`: logarithms of algebraic numbers in one toric slot, and the periods of `G₂`. -/
def lamGen (perQ : Set Q) : Set (TF ι Q) :=
  {v | ∃ j x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 j x} ∪
    {v | ∃ j x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 j x} ∪ qv '' perQ

/-- Generators of the periods: `2πi` in one toric slot, and the periods of `G₂`. -/
noncomputable def perGen (perQ : Set Q) : Set (TF ι Q) :=
  Set.range (fun j : ι => (tor1 j (2 * Real.pi * I) : TF ι Q)) ∪
    Set.range (fun j : ι => (tor2 j (2 * Real.pi * I) : TF ι Q)) ∪ qv '' perQ

/-- The Lie algebra of the subtorus `T_L`, `L ⊂ ℚ^{2n}`. -/
noncomputable def torSub (L : Submodule ℚ ((ι → ℚ) × (ι → ℚ))) : Submodule ℂ ((ι → ℂ) × (ι → ℂ)) :=
  Submodule.span ℂ ((fun l : (ι → ℚ) × (ι → ℚ) => ((fun j => ((l.1 j : ℚ) : ℂ)), (fun j => ((l.2 j : ℚ) : ℂ)))) ''
    (L : Set ((ι → ℚ) × (ι → ℚ))))

/-- **The group model of `G_m^{2n} × G₂`.** Sound when: `algQ`, `perQ` are the `ℚ̄`-structure and (generators of the
`ℚ`-span of) the periods of `G₂`; `G₂` has no `G_a` or `G_m` factor; and every nonzero connected algebraic subgroup of
`G₂` has a tangent vector with `λ ≠ 0` (connected subgroups of `G_m^{2n} × G₂` are products, as there are no nonzero
homomorphisms between a torus and `G₂`). -/
noncomputable def gmF (algQ : Q → Prop) (perQ : Set Q) (lam : Q →ₗ[ℂ] ℂ) [FiniteDimensional ℂ Q] :
    GroupModel (TF ι Q) where
  d₁ := 2 * Fintype.card ι
  d₂ := finrank ℂ Q
  alg := algF algQ
  lam := (Submodule.span ℚ (lamGen (ι := ι) perQ) : Set (TF ι Q))
  per := Submodule.span ℚ (perGen (ι := ι) perQ)
  sub := fun S => ∃ (L : Submodule ℚ ((ι → ℚ) × (ι → ℚ))) (h : Submodule ℂ Q),
    (h = ⊥ ∨ ∃ x ∈ h, lam x ≠ 0) ∧ S = (torSub L).prod h

/-! ## `V''`, `W''` -/

section Proof

variable (θ : ι → ℂ) (lam : Q →ₗ[ℂ] ℂ)

/-- `θᵀy + λ(q) − s θᵀx`; its kernel is `V'' = Ψ''⁻¹(ℂ(1, s))`. -/
noncomputable def phiF (s : ℂ) : TF ι Q →ₗ[ℂ] ℂ :=
  dotL θ ∘ₗ (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _) + lam ∘ₗ LinearMap.snd ℂ _ _ -
    s • (dotL θ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _))

lemma phiF_apply (s : ℂ) (v : TF ι Q) :
    phiF θ lam s v = dotL θ v.1.2 + lam v.2 - s * dotL θ v.1.1 := by
  simp [phiF]

/-- `Ψ'' = (θᵀx, θᵀy + λ(q))`. -/
noncomputable def PsiF : TF ι Q →ₗ[ℂ] ℂ × ℂ :=
  (dotL θ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)).prod
    (dotL θ ∘ₗ (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _) + lam ∘ₗ LinearMap.snd ℂ _ _)

lemma PsiF_apply (v : TF ι Q) : PsiF θ lam v = (dotL θ v.1.1, dotL θ v.1.2 + lam v.2) := by
  simp [PsiF]

lemma finrank_TF [FiniteDimensional ℂ Q] :
    finrank ℂ (TF ι Q) = 2 * Fintype.card ι + finrank ℂ Q := by
  simp [TF, Module.finrank_prod, two_mul]

variable {θ} in
lemma phiF_surjective {i0 : ι} (h0 : θ i0 ≠ 0) (s : ℂ) : Function.Surjective (phiF θ lam s) :=
  fun w => ⟨tor2 i0 (w / θ i0), by
    simp only [phiF_apply, tor2, dotL_single, map_zero, mul_zero, sub_zero, add_zero]
    field_simp⟩

variable {θ} in
lemma finrank_ker_phiF [FiniteDimensional ℂ Q] {i0 : ι} (h0 : θ i0 ≠ 0) (s : ℂ) :
    finrank ℂ (LinearMap.ker (phiF θ lam s)) + 1 = finrank ℂ (TF ι Q) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiF θ lam s)
  rw [LinearMap.range_eq_top.mpr (phiF_surjective lam h0 s), finrank_top, Module.finrank_self] at h1
  omega

variable {θ} in
lemma PsiF_surjective {i0 : ι} (h0 : θ i0 ≠ 0) : Function.Surjective (PsiF θ lam) := by
  rintro ⟨a, b⟩
  refine ⟨tor1 i0 (a / θ i0) + tor2 i0 (b / θ i0), ?_⟩
  simp only [PsiF_apply, tor1, tor2, Prod.fst_add, Prod.snd_add, add_zero, zero_add, map_add,
    dotL_single, map_zero, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> field_simp

/-- Algebraic vectors spanning `W'' = ker Ψ''`. -/
noncomputable def wGen (i0 : ι) (q₁ : Q) (T : Set Q) : Set (TF ι Q) :=
  Set.range (fun j : ι => ((((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ι → ℂ)), (0 : Q))) ∪
    Set.range (fun j : ι => (((0 : ι → ℂ), (Pi.single j 1 : ι → ℂ)), -(θ j) • q₁)) ∪ qv '' T

lemma wGen_le_V (i0 : ι) (q₁ : Q) (hq₁ : lam q₁ = 1) (T : Set Q) (hT : ∀ q ∈ T, lam q = 0) (s : ℂ) :
    Submodule.span ℂ (wGen θ i0 q₁ T) ≤ LinearMap.ker (phiF θ lam s) := by
  rw [Submodule.span_le]
  rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩)
  · simp [phiF_apply, map_sub, map_smul, dotL_single, mul_comm]
  · simp [phiF_apply, map_smul, dotL_single, hq₁]
  · simp [phiF_apply, qv, hT q hq]

lemma sum_smul_single (y : ι → ℂ) : ∑ j, y j • (Pi.single j (1 : ℂ) : ι → ℂ) = y := by
  funext k; simp [Finset.sum_apply, Pi.single_apply]

variable {θ} in
lemma decomp_x {i0 : ι} (h0 : θ i0 ≠ 0) (x : ι → ℂ) (hx : dotL θ x = 0) :
    ∑ j, (x j / θ i0) • ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ) = x := by
  simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
  have h1 : ∀ j, (x j / θ i0 * θ i0) = x j := fun j => div_mul_cancel₀ _ h0
  simp only [h1, sum_smul_single]
  rw [← Finset.sum_smul]
  have h2 : ∑ j, x j / θ i0 * θ j = dotL θ x / θ i0 := by
    rw [dotL_apply, Finset.sum_div]; congr 1; funext j; ring
  rw [h2, hx, zero_div, zero_smul, sub_zero]

variable {θ} in
lemma ker_PsiF_le_W {i0 : ι} (h0 : θ i0 ≠ 0) (q₁ : Q) (hq₁ : lam q₁ = 1) (T : Set Q)
    (hT : Submodule.span ℂ T = LinearMap.ker lam) :
    LinearMap.ker (PsiF θ lam) ≤ Submodule.span ℂ (wGen θ i0 q₁ T) := by
  intro v hv
  rw [LinearMap.mem_ker, PsiF_apply, Prod.mk.injEq] at hv
  obtain ⟨hx, hy⟩ := hv
  have hg1 : ∀ j, ((((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ι → ℂ)), (0 : Q)) ∈
      Submodule.span ℂ (wGen θ i0 q₁ T) := fun j => Submodule.subset_span (Or.inl (Or.inl ⟨j, rfl⟩))
  have hg2 : ∀ j, (((0 : ι → ℂ), (Pi.single j 1 : ι → ℂ)), -(θ j) • q₁) ∈
      Submodule.span ℂ (wGen θ i0 q₁ T) := fun j => Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩))
  have hq : v.2 + dotL θ v.1.2 • q₁ ∈ Submodule.span ℂ T := by
    rw [hT, LinearMap.mem_ker, map_add, map_smul, hq₁, smul_eq_mul, mul_one, add_comm]; exact hy
  have hqv : (qv (v.2 + dotL θ v.1.2 • q₁) : TF ι Q) ∈ Submodule.span ℂ (wGen θ i0 q₁ T) := by
    have : Submodule.map (LinearMap.inr ℂ ((ι → ℂ) × (ι → ℂ)) Q) (Submodule.span ℂ T) ≤
        Submodule.span ℂ (wGen θ i0 q₁ T) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span (Or.inr ⟨q, hq, rfl⟩)
    exact this ⟨_, hq, rfl⟩
  have hdec : v = ∑ j, (v.1.1 j / θ i0) •
        ((((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ι → ℂ)), (0 : Q)) +
      ∑ j, v.1.2 j • (((0 : ι → ℂ), (Pi.single j 1 : ι → ℂ)), -(θ j) • q₁) +
      qv (v.2 + dotL θ v.1.2 • q₁) := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp only [qv, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, Prod.smul_mk, smul_zero,
        Finset.sum_const_zero, add_zero]
      exact (decomp_x h0 _ hx).symm
    · simp only [qv, Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
        Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add, add_zero]
      exact (sum_smul_single _).symm
    · simp only [qv, Prod.snd_add, Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero,
        zero_add, smul_neg, smul_smul, Finset.sum_neg_distrib]
      rw [← Finset.sum_smul, dotL_apply]
      have : ∑ i, v.1.2 i * -θ i = -∑ j, θ j * v.1.2 j := by
        rw [← Finset.sum_neg_distrib]; congr 1; funext j; ring
      rw [this, neg_smul]; abel
  rw [hdec]
  exact add_mem (add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hg1 j))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hg2 j))) hqv

end Proof

/-! ## The `3n` generators -/

section Gens

/-- The generators of `Y''`: `n` period lifts `(2πi e_h, 0; qh h)` and the data lifts `(X_k e_h, Y_k e_h; 0)`. -/
noncomputable def genF (qh : ι → Q) (X₁ Y₁ X₂ Y₂ : ℂ) : Fin 3 × ι → TF ι Q := fun p =>
  ![tor1 p.2 (2 * Real.pi * I) + qv (qh p.2), tor1 p.2 X₁ + tor2 p.2 Y₁, tor1 p.2 X₂ + tor2 p.2 Y₂] p.1

lemma genF_zero (qh : ι → Q) (X₁ Y₁ X₂ Y₂ : ℂ) (h : ι) :
    genF qh X₁ Y₁ X₂ Y₂ (0, h) = tor1 h (2 * Real.pi * I) + qv (qh h) := rfl
lemma genF_one (qh : ι → Q) (X₁ Y₁ X₂ Y₂ : ℂ) (h : ι) :
    genF qh X₁ Y₁ X₂ Y₂ (1, h) = tor1 h X₁ + tor2 h Y₁ := rfl
lemma genF_two (qh : ι → Q) (X₁ Y₁ X₂ Y₂ : ℂ) (h : ι) :
    genF qh X₁ Y₁ X₂ Y₂ (2, h) = tor1 h X₂ + tor2 h Y₂ := rfl

lemma genF_mem_V (θ : ι → ℂ) (lam : Q →ₗ[ℂ] ℂ) (s : ℂ) (qh : ι → Q)
    (hqh : ∀ h, lam (qh h) = s * (2 * Real.pi * I * θ h)) (X₁ Y₁ X₂ Y₂ : ℂ)
    (h₁ : Y₁ = s * X₁) (h₂ : Y₂ = s * X₂) (p : Fin 3 × ι) :
    genF qh X₁ Y₁ X₂ Y₂ p ∈ LinearMap.ker (phiF θ lam s) := by
  obtain ⟨a, h⟩ := p
  rw [LinearMap.mem_ker, phiF_apply]
  fin_cases a
  · simp [genF_zero, tor1, qv, dotL_single, hqh]; ring
  · simp [genF_one, tor1, tor2, dotL_single, h₁]; ring
  · simp [genF_two, tor1, tor2, dotL_single, h₂]; ring

lemma genF_linearIndependent (qh : ι → Q) (X₁ Y₁ X₂ Y₂ : ℂ)
    (hind : LinearIndependent ℚ ![Y₁, Y₂]) :
    LinearIndependent ℚ (genF qh X₁ Y₁ X₂ Y₂) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hli := Fintype.linearIndependent_iff.mp hind
  have hdata : ∀ h, g (1, h) = 0 ∧ g (2, h) = 0 := by
    intro h
    have e := congrArg (fun v : TF ι Q => v.1.2 h) hg
    simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, genF_zero, genF_one, genF_two,
      tor1, tor2, qv, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, Pi.single_apply,
      Prod.fst_zero, Prod.snd_zero, add_zero, zero_add, smul_zero, Finset.sum_const_zero,
      smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true, Prod.zero_eq_mk] at e
    have := hli ![g (1, h), g (2, h)] (by simpa [Fin.sum_univ_two] using e)
    exact ⟨by simpa using this 0, by simpa using this 1⟩
  have hper : ∀ h, g (0, h) = 0 := by
    intro h
    have e := congrArg (fun v : TF ι Q => v.1.1 h) hg
    simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_three, genF_zero, genF_one, genF_two, tor1, tor2, qv, Prod.fst_add, Pi.add_apply,
      Pi.zero_apply, Pi.single_apply, Prod.fst_zero, add_zero, zero_add, smul_zero,
      Finset.sum_const_zero, smul_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      (hdata _).1, (hdata _).2, zero_smul, Prod.zero_eq_mk] at e
    rw [Rat.smul_def] at e
    have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact_mod_cast (mul_eq_zero.mp e).resolve_right h2pi
  rintro ⟨a, h⟩
  fin_cases a
  · exact hper h
  · exact (hdata h).1
  · exact (hdata h).2

lemma qv_mem_span (perQ : Set Q) (S : Set (TF ι Q)) (hS : qv '' perQ ⊆ S) {q : Q}
    (hq : q ∈ Submodule.span ℚ perQ) : (qv q : TF ι Q) ∈ Submodule.span ℚ S := by
  have : Submodule.map (LinearMap.inr ℚ ((ι → ℂ) × (ι → ℂ)) Q) (Submodule.span ℚ perQ) ≤
      Submodule.span ℚ S := by
    rw [Submodule.map_span, Submodule.span_le]
    exact fun v hv => Submodule.subset_span (hS hv)
  exact this ⟨q, hq, rfl⟩

lemma genF_mem_lam (perQ : Set Q) (qh : ι → Q) (hqh : ∀ h, qh h ∈ Submodule.span ℚ perQ)
    (X₁ Y₁ X₂ Y₂ : ℂ) (hX₁ : IsAlgebraic ℚ (Complex.exp X₁)) (hY₁ : IsAlgebraic ℚ (Complex.exp Y₁))
    (hX₂ : IsAlgebraic ℚ (Complex.exp X₂)) (hY₂ : IsAlgebraic ℚ (Complex.exp Y₂)) (p : Fin 3 × ι) :
    genF qh X₁ Y₁ X₂ Y₂ p ∈ Submodule.span ℚ (lamGen (ι := ι) perQ) := by
  have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
    rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  have t1 : ∀ h x, IsAlgebraic ℚ (Complex.exp x) →
      (tor1 h x : TF ι Q) ∈ Submodule.span ℚ (lamGen (ι := ι) perQ) := fun h x hx =>
    Submodule.subset_span (Or.inl (Or.inl ⟨h, x, hx, rfl⟩))
  have t2 : ∀ h x, IsAlgebraic ℚ (Complex.exp x) →
      (tor2 h x : TF ι Q) ∈ Submodule.span ℚ (lamGen (ι := ι) perQ) := fun h x hx =>
    Submodule.subset_span (Or.inl (Or.inr ⟨h, x, hx, rfl⟩))
  obtain ⟨a, h⟩ := p
  fin_cases a
  · exact add_mem (t1 h _ h2pi) (qv_mem_span perQ _ (fun v hv => Or.inr hv) (hqh h))
  · exact add_mem (t1 h _ hX₁) (t2 h _ hY₁)
  · exact add_mem (t1 h _ hX₂) (t2 h _ hY₂)

lemma genF_zero_mem_per (perQ : Set Q) (qh : ι → Q) (hqh : ∀ h, qh h ∈ Submodule.span ℚ perQ)
    (X₁ Y₁ X₂ Y₂ : ℂ) (h : ι) :
    genF qh X₁ Y₁ X₂ Y₂ (0, h) ∈ Submodule.span ℚ (perGen (ι := ι) perQ) :=
  add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩)))
    (qv_mem_span perQ _ (fun v hv => Or.inr hv) (hqh h))

end Gens

/-! ## The contradiction -/

section Main

lemma isAlgebraic_ite (p : Prop) [Decidable p] {a b : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) :
    IsAlgebraic ℚ (if p then a else b) := by
  split_ifs <;> assumption

lemma dot_rat_mem_alg {θ : ι → ℂ} (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (l : ι → ℚ) :
    dotL θ (fun j => ((l j : ℚ) : ℂ)) ∈ algebraicClosure ℚ ℂ := by
  have hq : ∀ r : ℚ, (r : ℂ) ∈ algebraicClosure ℚ ℂ := fun r =>
    mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap r)
  rw [dotL_apply]
  exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j)) (hq (l j))

lemma dot_rat_eq_zero {θ : ι → ℂ} (hθ : LinearIndependent ℚ θ) (l : ι → ℚ)
    (h : dotL θ (fun j => ((l j : ℚ) : ℂ)) = 0) : l = 0 := by
  funext j
  refine Fintype.linearIndependent_iff.mp hθ l ?_ j
  rw [dotL_apply] at h
  simpa [Rat.smul_def, mul_comm] using h

omit [Fintype ι] [DecidableEq ι] in
lemma torSub_bot : torSub (⊥ : Submodule ℚ ((ι → ℚ) × (ι → ℚ))) = ⊥ := by
  simp only [torSub, Submodule.bot_coe, Set.image_singleton]
  rw [Submodule.span_singleton_eq_bot]
  refine Prod.ext ?_ ?_ <;> funext j <;> simp

/-- **The frame contradiction.** Under the hypothesis `HyperplaneKappa (gmF …)` (W88 §5d for `G_m^{2n} × G₂`), the
listed data cannot exist. -/
theorem frame_false [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (perQ : Set Q) (lam : Q →ₗ[ℂ] ℂ)
    (hW : HyperplaneKappa (gmF (ι := ι) algQ perQ lam))
    (hdQ : finrank ℂ Q < Fintype.card ι)
    (halg0 : algQ 0) (halgS : ∀ (c : ℂ) (q : Q), IsAlgebraic ℚ c → algQ q → algQ (c • q))
    (q₁ : Q) (hq₁ : algQ q₁) (hlq₁ : lam q₁ = 1)
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = LinearMap.ker lam)
    (s : ℂ) (hs : Transcendental ℚ s)
    (qh : ι → Q) (hqh : ∀ h, qh h ∈ Submodule.span ℚ perQ)
    (hlqh : ∀ h, lam (qh h) = s * (2 * Real.pi * I * θ h))
    (X₁ Y₁ X₂ Y₂ : ℂ) (hX₁ : IsAlgebraic ℚ (Complex.exp X₁)) (hY₁ : IsAlgebraic ℚ (Complex.exp Y₁))
    (hX₂ : IsAlgebraic ℚ (Complex.exp X₂)) (hY₂ : IsAlgebraic ℚ (Complex.exp Y₂))
    (h₁ : Y₁ = s * X₁) (h₂ : Y₂ = s * X₂) (hind : LinearIndependent ℚ ![Y₁, Y₂]) : False := by
  have hcard : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hdQ
  obtain ⟨i0⟩ : Nonempty ι := Fintype.card_pos_iff.mp hcard
  have h0 : θ i0 ≠ 0 := hθ.ne_zero i0
  -- the generators, indexed by `Fin m`
  have hli := genF_linearIndependent qh X₁ Y₁ X₂ Y₂ hind
  set e := Fintype.equivFin (Fin 3 × ι)
  set y' : Fin (Fintype.card (Fin 3 × ι)) → TF ι Q := genF qh X₁ Y₁ X₂ Y₂ ∘ e.symm with hy'
  have hli' : LinearIndependent ℚ y' := hli.comp _ e.symm.injective
  have hfin : finrank ℚ (Submodule.span ℚ (Set.range y')) = 3 * Fintype.card ι := by
    rw [finrank_span_eq_card hli']; simp [Fintype.card_prod]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y')) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hmem : ∀ p, genF qh X₁ Y₁ X₂ Y₂ p ∈ Submodule.span ℚ (Set.range y') := fun p =>
    Submodule.subset_span ⟨e p, by simp [hy']⟩
  -- `κ ≥ n`
  have hk : Fintype.card ι ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmF (ι := ι) algQ perQ lam).per) := by
    let f : ι → ↥(Submodule.span ℚ (Set.range y') ⊓ (gmF (ι := ι) algQ perQ lam).per) := fun h =>
      ⟨genF qh X₁ Y₁ X₂ Y₂ (0, h), hmem _, genF_zero_mem_per perQ qh hqh X₁ Y₁ X₂ Y₂ h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp
        (Submodule.span ℚ (Set.range y') ⊓ (gmF (ι := ι) algQ perQ lam).per).subtype
      exact hli.comp (fun h : ι => ((0 : Fin 3), h)) (fun a b hab => by simpa using hab)
    simpa using hf.fintype_card_le_finrank
  -- `V''` and `W''`
  have hTF := finrank_TF (ι := ι) (Q := Q)
  have hV := finrank_ker_phiF lam h0 s
  set W := Submodule.span ℂ (wGen θ i0 q₁ T) with hWdef
  have hWV : W ≤ LinearMap.ker (phiF θ lam s) :=
    wGen_le_V θ lam i0 q₁ hlq₁ T (fun q hq => by
      have : q ∈ Submodule.span ℂ T := Submodule.subset_span hq
      rw [hT] at this; exact this) s
  have hWlo : finrank ℂ (TF ι Q) ≤ finrank ℂ W + 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (PsiF θ lam)
    rw [LinearMap.range_eq_top.mpr (PsiF_surjective lam h0), finrank_top] at h1
    have h2 : finrank ℂ (ℂ × ℂ) = 2 := by simp [Module.finrank_prod]
    have h3 := Submodule.finrank_mono (ker_PsiF_le_W lam h0 q₁ hlq₁ T hT)
    rw [← hWdef] at h3
    omega
  have hWhi : finrank ℂ W + 1 ≤ finrank ℂ (TF ι Q) := by
    have := Submodule.finrank_mono hWV
    omega
  have hWrat : (gmF (ι := ι) algQ perQ lam).Rational W := by
    refine ⟨wGen θ i0 q₁ T, ?_, rfl⟩
    rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩)
    · refine ⟨fun k => ?_, fun k => isAlgebraic_zero, halg0⟩
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      exact ((hθalg i0).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)).sub
        ((hθalg j).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero))
    · refine ⟨fun k => isAlgebraic_zero, fun k => ?_, halgS _ _ (hθalg j).neg hq₁⟩
      simp only [Pi.single_apply]
      exact isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero
    · exact ⟨fun k => isAlgebraic_zero, fun k => isAlgebraic_zero, hTalg q hq⟩
  -- apply W88 §5d
  obtain ⟨S, ⟨L, h, hh, rfl⟩, hne, hle⟩ := hW (LinearMap.ker (phiF θ lam s)) W _ y'
    (by omega) hWV hWrat
    (fun i => ⟨genF_mem_V θ lam s qh hlqh X₁ Y₁ X₂ Y₂ h₁ h₂ _,
      genF_mem_lam perQ qh hqh X₁ Y₁ X₂ Y₂ hX₁ hY₁ hX₂ hY₂ _⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y')) : ℤ) >
        ((2 * Fintype.card ι : ℕ) + 2 * (finrank ℂ Q : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmF (ι := ι) algQ perQ lam).per)) *
          ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ W))
      rw [hfin]
      have hcase : ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ W) = 0 ∨
          ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ W) = 1 := by omega
      rcases hcase with hc | hc <;> rw [hc] <;> push_cast <;> omega)
  rcases hh with rfl | ⟨x, hx, hlx⟩
  · -- `S = T_L × 0`: a rational vector in `V''` forces `s ∈ ℚ̄`
    have hL : L ≠ ⊥ := by
      rintro rfl
      apply hne
      rw [torSub_bot, Submodule.prod_bot]
    obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff L).mp hL
    have hlm : (((fun j => ((l.1 j : ℚ) : ℂ)), (fun j => ((l.2 j : ℚ) : ℂ))), (0 : Q)) ∈
        (torSub L).prod (⊥ : Submodule ℂ Q) :=
      Submodule.mem_prod.mpr ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.zero_mem _⟩
    have hVl := hle hlm
    rw [LinearMap.mem_ker, phiF_apply, map_zero, add_zero] at hVl
    set A := dotL θ (fun j => ((l.1 j : ℚ) : ℂ))
    set B := dotL θ (fun j => ((l.2 j : ℚ) : ℂ))
    by_cases hA : A = 0
    · have h1 : l.1 = 0 := dot_rat_eq_zero hθ _ hA
      have hB : B = 0 := by rw [hA, mul_zero, sub_zero] at hVl; exact hVl
      have h2 : l.2 = 0 := dot_rat_eq_zero hθ _ hB
      exact hl0 (Prod.ext h1 h2)
    · apply hs
      have hsAB : s = B / A := by field_simp; linear_combination -hVl
      rw [hsAB, ← mem_algebraicClosure_iff]
      exact div_mem (dot_rat_mem_alg hθalg _) (dot_rat_mem_alg hθalg _)
  · -- `λ ≠ 0` on `T_H`
    have hxm : (qv x : TF ι Q) ∈ (torSub L).prod h :=
      Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hx⟩
    have hVx := hle hxm
    rw [LinearMap.mem_ker, phiF_apply] at hVx
    simp [qv] at hVx
    exact hlx hVx

end Main

end CM4E.Gen
