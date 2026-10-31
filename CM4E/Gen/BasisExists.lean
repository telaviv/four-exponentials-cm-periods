/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CM4E.Gen.Basis

/-!
# Existence of adapted bases

For `α ∈ ℂ` generating an imaginary quadratic field `k = ℚ(α)` and a finite set `S` of algebraic
numbers, there is an adapted basis `b : Fin r → ℂ` (`r ≥ 2`) of a number field `K ⊇ k`
containing `S`: take `K = k(S, √2)`, a `k`-basis `b` of `K`, and the `ℚ`-basis `{1, α}` of `k`; then
`θ = {b j, α b j}` is a `ℚ`-basis of `K` (`Basis.smulTower'`). `r = [K : k] ≥ 2` because
`√2 ∉ k` (`k ∩ ℝ = ℚ`).
-/

open Complex Polynomial IntermediateField

namespace CM4E.Gen

/-- The minimal polynomial of a non-real `α` with `α² = p + qα` has degree `2`. -/
lemma natDegree_minpoly_eq_two {α : ℂ} (hα : IsIntegral ℚ α) (him : α.im ≠ 0) {p q : ℚ}
    (h : α ^ 2 = p + q * α) : (minpoly ℚ α).natDegree = 2 := by
  apply le_antisymm
  · have hP : (X ^ 2 - C q * X - C p : ℚ[X]).natDegree = 2 := by compute_degree!
    have hmon : (X ^ 2 - C q * X - C p : ℚ[X]).Monic := by monicity!
    have hroot : aeval α (X ^ 2 - C q * X - C p : ℚ[X]) = 0 := by
      simp [h]
    rw [← hP]
    exact natDegree_le_natDegree (minpoly.min ℚ α hmon hroot)
  · have h0 : 0 < (minpoly ℚ α).natDegree := minpoly.natDegree_pos hα
    have h1 : (minpoly ℚ α).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨c, hc⟩
      apply him
      rw [← hc]
      simp
    omega

/-- Elements of `ℚ(α)` are `u + v α` with `u, v ∈ ℚ` (for `α` of degree `2`). -/
lemma mem_adjoin_quadratic {α : ℂ} (hα : IsIntegral ℚ α) (hdeg : (minpoly ℚ α).natDegree = 2)
    (x : ℚ⟮α⟯) : ∃ u v : ℚ, (x : ℂ) = u + v * α := by
  set pb := adjoin.powerBasis hα
  have hdim : pb.dim = 2 := by rw [adjoin.powerBasis_dim]; exact hdeg
  set bk := pb.basis.reindex (finCongr hdim)
  refine ⟨bk.repr x 0, bk.repr x 1, ?_⟩
  have hs := bk.sum_repr x
  rw [Fin.sum_univ_two] at hs
  have h0 : ((bk 0 : ℚ⟮α⟯) : ℂ) = 1 := by
    simp [bk, Module.Basis.reindex_apply, PowerBasis.coe_basis]
  have h1 : ((bk 1 : ℚ⟮α⟯) : ℂ) = α := by
    simp [bk, Module.Basis.reindex_apply, PowerBasis.coe_basis, pb, adjoin.powerBasis_gen]
  have := congrArg (fun y : ℚ⟮α⟯ => (y : ℂ)) hs
  simp only [IntermediateField.coe_add, IntermediateField.coe_smul, h0, h1] at this
  rw [← this]
  simp [Rat.smul_def]

/-- `√2` (as a complex number) is integral over `ℚ`. -/
lemma isIntegral_sqrt_two : IsIntegral ℚ (((Real.sqrt 2 : ℝ)) : ℂ) := by
  refine ⟨X ^ 2 - C 2, by monicity!, ?_⟩
  rw [← aeval_def]
  simp [← Complex.ofReal_pow]

theorem exists_adapted_basis (α : ℂ) (hα : IsAlgebraic ℚ α) (him : α.im ≠ 0)
    (hquad : ∃ p q : ℚ, α ^ 2 = p + q * α)
    (S : Finset ℂ) (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ r : ℕ, 2 ≤ r ∧ ∃ b : Fin r → ℂ, IsAdaptedFieldBasis α b ∧ ∀ s ∈ S, s ∈ Kspan α b := by
  obtain ⟨p, q, hpq⟩ := hquad
  have hαi : IsIntegral ℚ α := hα.isIntegral
  have hdeg := natDegree_minpoly_eq_two hαi him hpq
  -- the `ℚ`-basis `{1, α}` of `k = ℚ(α)`
  set pb := adjoin.powerBasis hαi
  have hdim : pb.dim = 2 := by rw [adjoin.powerBasis_dim]; exact hdeg
  set bk : Module.Basis (Fin 2) ℚ ℚ⟮α⟯ := pb.basis.reindex (finCongr hdim)
  have h0 : ((bk 0 : ℚ⟮α⟯) : ℂ) = 1 := by
    simp [bk, Module.Basis.reindex_apply, PowerBasis.coe_basis]
  have h1 : ((bk 1 : ℚ⟮α⟯) : ℂ) = α := by
    simp [bk, Module.Basis.reindex_apply, PowerBasis.coe_basis, pb, adjoin.powerBasis_gen]
  have : FiniteDimensional ℚ ℚ⟮α⟯ := adjoin.finiteDimensional hαi
  -- `K = k(S, √2)`
  set s2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  set T : Set ℂ := (S : Set ℂ) ∪ {s2}
  set K : IntermediateField ℚ⟮α⟯ ℂ := IntermediateField.adjoin ℚ⟮α⟯ T
  have hT : ∀ x ∈ T, IsIntegral ℚ⟮α⟯ x := by
    rintro x (hx | hx)
    · exact (hS x hx).isIntegral.tower_top
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact isIntegral_sqrt_two.tower_top
  have : Finite T := (S.finite_toSet.union (Set.finite_singleton _)).to_subtype
  have : FiniteDimensional ℚ⟮α⟯ K := finiteDimensional_adjoin hT
  have : Module.Free ℚ⟮α⟯ K := Module.Free.of_divisionRing _ _
  set r := Module.finrank ℚ⟮α⟯ K
  set b' := Module.finBasis ℚ⟮α⟯ K
  set B : Module.Basis (Fin r × Fin 2) ℚ K := bk.smulTower' b'
  let f : K →ₗ[ℚ] ℂ := (K.val.restrictScalars ℚ).toLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  set b : Fin r → ℂ := fun j => (b' j : ℂ)
  have htheta : theta α b = f ∘ B := by
    funext ⟨j, i⟩
    fin_cases i
    · simp [theta, B, Module.Basis.smulTower'_apply, f, b, Algebra.smul_def, h0]
    · simp [theta, B, Module.Basis.smulTower'_apply, f, b, Algebra.smul_def, h1]
  have hspan : ∀ x, x ∈ Kspan α b ↔ x ∈ K := by
    intro x
    rw [Kspan, htheta, Set.range_comp, Submodule.span_image, B.span_eq, Submodule.map_top,
      LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have halg : ∀ x ∈ K, IsAlgebraic ℚ x := by
    intro x hx
    have : Module.Finite ℚ K := Module.Finite.trans ℚ⟮α⟯ K
    have : IsIntegral ℚ (⟨x, hx⟩ : K) := IsIntegral.of_finite ℚ _
    exact (this.map (K.val.restrictScalars ℚ)).isAlgebraic
  have hr : 2 ≤ r := by
    have hpos : 0 < r := Module.finrank_pos
    by_contra hlt
    have hr1 : r = 1 := by omega
    have hbot : K = ⊥ := IntermediateField.finrank_eq_one_iff.mp hr1
    have hs2 : s2 ∈ K := subset_adjoin ℚ⟮α⟯ T (Or.inr rfl)
    rw [hbot, IntermediateField.mem_bot] at hs2
    obtain ⟨c, hc⟩ := hs2
    obtain ⟨u, v, huv⟩ := mem_adjoin_quadratic hαi hdeg c
    have hc' : s2 = (u : ℂ) + (v : ℂ) * α := by rw [← hc, ← huv]; rfl
    have him' := congrArg Complex.im hc'
    have hre' := congrArg Complex.re hc'
    simp [s2] at him' hre'
    have hv : v = 0 := by
      rcases him' with h | h
      · exact h
      · exact absurd h him
    rw [hv] at hre'
    simp at hre'
    exact irrational_sqrt_two ⟨u, by rw [hre']⟩
  refine ⟨r, hr, b, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [htheta]
    exact B.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  · rw [hspan]
    exact K.one_mem
  · intro x hx y hy
    rw [hspan] at *
    exact K.mul_mem hx hy
  · intro x hx
    rw [hspan] at *
    exact K.inv_mem hx
  · intro j
    exact halg _ (b' j).2
  · intro s hs
    rw [hspan]
    exact subset_adjoin ℚ⟮α⟯ T (Or.inl hs)

end CM4E.Gen
