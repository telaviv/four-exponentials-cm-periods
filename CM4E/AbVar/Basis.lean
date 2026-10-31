/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Adapted bases over a field of any degree

For an algebraic `α ∈ ℂ` of degree `d` (`F = ℚ(α)`) and `b : Fin r → ℂ`, put `θ(j, e) = α^e b j` (`e < d`).
`IsAdaptedBasisD α d b` says that `θ` is a `ℚ`-basis of a number field `K = span_ℚ θ ⊂ ℂ`, i.e. `b` is an `F`-basis of
`K`. This generalises `CM4E/Gen/Basis.lean` (`d = 2`) to the CM fields of `CM4E/AbVar/` (e.g. `ℚ(ζ₇)`, `d = 6`).
`exists_adapted_basisD`: for every finite set of algebraic numbers there is such a `b` with the set inside `K`
(take `K = F(S)`, a `F`-basis `b` of `K`, and the power basis of `F`).
-/

open Complex Polynomial IntermediateField

namespace CM4E.AbVar

/-- `θ(j, e) = α^e b j`. -/
def thetaD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) : Fin r × Fin d → ℂ :=
  fun p => α ^ (p.2 : ℕ) * b p.1

/-- `K = span_ℚ θ`. -/
noncomputable def KspanD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ (Set.range (thetaD α d b))

/-- `θ` is a `ℚ`-basis of a subfield `K` of `ℂ` consisting of algebraic numbers. -/
structure IsAdaptedBasisD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) : Prop where
  indep : LinearIndependent ℚ (thetaD α d b)
  one_mem : (1 : ℂ) ∈ KspanD α d b
  mul_mem : ∀ x ∈ KspanD α d b, ∀ y ∈ KspanD α d b, x * y ∈ KspanD α d b
  inv_mem : ∀ x ∈ KspanD α d b, x⁻¹ ∈ KspanD α d b
  alg : ∀ j, IsAlgebraic ℚ (b j)

lemma thetaD_isAlgebraic {α : ℂ} (hα : IsAlgebraic ℚ α) (d : ℕ) {r : ℕ} {b : Fin r → ℂ}
    (hb : ∀ j, IsAlgebraic ℚ (b j)) (p : Fin r × Fin d) : IsAlgebraic ℚ (thetaD α d b p) :=
  (hα.pow _).mul (hb _)

lemma KspanD_isAlgebraic {α : ℂ} (hα : IsAlgebraic ℚ α) {d r : ℕ} {b : Fin r → ℂ}
    (hb : ∀ j, IsAlgebraic ℚ (b j)) {x : ℂ} (hx : x ∈ KspanD α d b) : IsAlgebraic ℚ x := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  rw [← mem_algebraicClosure_iff]
  exact sum_mem fun j _ => by
    rw [Rat.smul_def]
    exact mul_mem (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (c j)))
      (mem_algebraicClosure_iff.mpr (thetaD_isAlgebraic hα d hb j))

/-- Coordinates of `x ∈ K` in the basis `θ` (arbitrary outside `K`). -/
noncomputable def coordsD (α : ℂ) (d : ℕ) {r : ℕ} (b : Fin r → ℂ) (x : ℂ) : Fin r × Fin d → ℚ :=
  Classical.epsilon (fun m : Fin r × Fin d → ℚ => ∑ j, (m j : ℂ) * thetaD α d b j = x)

lemma coordsD_spec {α : ℂ} {d r : ℕ} {b : Fin r → ℂ} {x : ℂ} (hx : x ∈ KspanD α d b) :
    ∑ j, (coordsD α d b x j : ℂ) * thetaD α d b j = x := by
  refine Classical.epsilon_spec (p := fun m : Fin r × Fin d → ℚ => ∑ j, (m j : ℂ) * thetaD α d b j = x) ?_
  obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  exact ⟨m, by simpa [Rat.smul_def] using hm⟩

theorem exists_adapted_basisD (α : ℂ) (hα : IsAlgebraic ℚ α) (S : Finset ℂ) (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ b : Fin r → ℂ, IsAdaptedBasisD α (minpoly ℚ α).natDegree b ∧
      ∀ s ∈ S, s ∈ KspanD α (minpoly ℚ α).natDegree b := by
  have hαi : IsIntegral ℚ α := hα.isIntegral
  set d := (minpoly ℚ α).natDegree
  set pb := adjoin.powerBasis hαi
  have hdim : pb.dim = d := by rw [adjoin.powerBasis_dim]
  set bk : Module.Basis (Fin d) ℚ ℚ⟮α⟯ := pb.basis.reindex (finCongr hdim)
  have hbk : ∀ e : Fin d, ((bk e : ℚ⟮α⟯) : ℂ) = α ^ (e : ℕ) := by
    intro e
    simp [bk, Module.Basis.reindex_apply, PowerBasis.coe_basis, pb, adjoin.powerBasis_gen]
  have : FiniteDimensional ℚ ℚ⟮α⟯ := adjoin.finiteDimensional hαi
  set K : IntermediateField ℚ⟮α⟯ ℂ := IntermediateField.adjoin ℚ⟮α⟯ (S : Set ℂ)
  have hT : ∀ x ∈ (S : Set ℂ), IsIntegral ℚ⟮α⟯ x := fun x hx => (hS x hx).isIntegral.tower_top
  have : Finite (S : Set ℂ) := S.finite_toSet.to_subtype
  have : FiniteDimensional ℚ⟮α⟯ K := finiteDimensional_adjoin hT
  have : Module.Free ℚ⟮α⟯ K := Module.Free.of_divisionRing _ _
  set r := Module.finrank ℚ⟮α⟯ K
  set b' := Module.finBasis ℚ⟮α⟯ K
  set B : Module.Basis (Fin r × Fin d) ℚ K := bk.smulTower' b'
  let f : K →ₗ[ℚ] ℂ := (K.val.restrictScalars ℚ).toLinearMap
  have hf : Function.Injective f := Subtype.val_injective
  set b : Fin r → ℂ := fun j => (b' j : ℂ)
  have htheta : thetaD α d b = f ∘ B := by
    funext ⟨j, e⟩
    simp [thetaD, B, Module.Basis.smulTower'_apply, f, b, Algebra.smul_def, hbk]
  have hspan : ∀ x, x ∈ KspanD α d b ↔ x ∈ K := by
    intro x
    rw [KspanD, htheta, Set.range_comp, Submodule.span_image, B.span_eq, Submodule.map_top,
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
  have hr : 1 ≤ r := Module.finrank_pos
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
    exact subset_adjoin ℚ⟮α⟯ (S : Set ℂ) hs

end CM4E.AbVar
