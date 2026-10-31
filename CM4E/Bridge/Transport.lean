/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Waldschmidt

/-!
# Transport of the hyperplane hypothesis along a linear isomorphism

`hyperplaneKappa_transport`: if `Φ : V₁ ≃ V₂` is a `ℂ`-linear isomorphism carrying the algebraic vectors, (a positive
integer multiple of each) logarithm and the periods of the model `G₁` into those of `G₂`, pulling back every nonzero
member of `G₂.sub` into `G₁.sub`, and `G₂.d₁ + 2G₂.d₂ ≤ G₁.d₁ + 2G₁.d₂`, then `HyperplaneKappa G₂` implies
`HyperplaneKappa G₁`. This is how the group models of `CM4E/Gen/` are reduced to the standard model of
`G_a^{d₀} × G_m^{d₁} × E^m` (`CM4E/Bridge/Std.lean`), whose hypothesis is proved in `lean_lsg`.

The integer multiple is needed because the models of `CM4E/Gen/` use the `ℚ`-span of their generators as logarithms,
while the standard model uses the logarithms themselves: `D•y` has the same `ℚ`-span, so ranks and `κ` are unchanged.
-/

open Module CM4E.Waldschmidt

namespace CM4E.Bridge

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [Module ℚ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  [Module ℚ V₂]

/-- The `ℚ`-linear map underlying `Φ`. -/
def ratMap (Φ : V₁ ≃ₗ[ℂ] V₂) : V₁ →ₗ[ℚ] V₂ := Φ.toLinearMap.toAddMonoidHom.toRatLinearMap

lemma ratMap_apply (Φ : V₁ ≃ₗ[ℂ] V₂) (v : V₁) : ratMap Φ v = Φ v := rfl

lemma ratMap_injective (Φ : V₁ ≃ₗ[ℂ] V₂) : Function.Injective (ratMap Φ) := Φ.injective

/-- **Transport of `HyperplaneKappa`.** -/
theorem hyperplaneKappa_transport [FiniteDimensional ℂ V₁] (G₁ : GroupModel V₁) (G₂ : GroupModel V₂)
    (Φ : V₁ ≃ₗ[ℂ] V₂) (halg : ∀ v, G₁.alg v → G₂.alg (Φ v))
    (hlam : ∀ v ∈ G₁.lam, ∃ D : ℕ, 0 < D ∧ Φ (D • v) ∈ G₂.lam)
    (hper : ∀ v ∈ G₁.per, Φ v ∈ G₂.per)
    (hsub : ∀ S, G₂.sub S → S ≠ ⊥ → G₁.sub (S.comap Φ.toLinearMap))
    (hd : G₂.d₁ + 2 * G₂.d₂ ≤ G₁.d₁ + 2 * G₁.d₂) (hW : HyperplaneKappa G₂) : HyperplaneKappa G₁ := by
  intro V W m y hV hWV hWr hy hcount
  choose D hD hDlam using fun i => hlam (y i) (hy i).2
  set f := ratMap Φ
  set y' : Fin m → V₂ := fun i => Φ (D i • y i)
  -- spans
  have hspanD : Submodule.span ℚ (Set.range fun i => D i • y i) = Submodule.span ℚ (Set.range y) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show D i • y i ∈ _
      rw [← Nat.cast_smul_eq_nsmul ℚ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have : y i = ((D i : ℚ)⁻¹) • (D i • y i) := by
        rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (hD i).ne'), one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan' : Submodule.span ℚ (Set.range y') = (Submodule.span ℚ (Set.range y)).map f := by
    rw [← hspanD, Submodule.map_span, ← Set.range_comp]
    rfl
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y')) = finrank ℚ (Submodule.span ℚ (Set.range y)) := by
    rw [hspan']
    exact (Submodule.equivMapOfInjective f (ratMap_injective Φ) _).finrank_eq.symm
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y')) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hk : finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G₁.per) ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ G₂.per) := by
    have hle : (Submodule.span ℚ (Set.range y) ⊓ G₁.per).map f ≤ Submodule.span ℚ (Set.range y') ⊓ G₂.per := by
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨by rw [hspan']; exact ⟨x, hx1, rfl⟩, hper x hx2⟩
    calc finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G₁.per)
        = finrank ℚ ↥((Submodule.span ℚ (Set.range y) ⊓ G₁.per).map f) :=
          (Submodule.equivMapOfInjective f (ratMap_injective Φ) _).finrank_eq
      _ ≤ _ := Submodule.finrank_mono hle
  -- dimensions
  have hfV : finrank ℂ (V.map Φ.toLinearMap) = finrank ℂ V := LinearEquiv.finrank_map_eq Φ V
  have hfW : finrank ℂ (W.map Φ.toLinearMap) = finrank ℂ W := LinearEquiv.finrank_map_eq Φ W
  have hfT : finrank ℂ V₂ = finrank ℂ V₁ := Φ.finrank_eq.symm
  have hWle : finrank ℂ W ≤ finrank ℂ V := Submodule.finrank_mono hWV
  obtain ⟨S, hsub2, hne, hle⟩ := hW (V.map Φ.toLinearMap) (W.map Φ.toLinearMap) m y'
    (by rw [hfV, hfT]; exact hV) (Submodule.map_mono hWV)
    (by
      obtain ⟨T, hT, rfl⟩ := hWr
      refine ⟨Φ '' T, ?_, Submodule.map_span _ _⟩
      rintro _ ⟨v, hv, rfl⟩
      exact halg v (hT v hv))
    (fun i => ⟨⟨D i • y i, by rw [← Nat.cast_smul_eq_nsmul ℂ]; exact V.smul_mem _ (hy i).1, rfl⟩, hDlam i⟩)
    (by
      rw [hfinY, hfT, hfW]
      have he : (0 : ℤ) ≤ (finrank ℂ V₁ : ℤ) - 1 - finrank ℂ W := by omega
      have h1 : ((G₂.d₁ : ℤ) + 2 * G₂.d₂ - finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ G₂.per)) ≤
          ((G₁.d₁ : ℤ) + 2 * G₁.d₂ - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G₁.per)) := by
        have := hd; omega
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 he) hcount)
  refine ⟨S.comap Φ.toLinearMap, hsub S hsub2 hne, ?_, ?_⟩
  · intro h
    apply hne
    rw [← Submodule.map_comap_eq_of_surjective Φ.surjective S, h, Submodule.map_bot]
  · intro x hx
    obtain ⟨v, hv, hvx⟩ := hle hx
    rw [← Φ.injective hvx]
    exact hv

end CM4E.Bridge
