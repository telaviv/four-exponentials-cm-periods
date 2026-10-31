/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Common
import CM4E.Gen.Frame

/-!
# `P/π ∉ ℚ̄` from the frame hypothesis (lean_lsg ABVAR.md §1.6)

On the frame `gmF` of `CM4E/Gen/Frame.lean` (tangent space `((ι → ℂ) × (ι → ℂ)) × Q`, linear form `λ` on `Q`), the
same W88 §5d hypothesis that drives Theorems MG-A / MG♮-A also gives `P/π ∉ ℚ̄` for the period `P` that `λ` sees.

Suppose `λ(q₀) = θ_{j₀} απ` for a period `q₀` of `G₂` and an algebraic `α ≠ 0`. Take `μ ∈ ℚ̄` with `1, μ` independent
over `K = span_ℚ θ` and the hyperplane `V = W = ker φ`, `φ(x, y, q) = λ(q) − aθᵀx − aμθᵀy`, `a = α/(2i)`:
* `V` is `ℚ̄`-rational (`φ` has algebraic coefficients; `ker_eq_span_proj`);
* `y₀ = tor1 j₀ (2πi) + qv q₀ ∈ lam ∩ V`, `y₀ ≠ 0`;
* `(5.4)` reads `1 > (…) · 0`, as `d − 1 − dim W = 0`;
* so `V ⊇ T_L × h ≠ 0`. A vector `(0, x)` with `λx ≠ 0` is not in `V`, so `h = 0`; a rational toric vector `l ∈ V`
  has `θᵀl₁ + μθᵀl₂ = 0`, so `l = 0`. Contradiction (`frameW_false`).

`V` is toric-injective when `λ` is injective on `span_ℚ perQ` (`torInj_ker_phiW`).
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- `φ(x, y, q) = λ(q) − aθᵀx − aμθᵀy`. -/
noncomputable def phiW (θ : ι → ℂ) (lam : Q →ₗ[ℂ] ℂ) (a μ : ℂ) : TF ι Q →ₗ[ℂ] ℂ :=
  lam ∘ₗ LinearMap.snd ℂ _ _ - a • (dotL θ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)) -
    (a * μ) • (dotL θ ∘ₗ (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _))

omit [DecidableEq ι] [Module ℚ Q] in
lemma phiW_apply (θ : ι → ℂ) (lam : Q →ₗ[ℂ] ℂ) (a μ : ℂ) (v : TF ι Q) :
    phiW θ lam a μ v = lam v.2 - a * dotL θ v.1.1 - a * μ * dotL θ v.1.2 := by
  simp [phiW]

/-- `ker φ` is spanned by the projections `u − (φ u/φ e) e` of a spanning set. -/
lemma ker_eq_span_proj {E : Type*} [AddCommGroup E] [Module ℂ E] (φ : E →ₗ[ℂ] ℂ) (e : E) (he : φ e ≠ 0)
    (B : Set E) (hB : Submodule.span ℂ B = ⊤) :
    LinearMap.ker φ = Submodule.span ℂ ((fun u => u - (φ u / φ e) • e) '' B) := by
  set f : E →ₗ[ℂ] E := LinearMap.id - (φ e)⁻¹ • φ.smulRight e with hfdef
  have hf : ∀ v, f v = v - (φ v / φ e) • e := by
    intro v; simp [f, smul_smul, div_eq_inv_mul]
  have himg : (fun u => u - (φ u / φ e) • e) '' B = f '' B := Set.image_congr (fun v _ => (hf v).symm)
  rw [himg, Submodule.span_image, hB, Submodule.map_top]
  ext v
  constructor
  · intro hv
    rw [LinearMap.mem_ker] at hv
    exact ⟨v, by rw [hf, hv, zero_div, zero_smul, sub_zero]⟩
  · rintro ⟨w, rfl⟩
    rw [LinearMap.mem_ker, hf, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ he, sub_self]

lemma isAlgebraic_dotL {θ x : ι → ℂ} (hθ : ∀ j, IsAlgebraic ℚ (θ j)) (hx : ∀ j, IsAlgebraic ℚ (x j)) :
    IsAlgebraic ℚ (dotL θ x) := by
  rw [dotL_apply, ← mem_algebraicClosure_iff]
  exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθ j)) (mem_algebraicClosure_iff.mpr (hx j))

lemma isAlgebraic_single {η : Type*} [DecidableEq η] (j k : η) : IsAlgebraic ℚ ((Pi.single j (1 : ℂ) : η → ℂ) k) := by
  rw [Pi.single_apply]; exact isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero

lemma span_range_single (η : Type) [Fintype η] [DecidableEq η] :
    Submodule.span ℂ (Set.range fun j : η => (Pi.single j (1 : ℂ) : η → ℂ)) = ⊤ := by
  have h := (Pi.basisFun ℂ η).span_eq
  rwa [show ⇑(Pi.basisFun ℂ η) = fun j : η => (Pi.single j (1 : ℂ) : η → ℂ) from
    funext (Pi.basisFun_apply ℂ η)] at h

/-- A spanning set of `TF ι Q` built from a spanning set `BQ` of `Q`. -/
def spanTF (BQ : Set Q) : Set (TF ι Q) :=
  Set.range (fun j : ι => (tor1 j 1 : TF ι Q)) ∪ Set.range (fun j : ι => (tor2 j 1 : TF ι Q)) ∪ qv '' BQ

omit [Module ℚ Q] in
lemma span_spanTF (BQ : Set Q) (hBQ : Submodule.span ℂ BQ = ⊤) :
    Submodule.span ℂ (spanTF (ι := ι) BQ) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hdec : v = ∑ j, v.1.1 j • (tor1 j 1 : TF ι Q) + ∑ j, v.1.2 j • (tor2 j 1 : TF ι Q) + qv v.2 := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · simp only [tor1, tor2, qv, Prod.fst_add, Prod.fst_sum, Prod.smul_mk, smul_zero,
        Finset.sum_const_zero, add_zero]
      exact (sum_smul_single _).symm
    · simp only [tor1, tor2, qv, Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
        Prod.smul_mk, smul_zero, Finset.sum_const_zero, zero_add, add_zero]
      exact (sum_smul_single _).symm
    · simp [tor1, tor2, qv, Prod.snd_sum]
  have hq : (qv v.2 : TF ι Q) ∈ Submodule.span ℂ (spanTF (ι := ι) BQ) := by
    have : Submodule.map (LinearMap.inr ℂ ((ι → ℂ) × (ι → ℂ)) Q) (Submodule.span ℂ BQ) ≤
        Submodule.span ℂ (spanTF (ι := ι) BQ) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact Submodule.subset_span (Or.inr ⟨q, hq, rfl⟩)
    exact this ⟨v.2, by rw [hBQ]; trivial, rfl⟩
  rw [hdec]
  exact add_mem (add_mem
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨j, rfl⟩))))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩))))) hq

/-- `ker φ` is toric-injective for `gmF` as soon as `λ` is injective on `span_ℚ perQ`. -/
lemma torInj_ker_phiW [FiniteDimensional ℂ Q] (θ : ι → ℂ) (algQ : Q → Prop) (perQ : Set Q) (lam : Q →ₗ[ℂ] ℂ)
    (a μ : ℂ) (hper0 : ∀ q ∈ Submodule.span ℚ perQ, lam q = 0 → q = 0) :
    TorInj (gmF (ι := ι) algQ perQ lam) (LinearMap.ker (phiW θ lam a μ)) := by
  intro v hv hper h1
  have hl : lam v.2 = 0 := by
    rw [LinearMap.mem_ker, phiW_apply, h1] at hv
    simpa using hv
  exact Prod.ext h1 (hper0 _ (snd_mem_span_perQ perQ hper) hl)

/-- **`P/π ∉ ℚ̄` from the frame hypothesis.** Under W88 §5d for `G_m^{2n} × G₂` (restricted to a class `good` of
hyperplanes containing `ker φ`), no period `q₀` of `G₂` has `λ(q₀) = θ_{j₀} απ` with `α ∈ ℚ̄ˣ`, given `μ ∈ ℚ̄` with
`1, μ` independent over `K = span_ℚ θ`. -/
theorem frameW_false [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (perQ : Set Q) (lam : Q →ₗ[ℂ] ℂ)
    {good : Submodule ℂ (TF ι Q) → Prop} (hW : HyperplaneKappaOn (gmF (ι := ι) algQ perQ lam) good)
    (hlamalg : ∀ q, algQ q → IsAlgebraic ℚ (lam q)) (halg0 : algQ 0)
    (BQ : Set Q) (hBQ : Submodule.span ℂ BQ = ⊤) (hBQalg : ∀ q ∈ BQ, algQ q)
    (μ : ℂ) (hμalg : IsAlgebraic ℚ μ)
    (hμ : ∀ A ∈ Submodule.span ℚ (Set.range θ), ∀ B ∈ Submodule.span ℚ (Set.range θ), A + μ * B = 0 → B = 0)
    (α : ℂ) (hα : IsAlgebraic ℚ α) (hα0 : α ≠ 0)
    (hgood : good (LinearMap.ker (phiW θ lam (α / (2 * I)) μ)))
    (j0 : ι) (q0 : Q) (hq0 : q0 ∈ perQ) (hlq0 : lam q0 = θ j0 * (α * Real.pi)) : False := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  set a := α / (2 * I) with ha
  have ha0 : a ≠ 0 := div_ne_zero hα0 (mul_ne_zero two_ne_zero I_ne_zero)
  have h2I : IsAlgebraic ℚ (2 * I) := by
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (2 : ℚ)).mul isAlgebraic_I
  have haalg : IsAlgebraic ℚ a := by
    rw [ha, div_eq_mul_inv]; exact hα.mul h2I.inv
  set φ := phiW θ lam a μ with hφ
  have h0 : θ j0 ≠ 0 := hθ.ne_zero j0
  set e : TF ι Q := tor1 j0 1 with he_def
  have he : φ e = -(a * θ j0) := by simp [hφ, phiW_apply, e, tor1, dotL_single]
  have he0 : φ e ≠ 0 := by rw [he]; exact neg_ne_zero.mpr (mul_ne_zero ha0 h0)
  -- `V = ker φ` is a hyperplane
  have hsurj : Function.Surjective φ := fun w =>
    ⟨(w / φ e) • e, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ he0]⟩
  have hV : finrank ℂ (LinearMap.ker φ) + 1 = finrank ℂ (TF ι Q) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
    omega
  -- `V` is `ℚ̄`-rational
  have hφalg : ∀ v : TF ι Q, algF algQ v → IsAlgebraic ℚ (φ v) := by
    rintro v ⟨h1, h2, h3⟩
    rw [hφ, phiW_apply]
    exact ((hlamalg _ h3).sub (haalg.mul (isAlgebraic_dotL hθalg h1))).sub
      ((haalg.mul hμalg).mul (isAlgebraic_dotL hθalg h2))
  have hBalg : ∀ u ∈ spanTF (ι := ι) BQ, algF algQ u := by
    rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩)
    · exact ⟨fun k => isAlgebraic_single j k, fun k => isAlgebraic_zero, halg0⟩
    · exact ⟨fun k => isAlgebraic_zero, fun k => isAlgebraic_single j k, halg0⟩
    · exact ⟨fun k => isAlgebraic_zero, fun k => isAlgebraic_zero, hBQalg q hq⟩
  have heB : e ∈ spanTF (ι := ι) BQ := Or.inl (Or.inl ⟨j0, rfl⟩)
  have hPalg : ∀ u, algF algQ u → ∀ c : ℂ, IsAlgebraic ℚ c → algF algQ (u - c • e) := by
    rintro u ⟨h1, h2, h3⟩ c hc
    refine ⟨fun k => ?_, fun k => ?_, ?_⟩
    · simp only [e, tor1, Prod.fst_sub, Prod.smul_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact (h1 k).sub (hc.mul (isAlgebraic_single j0 k))
    · simpa [e, tor1] using h2 k
    · simpa [e, tor1] using h3
  have hrat : (gmF (ι := ι) algQ perQ lam).Rational (LinearMap.ker φ) := by
    refine ⟨_, ?_, ker_eq_span_proj φ e he0 _ (span_spanTF BQ hBQ)⟩
    rintro _ ⟨u, hu, rfl⟩
    refine hPalg u (hBalg u hu) _ ?_
    rw [← mem_algebraicClosure_iff]
    exact div_mem (mem_algebraicClosure_iff.mpr (hφalg u (hBalg u hu)))
      (mem_algebraicClosure_iff.mpr (hφalg e (hBalg e heB)))
  -- the period lift `y₀ = (2πi e_{j₀}, 0; q₀)`
  set y₀ : TF ι Q := tor1 j0 (2 * Real.pi * I) + qv q0 with hy0_def
  have hy0V : y₀ ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, hφ, phiW_apply]
    simp only [y₀, tor1, qv, Prod.fst_add, Prod.snd_add, add_zero, zero_add, dotL_single, map_zero,
      mul_zero, sub_zero, hlq0, ha]
    field_simp
    ring
  have hy0lam : y₀ ∈ (gmF (ι := ι) algQ perQ lam).lam := by
    show y₀ ∈ Submodule.span ℚ (lamGen (ι := ι) perQ)
    have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
      rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨j0, _, h2pi, rfl⟩)))
      (Submodule.subset_span (Or.inr ⟨q0, hq0, rfl⟩))
  have hy0 : y₀ ≠ 0 := by
    intro h
    have := congrArg (fun v : TF ι Q => v.1.1 j0) h
    simp [y₀, tor1, qv, Real.pi_ne_zero, I_ne_zero] at this
  -- apply W88 §5d with `V = W = ker φ`, `m = 1`
  obtain ⟨S, ⟨L, h, hh, rfl⟩, hne, hle⟩ := hW (LinearMap.ker φ) (LinearMap.ker φ) 1 (fun _ => y₀) hgood hV le_rfl
    hrat (fun _ => ⟨hy0V, hy0lam⟩) (by
      have hz : ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ (LinearMap.ker φ)) = 0 := by omega
      rw [hz, mul_zero, Set.range_const, finrank_span_singleton hy0]
      norm_num)
  rcases hh with rfl | ⟨x, hx, hlx⟩
  · -- `S = T_L × 0`: a nonzero rational toric vector in `V`
    have hL : L ≠ ⊥ := by
      rintro rfl
      apply hne
      rw [torSub_bot, Submodule.prod_bot]
    obtain ⟨l, hl, hl0⟩ := (Submodule.ne_bot_iff L).mp hL
    have hlm : (((fun j => ((l.1 j : ℚ) : ℂ)), (fun j => ((l.2 j : ℚ) : ℂ))), (0 : Q)) ∈
        (torSub L).prod (⊥ : Submodule ℂ Q) :=
      Submodule.mem_prod.mpr ⟨Submodule.subset_span ⟨l, hl, rfl⟩, Submodule.zero_mem _⟩
    have hVl := hle hlm
    rw [LinearMap.mem_ker, hφ, phiW_apply] at hVl
    simp only [map_zero, zero_sub] at hVl
    have hmem : ∀ l' : ι → ℚ, dotL θ (fun j => ((l' j : ℚ) : ℂ)) ∈ Submodule.span ℚ (Set.range θ) := by
      intro l'
      rw [dotL_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [show θ j * ((l' j : ℚ) : ℂ) = l' j • θ j by rw [Rat.smul_def]; ring]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have hAB : dotL θ (fun j => ((l.1 j : ℚ) : ℂ)) + μ * dotL θ (fun j => ((l.2 j : ℚ) : ℂ)) = 0 := by
      have : a * (dotL θ (fun j => ((l.1 j : ℚ) : ℂ)) + μ * dotL θ (fun j => ((l.2 j : ℚ) : ℂ))) = 0 := by
        linear_combination -hVl
      exact (mul_eq_zero.mp this).resolve_left ha0
    have hB := hμ _ (hmem _) _ (hmem _) hAB
    have hA : dotL θ (fun j => ((l.1 j : ℚ) : ℂ)) = 0 := by rw [hB, mul_zero, add_zero] at hAB; exact hAB
    exact hl0 (Prod.ext (dot_rat_eq_zero hθ _ hA) (dot_rat_eq_zero hθ _ hB))
  · -- `λ ≠ 0` on `T_H`
    have hxm : (qv x : TF ι Q) ∈ (torSub L).prod h :=
      Submodule.mem_prod.mpr ⟨Submodule.zero_mem _, hx⟩
    have hVx := hle hxm
    rw [LinearMap.mem_ker, hφ, phiW_apply] at hVx
    simp [qv] at hVx
    exact hlx hVx

end CM4E.Gen
