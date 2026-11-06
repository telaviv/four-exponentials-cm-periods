/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Frame

/-!
# A second frame: `Ψ''((x, y), q) = (θᵀx + μ(q), θᵀy + λ(q))`

This generalises `CM4E/Gen/Frame.lean` to groups `G'' = G_m^{2n} × G₂` where `G₂` may contain `G_a` factors (the
groups of the paper's Theorems SMG and SMG♮, used for Theorem S). The tangent space is again
`((ι → ℂ) × (ι → ℂ)) × Q`; two linear forms `μ, λ` on `Q` feed the two coordinates of `Ψ''`.

The subgroup condition is the uniform form also used for Theorem MX: a connected algebraic subgroup is `0` or has an
algebraic tangent vector with `Ψ'' ≠ 0` (i.e. `U` is the largest connected subgroup of `G^n` with tangent space in
`ker Φ`). The logarithms, periods and `d₂` are supplied by the instance (W88 writes `G = G_a^{d₀} × G_m^{d₁} × G₂`;
here `Q = T(G_a^{d₀} × G₂)`, so `d₂ = dim Q − d₀`).

`frame2_false`: given `n` period lifts with `Ψ'' = θ_h(2πi, s·2πi)`, `2n` data lifts with `Ψ'' = θ_h(y_k, s y_k)`,
`2πi, y₁, y₂` linearly independent over `ℚ̄`, `s` transcendental and `d₂ < n`, the hypothesis `HyperplaneKappa` is
contradictory. The count is that of Frame: `m = 3n`, `κ ≥ n`, `d − 1 − t ≤ 1`. `frame2_false_K_on` is the same
under `HyperplaneKappaOn … TorInj`; both come from `frame2_false_K_of_good`.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]

/-- `Ψ'' = (θᵀx + μ(q), θᵀy + λ(q))`. -/
noncomputable def PsiG (θ : ι → ℂ) (μ lam : Q →ₗ[ℂ] ℂ) : TF ι Q →ₗ[ℂ] ℂ × ℂ :=
  (dotL θ ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _) + μ ∘ₗ LinearMap.snd ℂ _ _).prod
    (dotL θ ∘ₗ (LinearMap.snd ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _) + lam ∘ₗ LinearMap.snd ℂ _ _)

lemma PsiG_apply (θ : ι → ℂ) (μ lam : Q →ₗ[ℂ] ℂ) (v : TF ι Q) :
    PsiG θ μ lam v = (dotL θ v.1.1 + μ v.2, dotL θ v.1.2 + lam v.2) := by
  simp [PsiG]

/-- **The group model of `G_m^{2n} × G₂`** with linear forms `μ, λ`. Sound when `lamS` consists of logarithms of
algebraic points, `perS` of periods, `d₂ = dim Q − d₀` (`d₀`, `d₁ = 2n` maximal), and no nonzero connected algebraic
subgroup has its tangent space in `ker Ψ''`. -/
noncomputable def gmF2 (θ : ι → ℂ) (algQ : Q → Prop) (lamS perS : Set (TF ι Q)) (μ lam : Q →ₗ[ℂ] ℂ)
    (d₂ : ℕ) : GroupModel (TF ι Q) where
  d₁ := 2 * Fintype.card ι
  d₂ := d₂
  alg := algF algQ
  lam := (Submodule.span ℚ lamS : Set (TF ι Q))
  per := Submodule.span ℚ perS
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algF algQ x ∧ PsiG θ μ lam x ≠ 0

section Proof

variable (θ : ι → ℂ) (μ lam : Q →ₗ[ℂ] ℂ)

/-- `θᵀy + λ(q) − s(θᵀx + μ(q))`; its kernel is `V'' = Ψ''⁻¹(ℂ(1, s))`. -/
noncomputable def phiG (s : ℂ) : TF ι Q →ₗ[ℂ] ℂ :=
  LinearMap.snd ℂ ℂ ℂ ∘ₗ PsiG θ μ lam - s • (LinearMap.fst ℂ ℂ ℂ ∘ₗ PsiG θ μ lam)

lemma phiG_apply (s : ℂ) (v : TF ι Q) :
    phiG θ μ lam s v = (PsiG θ μ lam v).2 - s * (PsiG θ μ lam v).1 := by
  simp [phiG]

variable {θ} in
lemma PsiG_surjective {i0 : ι} (h0 : θ i0 ≠ 0) : Function.Surjective (PsiG θ μ lam) := by
  rintro ⟨a, b⟩
  refine ⟨tor1 i0 (a / θ i0) + tor2 i0 (b / θ i0), ?_⟩
  simp only [PsiG_apply, tor1, tor2, Prod.fst_add, Prod.snd_add, add_zero, zero_add, map_add,
    dotL_single, map_zero, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> field_simp

variable {θ} in
lemma phiG_surjective {i0 : ι} (h0 : θ i0 ≠ 0) (s : ℂ) : Function.Surjective (phiG θ μ lam s) :=
  fun w => by
    obtain ⟨v, hv⟩ := PsiG_surjective μ lam h0 (0, w)
    exact ⟨v, by rw [phiG_apply, hv]; simp⟩

/-- Algebraic vectors spanning `ker Ψ''` (`T` spans `Q`). -/
noncomputable def wGen2 (i0 : ι) (T : Set Q) : Set (TF ι Q) :=
  Set.range (fun j : ι => ((((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ι → ℂ)), (0 : Q))) ∪
    Set.range (fun j : ι => (((0 : ι → ℂ), ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ)), (0 : Q))) ∪
    (fun q : Q => (((-(μ q / θ i0)) • (Pi.single i0 1 : ι → ℂ), (-(lam q / θ i0)) • (Pi.single i0 1 : ι → ℂ)), q)) '' T

lemma wGen2_le_ker (i0 : ι) (h0 : θ i0 ≠ 0) (T : Set Q) :
    Submodule.span ℂ (wGen2 θ μ lam i0 T) ≤ LinearMap.ker (PsiG θ μ lam) := by
  rw [Submodule.span_le]
  rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, -, rfl⟩)
  · simp [PsiG_apply, map_sub, map_smul, dotL_single, mul_comm]
  · simp [PsiG_apply, map_sub, map_smul, dotL_single, mul_comm]
  · simp only [SetLike.mem_coe, LinearMap.mem_ker, PsiG_apply, map_smul, dotL_single, smul_eq_mul,
      Prod.mk_eq_zero]
    constructor <;> field_simp <;> ring

variable {θ} in
lemma ker_PsiG_le_W {i0 : ι} (h0 : θ i0 ≠ 0) (T : Set Q) (hT : Submodule.span ℂ T = ⊤) :
    LinearMap.ker (PsiG θ μ lam) ≤ Submodule.span ℂ (wGen2 θ μ lam i0 T) := by
  set W := Submodule.span ℂ (wGen2 θ μ lam i0 T)
  have g3 : ∀ q ∈ Submodule.span ℂ T, (((-(μ q / θ i0)) • (Pi.single i0 1 : ι → ℂ),
      (-(lam q / θ i0)) • (Pi.single i0 1 : ι → ℂ)), q) ∈ W := by
    intro q hq
    refine Submodule.span_induction (fun x hx => Submodule.subset_span (Or.inr ⟨x, hx, rfl⟩)) ?_
      (fun x y _ _ hx hy => ?_) (fun c x _ hx => ?_) hq
    · have := W.zero_mem
      convert this using 1; simp
    · convert add_mem hx hy using 1
      simp only [map_add, Prod.mk_add_mk, add_div, neg_add, add_smul]
    · convert W.smul_mem c hx using 1
      simp only [map_smul, smul_eq_mul, Prod.smul_mk, smul_smul]
      congr 2 <;> congr 1 <;> ring
  have gx : ∀ x : ι → ℂ, dotL θ x = 0 → ((x, (0 : ι → ℂ)), (0 : Q)) ∈ W := by
    intro x hx
    rw [← decomp_x h0 x hx]
    have : ((∑ j, (x j / θ i0) • ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ι → ℂ)),
        (0 : Q)) = ∑ j, (x j / θ i0) •
          ((((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ), (0 : ι → ℂ)), (0 : Q)) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl ⟨j, rfl⟩)))
  have gy : ∀ y : ι → ℂ, dotL θ y = 0 → (((0 : ι → ℂ), y), (0 : Q)) ∈ W := by
    intro y hy
    rw [← decomp_x h0 y hy]
    have : (((0 : ι → ℂ), ∑ j, (y j / θ i0) • ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ)),
        (0 : Q)) = ∑ j, (y j / θ i0) •
          (((0 : ι → ℂ), ((θ i0) • Pi.single j 1 - (θ j) • Pi.single i0 1 : ι → ℂ)), (0 : Q)) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩)))
  intro v hv
  rw [LinearMap.mem_ker, PsiG_apply, Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2⟩ := hv
  set u : TF ι Q := (((-(μ v.2 / θ i0)) • (Pi.single i0 1 : ι → ℂ),
      (-(lam v.2 / θ i0)) • (Pi.single i0 1 : ι → ℂ)), v.2)
  have hu : u ∈ W := g3 v.2 (by rw [hT]; trivial)
  have hx : dotL θ (v.1.1 - u.1.1) = 0 := by
    simp only [u, map_sub, map_smul, dotL_single, smul_eq_mul]; field_simp; linear_combination h1
  have hy : dotL θ (v.1.2 - u.1.2) = 0 := by
    simp only [u, map_sub, map_smul, dotL_single, smul_eq_mul]; field_simp; linear_combination h2
  have : v = ((v.1.1 - u.1.1, (0 : ι → ℂ)), (0 : Q)) + (((0 : ι → ℂ), v.1.2 - u.1.2), (0 : Q)) + u := by
    refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [u]
  rw [this]
  exact add_mem (add_mem (gx _ hx) (gy _ hy)) hu

end Proof

/-! ## The contradiction -/

section Main

/-- The `3n` generators: period lifts `p h` and data lifts `dl k h`. -/
def genG (p : ι → TF ι Q) (dl : Fin 2 → ι → TF ι Q) : Fin 3 × ι → TF ι Q :=
  fun q => ![p q.2, dl 0 q.2, dl 1 q.2] q.1

/-- `θᵀl ∈ K = span_ℚ θ` for rational `l`. -/
lemma dot_rat_mem_span (θ : ι → ℂ) (l : ι → ℚ) :
    dotL θ (fun h => ((l h : ℚ) : ℂ)) ∈ Submodule.span ℚ (Set.range θ) := by
  rw [dotL_apply]
  refine Submodule.sum_mem _ fun h _ => ?_
  rw [show θ h * ((l h : ℚ) : ℂ) = l h • θ h by rw [Rat.smul_def]; ring]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)

/-- **The frame-2 contradiction, for `HyperplaneKappaOn`** (W88 §5d for `G_m^{2n} × G₂` restricted to a class `good`
of hyperplanes containing `V'' = ker (phiG θ μ lam s)`), with independence of `2πi, y₁, y₂` assumed only over
`K = span_ℚ θ`. Common core of `frame2_false_K` (`good = ⊤`) and `frame2_false_K_on` (`good = TorInj`). -/
theorem frame2_false_K_of_good [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (lamS perS : Set (TF ι Q))
    (μ lam : Q →ₗ[ℂ] ℂ) (d₂ : ℕ) {good : Submodule ℂ (TF ι Q) → Prop}
    (hW : HyperplaneKappaOn (gmF2 θ algQ lamS perS μ lam d₂) good)
    (hd₂ : d₂ < Fintype.card ι)
    (halg0 : algQ 0) (hμ : ∀ q, algQ q → IsAlgebraic ℚ (μ q)) (hlamA : ∀ q, algQ q → IsAlgebraic ℚ (lam q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = ⊤)
    (s : ℂ) (hs : Transcendental ℚ s) (hgood : good (LinearMap.ker (phiG θ μ lam s)))
    (p : ι → TF ι Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiG θ μ lam (p h) = (θ h * (2 * Real.pi * I), s * (θ h * (2 * Real.pi * I))))
    (y : Fin 2 → ℂ) (dl : Fin 2 → ι → TF ι Q) (hdl : ∀ k h, dl k h ∈ Submodule.span ℚ lamS)
    (hdΨ : ∀ k h, PsiG θ μ lam (dl k h) = (θ h * y k, s * (θ h * y k)))
    (hind3 : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Submodule.span ℚ (Set.range θ) → a₁ ∈ Submodule.span ℚ (Set.range θ) →
      a₂ ∈ Submodule.span ℚ (Set.range θ) →
      a₀ * (2 * Real.pi * I) + a₁ * y 0 + a₂ * y 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  have hcard : 0 < Fintype.card ι := lt_of_le_of_lt (Nat.zero_le _) hd₂
  obtain ⟨i0⟩ : Nonempty ι := Fintype.card_pos_iff.mp hcard
  have h0 : θ i0 ≠ 0 := hθ.ne_zero i0
  set g0 := genG p dl
  have hΨ1 : ∀ q, (PsiG θ μ lam (g0 q)).1 =
      θ q.2 * ![2 * Real.pi * I, y 0, y 1] q.1 := by
    rintro ⟨k, h⟩
    fin_cases k
    · simp [g0, genG, hpΨ]
    · simp [g0, genG, hdΨ]
    · simp [g0, genG, hdΨ]
  -- independence
  have hli : LinearIndependent ℚ g0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e := congrArg (fun v => (PsiG θ μ lam v).1) hg
    simp only [map_sum, Prod.fst_sum, map_zero, Prod.fst_zero] at e
    simp only [fun q => show (PsiG θ μ lam (g q • g0 q)).1 = (g q : ℂ) * (PsiG θ μ lam (g0 q)).1 by
      rw [map_rat_smul, Prod.smul_fst, Rat.smul_def], hΨ1, Fintype.sum_prod_type, Fin.sum_univ_three] at e
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e
    have hrel : dotL θ (fun h => ((g (0, h) : ℚ) : ℂ)) * (2 * Real.pi * I) +
        dotL θ (fun h => ((g (1, h) : ℚ) : ℂ)) * y 0 + dotL θ (fun h => ((g (2, h) : ℚ) : ℂ)) * y 1 = 0 := by
      simp only [dotL_apply, Finset.sum_mul]
      rw [← e]
      congr 1
      · congr 1 <;> exact Finset.sum_congr rfl fun h _ => by ring
      · exact Finset.sum_congr rfl fun h _ => by ring
    obtain ⟨a0, a1, a2⟩ := hind3 _ _ _ (dot_rat_mem_span θ _) (dot_rat_mem_span θ _) (dot_rat_mem_span θ _)
      hrel
    have z0 := dot_rat_eq_zero hθ _ a0
    have z1 := dot_rat_eq_zero hθ _ a1
    have z2 := dot_rat_eq_zero hθ _ a2
    rintro ⟨k, h⟩
    fin_cases k
    exacts [congrFun z0 h, congrFun z1 h, congrFun z2 h]
  set e := Fintype.equivFin (Fin 3 × ι)
  set y' : Fin (Fintype.card (Fin 3 × ι)) → TF ι Q := g0 ∘ e.symm with hy'
  have hli' : LinearIndependent ℚ y' := hli.comp _ e.symm.injective
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y')) = 3 * Fintype.card ι := by
    rw [finrank_span_eq_card hli']; simp [Fintype.card_prod]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y')) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hmem : ∀ q, g0 q ∈ Submodule.span ℚ (Set.range y') := fun q =>
    Submodule.subset_span ⟨e q, by simp [hy']⟩
  -- `κ ≥ n`
  have hk : Fintype.card ι ≤
      finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmF2 θ algQ lamS perS μ lam d₂).per) := by
    let f : ι → ↥(Submodule.span ℚ (Set.range y') ⊓ (gmF2 θ algQ lamS perS μ lam d₂).per) := fun h =>
      ⟨g0 (0, h), hmem _, hpp h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp
        (Submodule.span ℚ (Set.range y') ⊓ (gmF2 θ algQ lamS perS μ lam d₂).per).subtype
      exact hli.comp (fun h : ι => ((0 : Fin 3), h)) (fun a b hab => by simpa using hab)
    simpa using hf.fintype_card_le_finrank
  -- `V''`, `W''`
  have hV : finrank ℂ (LinearMap.ker (phiG θ μ lam s)) + 1 = finrank ℂ (TF ι Q) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (phiG θ μ lam s)
    rw [LinearMap.range_eq_top.mpr (phiG_surjective μ lam h0 s), finrank_top, Module.finrank_self] at h1
    omega
  set W := Submodule.span ℂ (wGen2 θ μ lam i0 T) with hWdef
  have hWV : W ≤ LinearMap.ker (phiG θ μ lam s) := by
    intro v hv
    have := wGen2_le_ker θ μ lam i0 h0 T hv
    rw [LinearMap.mem_ker] at this ⊢
    rw [phiG_apply, this]; simp
  have hWlo : finrank ℂ (TF ι Q) ≤ finrank ℂ W + 2 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (PsiG θ μ lam)
    rw [LinearMap.range_eq_top.mpr (PsiG_surjective μ lam h0), finrank_top] at h1
    have h2 : finrank ℂ (ℂ × ℂ) = 2 := by simp [Module.finrank_prod]
    have h3 := Submodule.finrank_mono (ker_PsiG_le_W μ lam h0 T hT)
    rw [← hWdef] at h3
    omega
  have hWhi : finrank ℂ W + 1 ≤ finrank ℂ (TF ι Q) := by
    have := Submodule.finrank_mono hWV
    omega
  have hWrat : (gmF2 θ algQ lamS perS μ lam d₂).Rational W := by
    refine ⟨wGen2 θ μ lam i0 T, ?_, rfl⟩
    rintro _ ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩)
    · refine ⟨fun k => ?_, fun k => isAlgebraic_zero, halg0⟩
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      exact ((hθalg i0).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)).sub
        ((hθalg j).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero))
    · refine ⟨fun k => isAlgebraic_zero, fun k => ?_, halg0⟩
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      exact ((hθalg i0).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)).sub
        ((hθalg j).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero))
    · have hc : ∀ c : ℂ, IsAlgebraic ℚ c → ∀ k, IsAlgebraic ℚ
          (((-(c / θ i0)) • (Pi.single i0 1 : ι → ℂ)) k) := by
        intro c hc k
        simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, div_eq_mul_inv]
        exact (hc.mul (hθalg i0).inv).neg.mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)
      exact ⟨hc _ (hμ q (hTalg q hq)), hc _ (hlamA q (hTalg q hq)), hTalg q hq⟩
  have hVmem : ∀ q, g0 q ∈ LinearMap.ker (phiG θ μ lam s) := by
    rintro ⟨k, h⟩
    rw [LinearMap.mem_ker, phiG_apply]
    fin_cases k
    · simp [g0, genG, hpΨ]
    · simp [g0, genG, hdΨ]
    · simp [g0, genG, hdΨ]
  have hlamMem : ∀ q, g0 q ∈ (gmF2 θ algQ lamS perS μ lam d₂).lam := by
    rintro ⟨k, h⟩
    show g0 (k, h) ∈ Submodule.span ℚ lamS
    fin_cases k
    exacts [hpl h, hdl 0 h, hdl 1 h]
  -- apply W88 §5d
  obtain ⟨S, hsub, hne, hle⟩ := hW (LinearMap.ker (phiG θ μ lam s)) W _ y' hgood
    (by omega) hWV hWrat
    (fun i => ⟨hVmem (e.symm i), hlamMem (e.symm i)⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y')) : ℤ) >
        ((2 * Fintype.card ι : ℕ) + 2 * (d₂ : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y') ⊓ (gmF2 θ algQ lamS perS μ lam d₂).per)) *
          ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ W))
      rw [hfinY]
      have hcase : ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ W) = 0 ∨
          ((finrank ℂ (TF ι Q) : ℤ) - 1 - finrank ℂ W) = 1 := by omega
      rcases hcase with hc | hc <;> rw [hc] <;> push_cast <;> omega)
  rcases hsub with rfl | ⟨x, hxS, ⟨hx1, hx2, hx3⟩, hx⟩
  · exact hne rfl
  · have hxV := hle hxS
    rw [LinearMap.mem_ker, phiG_apply] at hxV
    set P := PsiG θ μ lam x with hP
    have hPalg : ∀ k : Fin 2, IsAlgebraic ℚ (![P.1, P.2] k) := by
      have hdot : ∀ z : ι → ℂ, (∀ j, IsAlgebraic ℚ (z j)) → dotL θ z ∈ algebraicClosure ℚ ℂ :=
        fun z hz => by
          rw [dotL_apply]
          exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
            (mem_algebraicClosure_iff.mpr (hz j))
      intro k; fin_cases k
      · show IsAlgebraic ℚ P.1
        rw [hP, PsiG_apply, ← mem_algebraicClosure_iff]
        exact add_mem (hdot _ hx1) (mem_algebraicClosure_iff.mpr (hμ _ hx3))
      · show IsAlgebraic ℚ P.2
        rw [hP, PsiG_apply, ← mem_algebraicClosure_iff]
        exact add_mem (hdot _ hx2) (mem_algebraicClosure_iff.mpr (hlamA _ hx3))
    have h1 : IsAlgebraic ℚ P.1 := by simpa using hPalg 0
    have h2 : IsAlgebraic ℚ P.2 := by simpa using hPalg 1
    by_cases hP1 : P.1 = 0
    · apply hx
      have hP2 : P.2 = 0 := by rw [hP1, mul_zero, sub_zero] at hxV; exact hxV
      exact Prod.ext hP1 hP2
    · apply hs
      have : s = P.2 / P.1 := by field_simp; linear_combination -hxV
      rw [this, ← mem_algebraicClosure_iff]
      exact div_mem (mem_algebraicClosure_iff.mpr h2) (mem_algebraicClosure_iff.mpr h1)

/-- **The frame-2 contradiction** (W88 §5d for `G_m^{2n} × G₂`), with independence of `2πi, y₁, y₂` assumed only over
`K = span_ℚ θ`. -/
theorem frame2_false_K [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (lamS perS : Set (TF ι Q))
    (μ lam : Q →ₗ[ℂ] ℂ) (d₂ : ℕ) (hW : HyperplaneKappa (gmF2 θ algQ lamS perS μ lam d₂))
    (hd₂ : d₂ < Fintype.card ι)
    (halg0 : algQ 0) (hμ : ∀ q, algQ q → IsAlgebraic ℚ (μ q)) (hlamA : ∀ q, algQ q → IsAlgebraic ℚ (lam q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = ⊤)
    (s : ℂ) (hs : Transcendental ℚ s)
    (p : ι → TF ι Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiG θ μ lam (p h) = (θ h * (2 * Real.pi * I), s * (θ h * (2 * Real.pi * I))))
    (y : Fin 2 → ℂ) (dl : Fin 2 → ι → TF ι Q) (hdl : ∀ k h, dl k h ∈ Submodule.span ℚ lamS)
    (hdΨ : ∀ k h, PsiG θ μ lam (dl k h) = (θ h * y k, s * (θ h * y k)))
    (hind3 : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Submodule.span ℚ (Set.range θ) → a₁ ∈ Submodule.span ℚ (Set.range θ) →
      a₂ ∈ Submodule.span ℚ (Set.range θ) →
      a₀ * (2 * Real.pi * I) + a₁ * y 0 + a₂ * y 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False :=
  frame2_false_K_of_good θ hθ hθalg algQ lamS perS μ lam d₂ (good := fun _ => True) hW.on hd₂ halg0 hμ hlamA T hTalg
    hT s hs trivial p hpl hpp hpΨ y dl hdl hdΨ hind3

/-- `V'' = ker (phiG θ μ lam s)` is toric-injective (`TorInj`, `CM4E/Gen/Frame.lean`) for `gmF2` when no nonzero vector
of `span_ℚ perS` with zero toric part satisfies `λ(q) = s μ(q)`. -/
lemma torInj_ker_phiG (θ : ι → ℂ) (algQ : Q → Prop) (lamS perS : Set (TF ι Q)) (μ lam : Q →ₗ[ℂ] ℂ) (d₂ : ℕ)
    (s : ℂ) (hper0 : ∀ v ∈ Submodule.span ℚ perS, v.1 = 0 → lam v.2 = s * μ v.2 → v = 0) :
    TorInj (gmF2 θ algQ lamS perS μ lam d₂) (LinearMap.ker (phiG θ μ lam s)) := by
  intro v hv hper h1
  refine hper0 v hper h1 ?_
  rw [LinearMap.mem_ker, phiG_apply, PsiG_apply, h1] at hv
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero, zero_add] at hv
  linear_combination hv

/-- **The frame-2 contradiction under the toric-injective hypothesis.** As `frame2_false_K`, with `HyperplaneKappa`
weakened to `HyperplaneKappaOn … TorInj`, plus the condition `hper0` of `torInj_ker_phiG` (which makes `V''`
toric-injective). -/
theorem frame2_false_K_on [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (lamS perS : Set (TF ι Q))
    (μ lam : Q →ₗ[ℂ] ℂ) (d₂ : ℕ)
    (hW : HyperplaneKappaOn (gmF2 θ algQ lamS perS μ lam d₂) (TorInj (gmF2 θ algQ lamS perS μ lam d₂)))
    (hd₂ : d₂ < Fintype.card ι)
    (halg0 : algQ 0) (hμ : ∀ q, algQ q → IsAlgebraic ℚ (μ q)) (hlamA : ∀ q, algQ q → IsAlgebraic ℚ (lam q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = ⊤)
    (s : ℂ) (hs : Transcendental ℚ s)
    (hper0 : ∀ v ∈ Submodule.span ℚ perS, v.1 = 0 → lam v.2 = s * μ v.2 → v = 0)
    (p : ι → TF ι Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiG θ μ lam (p h) = (θ h * (2 * Real.pi * I), s * (θ h * (2 * Real.pi * I))))
    (y : Fin 2 → ℂ) (dl : Fin 2 → ι → TF ι Q) (hdl : ∀ k h, dl k h ∈ Submodule.span ℚ lamS)
    (hdΨ : ∀ k h, PsiG θ μ lam (dl k h) = (θ h * y k, s * (θ h * y k)))
    (hind3 : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Submodule.span ℚ (Set.range θ) → a₁ ∈ Submodule.span ℚ (Set.range θ) →
      a₂ ∈ Submodule.span ℚ (Set.range θ) →
      a₀ * (2 * Real.pi * I) + a₁ * y 0 + a₂ * y 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False :=
  frame2_false_K_of_good θ hθ hθalg algQ lamS perS μ lam d₂ hW hd₂ halg0 hμ hlamA T hTalg hT s hs
    (torInj_ker_phiG θ algQ lamS perS μ lam d₂ s hper0) p hpl hpp hpΨ y dl hdl hdΨ hind3

/-- **The frame-2 contradiction** with `2πi, y₁, y₂` independent over `ℚ̄`. -/
theorem frame2_false [FiniteDimensional ℂ Q] (θ : ι → ℂ) (hθ : LinearIndependent ℚ θ)
    (hθalg : ∀ j, IsAlgebraic ℚ (θ j)) (algQ : Q → Prop) (lamS perS : Set (TF ι Q))
    (μ lam : Q →ₗ[ℂ] ℂ) (d₂ : ℕ) (hW : HyperplaneKappa (gmF2 θ algQ lamS perS μ lam d₂))
    (hd₂ : d₂ < Fintype.card ι)
    (halg0 : algQ 0) (hμ : ∀ q, algQ q → IsAlgebraic ℚ (μ q)) (hlamA : ∀ q, algQ q → IsAlgebraic ℚ (lam q))
    (T : Set Q) (hTalg : ∀ q ∈ T, algQ q) (hT : Submodule.span ℂ T = ⊤)
    (s : ℂ) (hs : Transcendental ℚ s)
    (p : ι → TF ι Q) (hpl : ∀ h, p h ∈ Submodule.span ℚ lamS) (hpp : ∀ h, p h ∈ Submodule.span ℚ perS)
    (hpΨ : ∀ h, PsiG θ μ lam (p h) = (θ h * (2 * Real.pi * I), s * (θ h * (2 * Real.pi * I))))
    (y : Fin 2 → ℂ) (dl : Fin 2 → ι → TF ι Q) (hdl : ∀ k h, dl k h ∈ Submodule.span ℚ lamS)
    (hdΨ : ∀ k h, PsiG θ μ lam (dl k h) = (θ h * y k, s * (θ h * y k)))
    (hind3 : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * (2 * Real.pi * I) + a₁ * y 0 + a₂ * y 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  have hK : ∀ a ∈ Submodule.span ℚ (Set.range θ), IsAlgebraic ℚ a := by
    intro a ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp ha
    rw [← mem_algebraicClosure_iff]
    exact sum_mem fun j _ => by
      rw [Rat.smul_def]
      exact mul_mem (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (c j)))
        (mem_algebraicClosure_iff.mpr (hθalg j))
  exact frame2_false_K θ hθ hθalg algQ lamS perS μ lam d₂ hW hd₂ halg0 hμ hlamA T hTalg hT s hs p hpl hpp hpΨ y dl
    hdl hdΨ fun a₀ a₁ a₂ h₀ h₁ h₂ => hind3 a₀ a₁ a₂ (hK _ h₀) (hK _ h₁) (hK _ h₂)

end Main

end CM4E.Gen
