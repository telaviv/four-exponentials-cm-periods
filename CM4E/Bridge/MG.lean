/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.Transport
import CM4E.Bridge.Std
import CM4E.Gen.MG
import LSG.W88.K11Lin

/-!
# Theorem MG's hypothesis from the standard model: `A'' = E^n/B_{ker ψ} ≅ E^r`

For a CM lattice `L = ω ℤ[α]` with `α` integral (`α² = a + cα`, `a, c ∈ ℤ`) and an adapted basis `θ(j, e) = α^e b j`
(`n = 2r`), the abelian variety `A'' = E^n/B_{ker ψ}` of Theorem MG is isomorphic to `E^r` by
`(x_{j0}, x_{j1}) ↦ x_{j0} + [α]x_{j1}`: on tangent spaces `E0 z = (z_{j0} + α z_{j1})_j`, whose kernel is `ℂ·ker ψ`
(`ker_E0`), so `Qm = ℂ^n/ℂ·ker ψ ≅ ℂ^r` (`phiE`), and `λ = Σ_j b_j y_j` in the new coordinates. Together with a reindexing
of the toric coordinates this identifies the model `gmMG L b` of `G_m^{2n} × A''` with the standard model
`gmStd 0 (2n) (E, …, E)`, and `hyperplaneKappa_transport` gives `Thm11KappaMG L` from `HypStd`
(`thm11KappaMG_of_std`). Everything here is proved; in particular the subgroup condition of `gmMG` (every nonzero abelian
subvariety of `A''` has `λ ≠ 0` on its tangent space), a soundness fact of `CM4E/Gen/MG.lean`, becomes a theorem:
a nonzero abelian tangent space contains a nonzero lattice vector `((m_j + n_j α) ω)_j`, on which `λ = ω θᵀ(m, n) ≠ 0`.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen LSG.W88

namespace CM4E.Bridge

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- `E0 z = (z_{j0} + α z_{j1})_j`. -/
noncomputable def E0 : (Fin r × Fin 2 → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun z := fun j => z (j, 0) + L.α * z (j, 1)
  map_add' x y := by funext j; simp; ring
  map_smul' c x := by funext j; simp; ring

lemma E0_apply (z : Fin r × Fin 2 → ℂ) (j : Fin r) : E0 L z j = z (j, 0) + L.α * z (j, 1) := rfl

lemma E0_surjective : Function.Surjective (E0 L (r := r)) := fun y =>
  ⟨fun p => if p.2 = 0 then y p.1 else 0, by funext j; simp [E0_apply]⟩

variable {L b}

/-- `b` is linearly independent over `k = ℚ(α)`. -/
lemma b_kindep (hb : IsAdaptedFieldBasis L.α b) (u w : Fin r → ℚ)
    (h : ∑ j, b j * ((u j : ℂ) + w j * L.α) = 0) : u = 0 ∧ w = 0 := by
  have := Fintype.linearIndependent_iff.mp hb.indep (fun p => if p.2 = 0 then u p.1 else w p.1) (by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, theta, Rat.smul_def]
    simp
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring)
  exact ⟨funext fun j => by simpa using this (j, 0), funext fun j => by simpa using this (j, 1)⟩

variable (L b) in
lemma lamM_eq_sum (z : Fin r × Fin 2 → ℂ) : dotL (theta L.α b) z = ∑ j, b j * E0 L z j := by
  rw [dotL_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => by simp [Fin.sum_univ_two, theta, E0_apply]; ring

lemma Wpsi_le_ker (hb : IsAdaptedFieldBasis L.α b) : Wpsi L b ≤ LinearMap.ker (E0 L) := by
  rw [Wpsi, Submodule.span_le]
  rintro v ⟨hk, hv⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  have hsum : ∑ j, theta L.α b j * v j = dotL (theta L.α b) v := by rw [dotL_apply]
  rw [hsum, lamM_eq_sum] at hv
  -- each `E0 v j` is in `k`
  have hc : ∀ j, ∃ U W : ℚ, E0 L v j = U + W * L.α := by
    intro j
    obtain ⟨u0, w0, h0⟩ := hk (j, 0)
    obtain ⟨u1, w1, h1⟩ := hk (j, 1)
    refine ⟨u0 + w1 * L.p, w0 + u1 + w1 * L.q, ?_⟩
    rw [E0_apply, h0, h1]; push_cast
    linear_combination (w1 : ℂ) * L.hquad
  choose U W hUW using hc
  obtain ⟨hU, hW⟩ := b_kindep hb U W (by rw [← hv]; exact Finset.sum_congr rfl fun j _ => by rw [hUW])
  funext j
  rw [hUW, Pi.zero_apply, show U j = 0 from congrFun hU j, show W j = 0 from congrFun hW j]
  simp

lemma ker_E0 (hb : IsAdaptedFieldBasis L.α b) : LinearMap.ker (E0 L) = Wpsi L b := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (Wpsi_le_ker hb)
  have h1 := LinearMap.finrank_range_add_finrank_ker (E0 L (r := r))
  rw [LinearMap.range_eq_top.mpr (E0_surjective L), finrank_top] at h1
  have h2 := finrank_Wpsi_ge L b
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h1
  omega

/-- **`Qm = ℂ^n/ℂ·ker ψ ≅ ℂ^r`**, `[z] ↦ (z_{j0} + α z_{j1})_j`. -/
noncomputable def phiE (hb : IsAdaptedFieldBasis L.α b) : Qm L b ≃ₗ[ℂ] (Fin r → ℂ) :=
  (Submodule.quotEquivOfEq _ _ (ker_E0 hb).symm).trans ((E0 L).quotKerEquivOfSurjective (E0_surjective L))

lemma phiE_mk (hb : IsAdaptedFieldBasis L.α b) (z : Fin r × Fin 2 → ℂ) :
    phiE hb (Submodule.Quotient.mk z) = E0 L z := rfl

lemma lamM_phiE (hb : IsAdaptedFieldBasis L.α b) (q : Qm L b) :
    lamM L b q = ∑ j, b j * phiE hb q j := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [lamM_mk, phiE_mk, lamM_eq_sum]

/-! ## Toric coordinates -/

section Toric

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-- `ι ⊕ ι ≃ Fin (card (ι ⊕ ι))`. -/
noncomputable def eT : ι ⊕ ι ≃ Fin (Fintype.card (ι ⊕ ι)) := Fintype.equivFin _

/-- The toric coordinates `(x, y) ∈ ℂ^ι × ℂ^ι` as one vector of `ℂ^{2n}`. -/
noncomputable def phiT : ((ι → ℂ) × (ι → ℂ)) ≃ₗ[ℂ] (Fin (Fintype.card (ι ⊕ ι)) → ℂ) where
  toFun v k := Sum.elim v.1 v.2 ((eT ι).symm k)
  invFun w := (fun i => w (eT ι (Sum.inl i)), fun i => w (eT ι (Sum.inr i)))
  map_add' x y := by funext k; simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]; generalize (eT ι).symm k = s; cases s <;> rfl
  map_smul' c x := by funext k; simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]; generalize (eT ι).symm k = s; cases s <;> rfl
  left_inv v := by ext i <;> simp
  right_inv w := by
    funext k
    obtain ⟨s, rfl⟩ := (eT ι).surjective k
    cases s <;> simp

/-- The same reindexing over `ℚ`. -/
noncomputable def rhoT : (Fin (Fintype.card (ι ⊕ ι)) → ℚ) ≃ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)) where
  toFun w := (fun i => w (eT ι (Sum.inl i)), fun i => w (eT ι (Sum.inr i)))
  invFun v k := Sum.elim v.1 v.2 ((eT ι).symm k)
  map_add' x y := by ext i <;> simp
  map_smul' c x := by ext i <;> simp
  left_inv w := by
    funext k
    obtain ⟨s, rfl⟩ := (eT ι).surjective k
    cases s <;> simp
  right_inv v := by ext i <;> simp

variable {ι}

omit [DecidableEq ι] in
lemma phiT_apply_forall {P : ℂ → Prop} (v : (ι → ℂ) × (ι → ℂ)) (h1 : ∀ i, P (v.1 i)) (h2 : ∀ i, P (v.2 i)) (k) :
    P (phiT ι v k) := by
  show P (Sum.elim v.1 v.2 ((eT ι).symm k))
  cases (eT ι).symm k
  exacts [h1 _, h2 _]

omit [DecidableEq ι] in
lemma phiT_symm_cast (q : Fin (Fintype.card (ι ⊕ ι)) → ℚ) :
    (phiT ι).symm (fun k => ((q k : ℚ) : ℂ)) =
      ((fun j => (((rhoT ι q).1 j : ℚ) : ℂ)), (fun j => (((rhoT ι q).2 j : ℚ) : ℂ))) := rfl

omit [DecidableEq ι] in
/-- The pull-back of a toric Lie algebra `U^⊥` is a `torSub`. -/
lemma comap_phiT_torusLie (U : Submodule ℚ (Fin (Fintype.card (ι ⊕ ι)) → ℚ)) :
    (torusLie U).comap (phiT ι).toLinearMap = torSub ((K11.annQ U).map (rhoT ι).toLinearMap) := by
  have h1 : torusLie U = K11.cspan (K11.annQ U) := K11.annC_eq_cspan U
  rw [h1, K11.cspan, Submodule.comap_equiv_eq_map_symm, Submodule.map_span, torSub, ← Set.image_comp]
  congr 1
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map, Function.comp_apply]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨rhoT ι q, ⟨q, hq, rfl⟩, (phiT_symm_cast q).symm⟩
  · rintro ⟨l, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, phiT_symm_cast q⟩

end Toric

/-! ## The bridge -/

/-- The coordinate isomorphism `T(G_m^{2n} × A'') ≅ ℂ^0 × ℂ^{2n} × ℂ^r`. -/
noncomputable def phiMG (hb : IsAdaptedFieldBasis L.α b) :
    TF (Fin r × Fin 2) (Qm L b) ≃ₗ[ℂ] Tan 0 (Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2))) r :=
  (LinearEquiv.prodCongr (phiT (Fin r × Fin 2)) (phiE hb)).trans LinearEquiv.uniqueProd.symm

lemma phiMG_apply (hb : IsAdaptedFieldBasis L.α b) (v : TF (Fin r × Fin 2) (Qm L b)) :
    phiMG hb v = (0, phiT _ v.1, phiE hb v.2) := by
  refine Prod.ext (Subsingleton.elim _ _) rfl

lemma E0_single_mem (hint : ∃ a c : ℤ, L.α ^ 2 = a + c * L.α) (p : Fin r × Fin 2) {w : ℂ}
    (hw : w = L.ω ∨ w = L.α * L.ω) (j : Fin r) : E0 L (Pi.single p w) j ∈ L.pp.lattice := by
  have h1 : L.ω ∈ L.pp.lattice := L.hω₁ ▸ L.pp.ω₁_mem_lattice
  have h2 : L.α * L.ω ∈ L.pp.lattice := L.hω₂ ▸ L.pp.ω₂_mem_lattice
  have h3 : L.α * (L.α * L.ω) ∈ L.pp.lattice := by
    obtain ⟨a, c, hac⟩ := hint
    rw [← mul_assoc, ← sq, hac, add_mul, mul_assoc]
    exact add_mem (by simpa [zsmul_eq_mul] using L.pp.lattice.smul_mem a h1)
      (by simpa [zsmul_eq_mul, mul_assoc] using L.pp.lattice.smul_mem c h2)
  rw [E0_apply]
  rcases p with ⟨j', e⟩
  fin_cases e
  · by_cases hj : j' = j
    · subst hj; rcases hw with rfl | rfl <;> simpa
    · simp [Pi.single_apply, Ne.symm hj, hj]
  · by_cases hj : j' = j
    · subst hj; rcases hw with rfl | rfl <;> simpa
    · simp [Pi.single_apply, Ne.symm hj, hj]

/-- **Thm11KappaMG from the standard model** (`L` with `α` integral). -/
theorem thm11KappaMG_of_std (hS : HypStd) (L : CMLattice) (hint : ∃ a c : ℤ, L.α ^ 2 = a + c * L.α) :
    Thm11KappaMG L := by
  intro hg₂ hg₃ r b hb
  refine hyperplaneKappa_transport (gmMG L b) (gmStd 0 _ (fun _ : Fin r => L.pp)) (phiMG hb) ?_ ?_ ?_ ?_ ?_
    (hS 0 _ r _ (fun _ => ⟨hg₂, hg₃⟩))
  · -- algebraic vectors
    rintro v ⟨h1, h2, ⟨z, hz, hzv⟩⟩
    rw [phiMG_apply]
    refine ⟨fun i => i.elim0, phiT_apply_forall v.1 h1 h2, fun j => ?_⟩
    rw [← hzv]
    show IsAlgebraic ℚ (E0 L z j)
    rw [E0_apply]
    exact (hz _).add (L.isAlgebraic_α.mul (hz _))
  · -- logarithms
    intro v hv
    obtain ⟨D, hD, hDv⟩ := exists_nsmul_mem_closure _ hv
    refine ⟨D, hD, lamPer_le_Lam _ ?_⟩
    have hle : AddSubgroup.closure (lamGen (ι := Fin r × Fin 2) (perQm L b)) ≤
        (lamPer (d0 := 0) (fun _ : Fin r => L.pp)).comap (phiMG hb).toLinearMap.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro g ((⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨q, hq, rfl⟩)
      · show phiMG hb (tor1 j x) ∈ lamPer _
        rw [phiMG_apply]
        refine ⟨fun i => i.elim0, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _ (fun i => ?_)
          (fun i => by simpa [tor1] using isAlgebraic_one),
          fun j' => by simp [tor1]⟩
        simp only [tor1, Pi.single_apply]; split_ifs
        exacts [hx, by simpa using isAlgebraic_one]
      · show phiMG hb (tor2 j x) ∈ lamPer _
        rw [phiMG_apply]
        refine ⟨fun i => i.elim0, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _
          (fun i => by simpa [tor2] using isAlgebraic_one) (fun i => ?_),
          fun j' => by simp [tor2]⟩
        simp only [tor2, Pi.single_apply]; split_ifs
        exacts [hx, by simpa using isAlgebraic_one]
      · show phiMG hb (qv q) ∈ lamPer _
        rw [phiMG_apply]
        refine ⟨fun i => i.elim0, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _
          (fun i => by simpa [qv] using isAlgebraic_one) (fun i => by simpa [qv] using isAlgebraic_one), ?_⟩
        rcases hq with ⟨p, rfl⟩ | ⟨p, rfl⟩
        · exact fun j => E0_single_mem hint p (Or.inl rfl) j
        · exact fun j => E0_single_mem hint p (Or.inr rfl) j
    exact hle hDv
  · -- periods
    intro v hv
    have hle : Submodule.span ℚ (perGen (ι := Fin r × Fin 2) (perQm L b)) ≤
        (Submodule.span ℚ (Per (d0 := 0) (d1 := Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2)))
          (fun _ : Fin r => L.pp) : Set _)).comap (ratMap (phiMG hb)) := by
      rw [Submodule.span_le]
      intro g hg
      apply Submodule.subset_span
      rw [ratMap_apply, phiMG_apply]
      refine ⟨Subsingleton.elim _ _, ?_, ?_⟩
      · rcases hg with (⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, -, rfl⟩
        · refine phiT_apply_forall (P := fun z => ∃ k : ℤ, z = 2 * Real.pi * I * k) _ (fun i => ?_)
            (fun i => ⟨0, by simp [tor1]⟩)
          simp only [tor1, Pi.single_apply]; split_ifs
          exacts [⟨1, by simp⟩, ⟨0, by simp⟩]
        · refine phiT_apply_forall (P := fun z => ∃ k : ℤ, z = 2 * Real.pi * I * k) _
            (fun i => ⟨0, by simp [tor2]⟩) (fun i => ?_)
          simp only [tor2, Pi.single_apply]; split_ifs
          exacts [⟨1, by simp⟩, ⟨0, by simp⟩]
        · exact phiT_apply_forall (P := fun z => ∃ k : ℤ, z = 2 * Real.pi * I * k) _
            (fun i => ⟨0, by simp [qv]⟩) (fun i => ⟨0, by simp [qv]⟩)
      · rcases hg with (⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩
        · intro j'; simp [tor1]
        · intro j'; simp [tor2]
        · rcases hq with ⟨p, rfl⟩ | ⟨p, rfl⟩
          · exact fun j => E0_single_mem hint p (Or.inl rfl) j
          · exact fun j => E0_single_mem hint p (Or.inr rfl) j
    exact hle hv
  · -- subgroups
    rintro S ⟨H, rfl⟩ hne
    refine ⟨(K11.annQ H.U).map (rhoT (Fin r × Fin 2)).toLinearMap, H.t.comap (phiE hb).toLinearMap, ?_, ?_⟩
    · by_cases ht : H.t = ⊥
      · left
        rw [ht, Submodule.comap_bot, LinearEquiv.ker]
      · right
        -- a nonzero lattice vector in `t`
        obtain ⟨z, ⟨hzt, hzl⟩, hz0⟩ : ∃ z, (z ∈ H.t ∧ ∀ j, z j ∈ L.pp.lattice) ∧ z ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply ht
          have hab := H.t_ab
          have hspan : Submodule.span ℝ {z : Fin r → ℂ | z ∈ H.t ∧ ∀ j, z j ∈ ((fun _ : Fin r => L.pp) j).lattice} = ⊥ := by
            rw [Submodule.span_eq_bot]
            exact fun z hz => hcon z hz
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ (H.t.restrictScalars ℝ : Submodule ℝ (Fin r → ℂ)) := hx
          rw [hab, hspan] at this
          exact this
        refine ⟨(phiE hb).symm z, by simpa using hzt, ?_⟩
        rw [lamM_phiE hb, LinearEquiv.apply_symm_apply]
        intro hsum
        choose mm nn hmn using fun j => PeriodPair.mem_lattice.mp (hzl j)
        have hzj : ∀ j, z j = ((mm j : ℂ) + nn j * L.α) * L.ω := fun j => by
          rw [← hmn j, L.hω₁, L.hω₂]; ring
        have hω := L.ω_ne_zero
        have hsum' : (∑ j, b j * (((mm j : ℚ) : ℂ) + ((nn j : ℚ) : ℂ) * L.α)) * L.ω = 0 := by
          rw [Finset.sum_mul, ← hsum]
          exact Finset.sum_congr rfl fun j _ => by rw [hzj]; push_cast; ring
        obtain ⟨hu, hw⟩ := b_kindep hb (fun j => mm j) (fun j => nn j) ((mul_eq_zero.mp hsum').resolve_right hω)
        apply hz0
        funext j
        have h1 : (mm j : ℚ) = 0 := congrFun hu j
        have h2 : (nn j : ℚ) = 0 := congrFun hw j
        rw [hzj, Pi.zero_apply]
        simp [show (mm j : ℂ) = 0 by exact_mod_cast h1, show (nn j : ℂ) = 0 by exact_mod_cast h2]
    · rw [← comap_phiT_torusLie]
      ext v
      simp only [Submodule.mem_comap, SubgroupData.tan, Submodule.mem_prod, LinearEquiv.coe_coe, phiMG_apply]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨by rw [Subsingleton.elim (0 : Fin 0 → ℂ) 0]; exact H.h0.zero_mem,
        h.1, h.2⟩⟩
  · -- the count
    show Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2)) + 2 * r ≤
      2 * Fintype.card (Fin r × Fin 2) + 2 * finrank ℂ (Qm L b)
    rw [(phiE hb).finrank_eq, Fintype.card_sum]
    simp
    omega

end CM4E.Bridge
