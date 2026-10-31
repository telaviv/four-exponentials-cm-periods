/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.MG
import CM4E.Gen.SMG

/-!
# Theorem SMG's hypothesis from the standard model

The model `gmSMG L b` of `G_a² × G_m^{2n} × A''` (`CM4E/Gen/SMG.lean`, frame `gmF2` with the uniform subgroup condition)
is identified with the standard model `gmStd 2 (2n) (E, …, E)` by `(x, y, (a₁, a₂, [z])) ↦ ((a₁, a₂), (x, y), E0 z)`
(`phiSMG`, using `phiE` of `CM4E/Bridge/MG.lean`), and `thm11KappaSMG_of_std` derives `Thm11KappaSMG L` from `HypStdCM L.pp`.
The uniform subgroup condition is proved: a nonzero `h₀ × U^⊥ × t` contains an algebraic vector with `Ψ'' ≠ 0` (an
algebraic vector of `h₀`; a rational vector of `U^⊥`; or `z/ω` for a nonzero lattice vector `z ∈ t`).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen LSG.W88

namespace CM4E.Bridge

variable {L : CMLattice} {r : ℕ} {b : Fin r → ℂ}

/-- The coordinate isomorphism `T(G_a² × G_m^{2n} × A'') ≅ ℂ² × ℂ^{2n} × ℂ^r`. -/
noncomputable def phiSMG (hb : IsAdaptedFieldBasis L.α b) :
    TF (Fin r × Fin 2) (QS L b) ≃ₗ[ℂ] Tan 2 (Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2))) r where
  toFun v := (![v.2.1, v.2.2.1], phiT _ v.1, phiE hb v.2.2.2)
  invFun w := ((phiT _).symm w.2.1, (w.1 0, w.1 1, (phiE hb).symm w.2.2))
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; fin_cases i <;> simp
    · simp
    · simp
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; fin_cases i <;> simp
    · simp
    · simp
  left_inv v := by simp
  right_inv w := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; fin_cases i <;> simp
    · simp
    · simp

lemma phiSMG_apply (hb : IsAdaptedFieldBasis L.α b) (v : TF (Fin r × Fin 2) (QS L b)) :
    phiSMG hb v = (![v.2.1, v.2.2.1], phiT _ v.1, phiE hb v.2.2.2) := rfl

lemma phiSMG_symm_apply (hb : IsAdaptedFieldBasis L.α b)
    (w : Tan 2 (Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2))) r) :
    (phiSMG hb).symm w = ((phiT _).symm w.2.1, (w.1 0, w.1 1, (phiE hb).symm w.2.2)) := rfl

/-- **Thm11KappaSMG from the standard model** (`L` with `α` integral). -/
theorem thm11KappaSMG_of_std (L : CMLattice) (hS : HypStdCM L.pp) (hint : ∃ a c : ℤ, L.α ^ 2 = a + c * L.α) :
    Thm11KappaSMG L := by
  intro hg₂ hg₃ r b hb
  have hθalg := theta_isAlgebraic L.isAlgebraic_α hb.alg
  have hexp0 : IsAlgebraic ℚ (Complex.exp 0) := by simpa using isAlgebraic_one
  refine hyperplaneKappa_transport (gmSMG L b) (gmStd 2 _ (fun _ : Fin r => L.pp)) (phiSMG hb) ?_ ?_ ?_ ?_ ?_
    (hS 2 _ r hg₂ hg₃)
  · -- algebraic vectors
    rintro v ⟨h1, h2, ⟨ha1, ha2, ⟨z, hz, hzv⟩⟩⟩
    rw [phiSMG_apply]
    refine ⟨fun i => ?_, phiT_apply_forall v.1 h1 h2, fun j => ?_⟩
    · fin_cases i
      exacts [ha1, ha2]
    · show IsAlgebraic ℚ (phiE hb v.2.2.2 j)
      rw [← hzv, phiE_mk, E0_apply]
      exact (hz _).add (L.isAlgebraic_α.mul (hz _))
  · -- logarithms
    intro v hv
    obtain ⟨D, hD, hDv⟩ := exists_nsmul_mem_closure _ hv
    refine ⟨D, hD, lamPer_le_Lam _ ?_⟩
    have hle : AddSubgroup.closure (lamSS L b) ≤
        (lamPer (d0 := 2) (fun _ : Fin r => L.pp)).comap (phiSMG hb).toLinearMap.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro g (((⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨a, a', ha, ha', rfl⟩) | ⟨q, hq, rfl⟩)
      · show phiSMG hb (tor1 j x) ∈ lamPer _
        rw [phiSMG_apply]
        refine ⟨fun i => by fin_cases i <;> simpa [tor1] using isAlgebraic_zero,
          phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z))
          _ (fun i => ?_) (fun i => by simpa [tor1] using isAlgebraic_one), fun j' => by simp [tor1]⟩
        simp only [tor1, Pi.single_apply]; split_ifs
        exacts [hx, by simpa using isAlgebraic_one]
      · show phiSMG hb (tor2 j x) ∈ lamPer _
        rw [phiSMG_apply]
        refine ⟨fun i => by fin_cases i <;> simpa [tor2] using isAlgebraic_zero,
          phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z))
          _ (fun i => by simpa [tor2] using isAlgebraic_one) (fun i => ?_), fun j' => by simp [tor2]⟩
        simp only [tor2, Pi.single_apply]; split_ifs
        exacts [hx, by simpa using isAlgebraic_one]
      · show phiSMG hb (qv ((a, a', 0) : QS L b)) ∈ lamPer _
        rw [phiSMG_apply]
        refine ⟨fun i => ?_, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z))
          _ (fun i => by simpa [qv] using isAlgebraic_one) (fun i => by simpa [qv] using isAlgebraic_one),
          fun j' => by simp [qv]⟩
        fin_cases i
        exacts [ha, ha']
      · show phiSMG hb (qv (inQS L b q)) ∈ lamPer _
        rw [phiSMG_apply]
        refine ⟨fun i => by fin_cases i <;> simpa [qv, inQS] using isAlgebraic_zero, phiT_apply_forall
          (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _ (fun i => by simpa [qv] using isAlgebraic_one)
          (fun i => by simpa [qv] using isAlgebraic_one), ?_⟩
        rcases hq with ⟨p, rfl⟩ | ⟨p, rfl⟩
        · exact fun j => E0_single_mem hint p (Or.inl rfl) j
        · exact fun j => E0_single_mem hint p (Or.inr rfl) j
    exact hle hDv
  · -- periods
    intro v hv
    have hle : Submodule.span ℚ (perSS L b) ≤
        (Submodule.span ℚ (Per (d0 := 2) (d1 := Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2)))
          (fun _ : Fin r => L.pp) : Set _)).comap (ratMap (phiSMG hb)) := by
      rw [Submodule.span_le]
      intro g hg
      apply Submodule.subset_span
      rw [ratMap_apply, phiSMG_apply]
      rcases hg with (⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨q, hq, rfl⟩
      · refine ⟨by funext i; fin_cases i <;> simp [tor1], phiT_apply_forall
          (P := fun z => ∃ k : ℤ, z = 2 * Real.pi * I * k) _ (fun i => ?_) (fun i => ⟨0, by simp [tor1]⟩),
          fun j' => by simp [tor1]⟩
        simp only [tor1, Pi.single_apply]; split_ifs
        exacts [⟨1, by simp⟩, ⟨0, by simp⟩]
      · refine ⟨by funext i; fin_cases i <;> simp [tor2], phiT_apply_forall
          (P := fun z => ∃ k : ℤ, z = 2 * Real.pi * I * k) _ (fun i => ⟨0, by simp [tor2]⟩) (fun i => ?_),
          fun j' => by simp [tor2]⟩
        simp only [tor2, Pi.single_apply]; split_ifs
        exacts [⟨1, by simp⟩, ⟨0, by simp⟩]
      · refine ⟨by funext i; fin_cases i <;> simp [qv, inQS], phiT_apply_forall
          (P := fun z => ∃ k : ℤ, z = 2 * Real.pi * I * k) _ (fun i => ⟨0, by simp [qv]⟩)
          (fun i => ⟨0, by simp [qv]⟩), ?_⟩
        rcases hq with ⟨p, rfl⟩ | ⟨p, rfl⟩
        · exact fun j => E0_single_mem hint p (Or.inl rfl) j
        · exact fun j => E0_single_mem hint p (Or.inr rfl) j
    exact hle hv
  · -- subgroups (uniform condition)
    rintro S ⟨H, rfl⟩ hne
    right
    by_cases h0 : H.h0 = ⊥
    · by_cases hU : torusLie H.U = ⊥
      · -- the abelian part is nonzero
        have ht : H.t ≠ ⊥ := by
          intro ht; apply hne
          rw [SubgroupData.tan, h0, hU, ht]
          simp
        obtain ⟨z, ⟨hzt, hzl⟩, hz0⟩ : ∃ z, (z ∈ H.t ∧ ∀ j, z j ∈ L.pp.lattice) ∧ z ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply ht
          have hspan : Submodule.span ℝ {z : Fin r → ℂ | z ∈ H.t ∧ ∀ j, z j ∈ ((fun _ : Fin r => L.pp) j).lattice} = ⊥ := by
            rw [Submodule.span_eq_bot]
            exact fun z hz => hcon z hz
          rw [eq_bot_iff]
          intro x hx
          have : x ∈ (H.t.restrictScalars ℝ : Submodule ℝ (Fin r → ℂ)) := hx
          rw [H.t_ab, hspan] at this
          exact this
        choose mm nn hmn using fun j => PeriodPair.mem_lattice.mp (hzl j)
        have hω := L.ω_ne_zero
        set y : Fin r → ℂ := fun j => (mm j : ℂ) + nn j * L.α with hy
        have hzj : z = L.ω • y := by
          funext j; rw [← hmn j, L.hω₁, L.hω₂]; simp [hy]; ring
        have hyt : y ∈ H.t := by
          have := H.t.smul_mem (L.ω)⁻¹ hzt
          rwa [hzj, smul_smul, inv_mul_cancel₀ hω, one_smul] at this
        set w : Fin r × Fin 2 → ℂ := fun p => if p.2 = 0 then y p.1 else 0
        have hw : E0 L w = y := by funext j; simp [E0_apply, w]
        refine ⟨qv (ι := Fin r × Fin 2) ((0, 0, Submodule.Quotient.mk w) : QS L b), ?_, ⟨fun _ => isAlgebraic_zero,
          fun _ => isAlgebraic_zero, isAlgebraic_zero, isAlgebraic_zero, w, fun p => ?_, rfl⟩, ?_⟩
        · show phiSMG hb _ ∈ H.tan
          rw [phiSMG_apply]
          refine ⟨?_, ?_, ?_⟩
          · have : (![(qv (ι := Fin r × Fin 2) ((0, 0, Submodule.Quotient.mk w) : QS L b)).2.1,
                (qv (ι := Fin r × Fin 2) ((0, 0, Submodule.Quotient.mk w) : QS L b)).2.2.1] : Fin 2 → ℂ) = 0 := by
              funext i; fin_cases i <;> simp [qv]
            rw [this]; exact H.h0.zero_mem
          · have : phiT (Fin r × Fin 2) (qv (ι := Fin r × Fin 2) ((0, 0, Submodule.Quotient.mk w) : QS L b)).1 = 0 := by
              simp [qv]
            rw [this]; exact (torusLie H.U).zero_mem
          · show phiE hb (Submodule.Quotient.mk w) ∈ H.t
            rw [phiE_mk, hw]; exact hyt
        · simp only [w]; split_ifs
          · show IsAlgebraic ℚ ((mm p.1 : ℂ) + nn p.1 * L.α)
            rw [← mem_algebraicClosure_iff]
            exact add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) (mem_algebraicClosure_iff.mpr L.isAlgebraic_α))
          · exact isAlgebraic_zero
        · rw [PsiG_apply]
          intro h
          have h2 := congrArg Prod.snd h
          simp only [qv, map_zero, zero_add, lamS_apply, Prod.snd_zero] at h2
          rw [lamM_phiE hb, phiE_mk, hw] at h2
          obtain ⟨hu, hv⟩ := b_kindep hb (fun j => mm j) (fun j => nn j) (by simpa [hy] using h2)
          apply hz0
          rw [hzj]
          funext j
          have e1 : (mm j : ℚ) = 0 := congrFun hu j
          have e2 : (nn j : ℚ) = 0 := congrFun hv j
          simp [hy, show (mm j : ℂ) = 0 by exact_mod_cast e1, show (nn j : ℂ) = 0 by exact_mod_cast e2]
      · -- the toric part is nonzero: a rational vector
        have hne' : K11.annQ H.U ≠ ⊥ := by
          intro h; apply hU
          rw [show torusLie H.U = K11.cspan (K11.annQ H.U) from K11.annC_eq_cspan H.U, h, K11.cspan_bot]
        obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
        set u : (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ) :=
          (phiT _).symm (fun k => ((q k : ℚ) : ℂ)) with hu
        refine ⟨((u, (0 : QS L b))), ?_, ⟨fun j => ?_, fun j => ?_, isAlgebraic_zero, isAlgebraic_zero,
          0, fun _ => isAlgebraic_zero, by simp⟩, ?_⟩
        · show phiSMG hb _ ∈ H.tan
          rw [phiSMG_apply]
          refine ⟨?_, ?_, ?_⟩
          · have : (![((u, (0 : QS L b))).2.1, ((u, (0 : QS L b))).2.2.1] : Fin 2 → ℂ) = 0 := by
              funext i; fin_cases i <;> simp
            rw [this]; exact H.h0.zero_mem
          · simp only [hu, LinearEquiv.apply_symm_apply]
            rw [show torusLie H.U = K11.cspan (K11.annQ H.U) from K11.annC_eq_cspan H.U]
            exact K11.castL_mem_cspan hq
          · simp
        · simp only [hu, phiT_symm_cast]; exact isAlgebraic_algebraMap _
        · simp only [hu, phiT_symm_cast]; exact isAlgebraic_algebraMap _
        · rw [PsiG_apply]
          intro h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          simp only [map_zero, add_zero, Prod.fst_zero, Prod.snd_zero, hu, phiT_symm_cast] at h1 h2
          have z1 := dot_rat_eq_zero hb.indep _ h1
          have z2 := dot_rat_eq_zero hb.indep _ h2
          apply hq0
          have : rhoT (Fin r × Fin 2) q = 0 := Prod.ext z1 z2
          simpa using congrArg (rhoT (Fin r × Fin 2)).symm this
    · -- the `G_a` part is nonzero: an algebraic vector
      obtain ⟨a, ha, ha0⟩ : ∃ a ∈ H.h0, AlgVec a ∧ a ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply h0
        rw [H.h0_rat, Submodule.span_eq_bot]
        rintro x ⟨hx, hxa⟩
        exact hcon x hx hxa
      refine ⟨((0, (a 0, a 1, 0)) : TF (Fin r × Fin 2) (QS L b)), ?_, ⟨fun _ => isAlgebraic_zero,
        fun _ => isAlgebraic_zero, ha0.1 0, ha0.1 1, 0, fun _ => isAlgebraic_zero, by simp⟩, ?_⟩
      · show phiSMG hb _ ∈ H.tan
        rw [phiSMG_apply]
        refine ⟨?_, by simp [(torusLie H.U).zero_mem], by simp [H.t.zero_mem]⟩
        have : (![(a 0), (a 1)] : Fin 2 → ℂ) = a := by funext i; fin_cases i <;> rfl
        simpa [this] using ha
      · rw [PsiG_apply]
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [map_zero, zero_add, muS_apply, lamS_apply, Prod.fst_zero, Prod.snd_zero, add_zero] at h1 h2
        apply ha0.2
        funext i; fin_cases i
        · exact h1
        · simpa using h2
  · -- the count
    show Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2)) + 2 * r ≤
      2 * Fintype.card (Fin r × Fin 2) + 2 * finrank ℂ (Qm L b)
    rw [(phiE hb).finrank_eq, Fintype.card_sum]
    simp
    omega

end CM4E.Bridge
