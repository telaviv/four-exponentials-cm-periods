/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.MGK
import CM4E.Gen.ThmM

/-!
# Theorem M's hypothesis from the standard model

The model `gmM L b` of `A'' × G_m^n × G_a` (`CM4E/Gen/ThmM.lean`, frame `gmFM` with the uniform subgroup condition) is
identified with the standard model `gmStd 1 n (E, …, E)` by `(q, y, s) ↦ (s, y, E0 q)` (`phiMM`), and
`thm11KappaM_of_std` derives `Thm11KappaM L` from `HypStdCMAt L.pp 1`. The logarithms use the arithmetic of elliptic
logarithms (`lamLog`, `CMMulLogE`), as in `CM4E/Bridge/MGK.lean`. The uniform subgroup condition: a nonzero
`h₀ × U^⊥ × t` contains an algebraic vector with `Ψ'' ≠ 0` (an algebraic vector of `h₀`, a rational vector of `U^⊥`,
or `z/ω` for a nonzero lattice vector `z ∈ t`).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen LSG.W88

namespace CM4E.Bridge

variable (ι : Type) [Fintype ι]

/-- An enumeration of `ι`. -/
noncomputable def eT1 : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι

/-- The toric coordinates `y ∈ ℂ^ι` as a vector of `ℂ^n`. -/
noncomputable def phi1 : (ι → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (eT1 ι).symm

lemma phi1_apply (y : ι → ℂ) (k : Fin (Fintype.card ι)) : phi1 ι y k = y ((eT1 ι).symm k) := rfl

lemma phi1_symm_apply (w : Fin (Fintype.card ι) → ℂ) (j : ι) : (phi1 ι).symm w j = w (eT1 ι j) := by
  obtain ⟨y, rfl⟩ := (phi1 ι).surjective w
  simp [phi1_apply]

variable {L : CMLattice} {r : ℕ} {b : Fin r → ℂ}

/-- The coordinate isomorphism `T(A'' × G_m^n × G_a) ≅ ℂ × ℂ^n × ℂ^r`. -/
noncomputable def phiMM (hb : IsAdaptedFieldBasis L.α b) :
    TM (Fin r × Fin 2) (Qm L b) ≃ₗ[ℂ] Tan 1 (Fintype.card (Fin r × Fin 2)) r where
  toFun v := (![v.2.2], phi1 _ v.2.1, phiE hb v.1)
  invFun w := ((phiE hb).symm w.2.2, (phi1 _).symm w.2.1, w.1 0)
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; fin_cases i; simp
    · simp
    · simp
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; fin_cases i; simp
    · simp
    · simp
  left_inv v := by simp
  right_inv w := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; fin_cases i; simp
    · simp
    · simp

lemma phiMM_apply (hb : IsAdaptedFieldBasis L.α b) (v : TM (Fin r × Fin 2) (Qm L b)) :
    phiMM hb v = (![v.2.2], phi1 _ v.2.1, phiE hb v.1) := rfl

/-- **Thm11KappaM from the standard model** (`L` with `α` integral and acting on elliptic logarithms). -/
theorem thm11KappaM_of_std (L : CMLattice) (hS : HypStdCMAt L.pp 1) (hint : ∃ a c : ℤ, L.α ^ 2 = a + c * L.α)
    (hCM : CMMulLogE L) : Thm11KappaM L := by
  intro hg₂ hg₃ r b hb
  have h0E : LogE L.pp 0 := Or.inl L.pp.lattice.zero_mem
  refine hyperplaneKappa_transport (gmM L b) (gmStd 1 _ (fun _ : Fin r => L.pp)) (phiMM hb) ?_ ?_ ?_ ?_ ?_
    (hS _ r hg₂ hg₃)
  · -- algebraic vectors
    rintro v ⟨⟨z, hz, hzv⟩, h1, h2⟩
    rw [phiMM_apply]
    refine ⟨fun i => by fin_cases i; exact h2, fun k => by show IsAlgebraic ℚ (phi1 _ v.2.1 k); rw [phi1_apply]; exact h1 _, fun j => ?_⟩
    rw [← hzv]
    show IsAlgebraic ℚ (phiE hb (Submodule.Quotient.mk z) j)
    rw [phiE_mk, E0_apply]
    exact (hz _).add (L.isAlgebraic_α.mul (hz _))
  · -- logarithms
    intro v hv
    obtain ⟨D, hD, hDv⟩ := exists_nsmul_mem_closure _ hv
    refine ⟨D, hD, lamLog_le_Lam L.pp hg₂ ?_⟩
    have hle : AddSubgroup.closure (lamMS L b) ≤
        (lamLog (d0 := 1) (m := r) L.pp hg₂).comap (phiMM hb).toLinearMap.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro g ((⟨p, u, hu, rfl⟩ | ⟨h, l, hl, rfl⟩) | ⟨c, hc, rfl⟩)
      · show phiMM hb (eSlot L b p u) ∈ lamLog _ hg₂
        rw [phiMM_apply]
        refine ⟨fun i => by fin_cases i; simpa [eSlot] using isAlgebraic_zero,
          fun k => by simpa [eSlot, phi1_apply] using isAlgebraic_one, fun j => ?_⟩
        show LogE L.pp (phiE hb (Submodule.Quotient.mk (Pi.single p u)) j)
        rw [phiE_mk]
        exact E0_single_logE hCM p hu j
      · show phiMM hb (mSlot L b h l) ∈ lamLog _ hg₂
        rw [phiMM_apply]
        refine ⟨fun i => by fin_cases i; simpa [mSlot] using isAlgebraic_zero, fun k => ?_,
          fun j => by simp only [mSlot, map_zero, Pi.zero_apply]; exact h0E⟩
        simp only [mSlot, phi1_apply, Pi.single_apply]; split_ifs
        exacts [hl, by simpa using isAlgebraic_one]
      · show phiMM hb (aSlot L b c) ∈ lamLog _ hg₂
        rw [phiMM_apply]
        refine ⟨fun i => by fin_cases i; simpa [aSlot] using hc,
          fun k => by simpa [aSlot, phi1_apply] using isAlgebraic_one,
          fun j => by simp only [aSlot, map_zero, Pi.zero_apply]; exact h0E⟩
    exact hle hDv
  · -- periods
    intro v hv
    have hle : Submodule.span ℚ (perMS L b) ≤
        (Submodule.span ℚ (Per (d0 := 1) (d1 := Fintype.card (Fin r × Fin 2))
          (fun _ : Fin r => L.pp) : Set _)).comap (ratMap (phiMM hb)) := by
      rw [Submodule.span_le]
      intro g hg
      apply Submodule.subset_span
      rw [ratMap_apply, phiMM_apply]
      rcases hg with ⟨q, hq, rfl⟩ | ⟨h, rfl⟩
      · refine ⟨by funext i; fin_cases i; simp, fun k => ⟨0, by simp [phi1_apply]⟩, ?_⟩
        rcases hq with ⟨p, rfl⟩ | ⟨p, rfl⟩
        · exact fun j => by rw [phiE_mk]; exact E0_single_mem hint p (Or.inl rfl) j
        · exact fun j => by rw [phiE_mk]; exact E0_single_mem hint p (Or.inr rfl) j
      · refine ⟨by funext i; fin_cases i; simp [mSlot], fun k => ?_, fun j => by simp [mSlot]⟩
        simp only [mSlot, phi1_apply, Pi.single_apply]; split_ifs
        exacts [⟨1, by simp⟩, ⟨0, by simp⟩]
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
        refine ⟨((Submodule.Quotient.mk w : Qm L b), 0, 0), ?_, ⟨⟨w, fun p => ?_, rfl⟩, fun _ => isAlgebraic_zero,
          isAlgebraic_zero⟩, ?_⟩
        · show phiMM hb _ ∈ H.tan
          rw [phiMM_apply]
          refine ⟨?_, by simp [(torusLie H.U).zero_mem], ?_⟩
          · have : (![(((Submodule.Quotient.mk w : Qm L b), (0 : Fin r × Fin 2 → ℂ), (0 : ℂ)) :
                TM (Fin r × Fin 2) (Qm L b)).2.2] : Fin 1 → ℂ) = 0 := by
              funext i; fin_cases i; simp
            rw [this]; exact H.h0.zero_mem
          · show phiE hb (Submodule.Quotient.mk w) ∈ H.t
            rw [phiE_mk, hw]; exact hyt
        · simp only [w]; split_ifs
          · show IsAlgebraic ℚ ((mm p.1 : ℂ) + nn p.1 * L.α)
            rw [← mem_algebraicClosure_iff]
            exact add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) (mem_algebraicClosure_iff.mpr L.isAlgebraic_α))
          · exact isAlgebraic_zero
        · rw [PsiM_apply]
          intro h
          have h1 := congrArg Prod.fst h
          simp only [Prod.fst_zero] at h1
          rw [lamM_phiE hb, phiE_mk, hw] at h1
          obtain ⟨hu, hv⟩ := b_kindep hb (fun j => mm j) (fun j => nn j) (by simpa [hy] using h1)
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
        set u : Fin r × Fin 2 → ℂ := (phi1 _).symm (fun k => ((q k : ℚ) : ℂ)) with hu
        have hu' : ∀ j, u j = ((q (eT1 _ j) : ℚ) : ℂ) := fun j => by rw [hu, phi1_symm_apply]
        refine ⟨((0 : Qm L b), u, 0), ?_, ⟨⟨0, fun _ => isAlgebraic_zero, by simp⟩, fun j => ?_,
          isAlgebraic_zero⟩, ?_⟩
        · show phiMM hb _ ∈ H.tan
          rw [phiMM_apply]
          refine ⟨?_, ?_, by simp [H.t.zero_mem]⟩
          · have : (![(((0 : Qm L b), u, (0 : ℂ)) : TM (Fin r × Fin 2) (Qm L b)).2.2] : Fin 1 → ℂ) = 0 := by
              funext i; fin_cases i; simp
            rw [this]; exact H.h0.zero_mem
          · simp only [hu, LinearEquiv.apply_symm_apply]
            rw [show torusLie H.U = K11.cspan (K11.annQ H.U) from K11.annC_eq_cspan H.U]
            exact K11.castL_mem_cspan hq
        · show IsAlgebraic ℚ (u j); rw [hu']; exact isAlgebraic_algebraMap _
        · rw [PsiM_apply]
          intro h
          have h2 := congrArg Prod.snd h
          simp only [Prod.snd_zero, add_zero] at h2
          have h2' : dotL (theta L.α b) (fun j => ((q (eT1 _ j) : ℚ) : ℂ)) = 0 := by
            rw [← h2]; congr 1
          have z := dot_rat_eq_zero hb.indep _ h2'
          apply hq0
          funext k
          have := congrFun z ((eT1 _).symm k)
          simpa using this
    · -- the `G_a` part is nonzero: an algebraic vector
      obtain ⟨a, ha, ha0⟩ : ∃ a ∈ H.h0, AlgVec a ∧ a ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply h0
        rw [H.h0_rat, Submodule.span_eq_bot]
        rintro x ⟨hx, hxa⟩
        exact hcon x hx hxa
      refine ⟨(((0 : Qm L b), 0, a 0) : TM (Fin r × Fin 2) (Qm L b)), ?_, ⟨⟨0, fun _ => isAlgebraic_zero, by simp⟩,
        fun _ => isAlgebraic_zero, ha0.1 0⟩, ?_⟩
      · show phiMM hb _ ∈ H.tan
        rw [phiMM_apply]
        refine ⟨?_, by simp [(torusLie H.U).zero_mem], by simp [H.t.zero_mem]⟩
        have : (![a 0] : Fin 1 → ℂ) = a := by funext i; fin_cases i; rfl
        simpa [this] using ha
      · rw [PsiM_apply]
        intro h
        have h2 := congrArg Prod.snd h
        simp only [map_zero, zero_add, Prod.snd_zero] at h2
        apply ha0.2
        funext i; fin_cases i
        simpa using h2
  · -- the count
    show Fintype.card (Fin r × Fin 2) + 2 * r ≤ Fintype.card (Fin r × Fin 2) + 2 * finrank ℂ (Qm L b)
    rw [(phiE hb).finrank_eq]
    simp

end CM4E.Bridge
