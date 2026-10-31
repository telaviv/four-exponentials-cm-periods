/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.SMG
import CM4E.Bridge.ELog
import CM4E.Gen.MGK

/-!
# The `K`-form of Theorem MG from the standard model

The model `gmMGK L b` of `G_m^{2n} × A''` with elliptic logarithms (`CM4E/Gen/MGK.lean`, frame `gmF2` with `μ = 0`)
is identified with the standard model `gmStd 0 (2n) (E, …, E)` by the map `phiMG` of `CM4E/Bridge/MG.lean`, and
`thm11KappaMGK_of_std` derives `Thm11KappaMGK L` from `HypStdCMAt L.pp 0`. Beyond the MG bridge this uses the arithmetic
of elliptic logarithms (`CM4E/Bridge/ELog.lean`): the images `u e_j`, `αu e_j` of the generators `[u e_{(j,k)}]` are
logarithms of algebraic points when `α` acts on them (`CMMulLogE L`), and sums of such are again logarithms
(`lamLog`, the addition law).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen LSG.W88

namespace CM4E.Bridge

variable {d0 d1 m : ℕ}

/-- The logarithms whose `E`-coordinates are elliptic logarithms of algebraic points (`g₂` algebraic): an additive
subgroup of `Lam`. -/
def lamLog (P : PeriodPair) (hg₂ : IsAlgebraic ℚ P.g₂) : AddSubgroup (Tan d0 d1 m) where
  carrier := {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧ ∀ j, LogE P (p.2.2 j)}
  add_mem' {p q} hp hq := by
    refine ⟨fun i => (hp.1 i).add (hq.1 i), fun i => ?_, fun j => logE_add P hg₂ (hp.2.2 j) (hq.2.2 j)⟩
    show IsAlgebraic ℚ (Complex.exp (p.2.1 i + q.2.1 i))
    rw [Complex.exp_add]; exact (hp.2.1 i).mul (hq.2.1 i)
  zero_mem' := ⟨fun _ => isAlgebraic_zero, fun _ => by simpa using isAlgebraic_one, fun _ => Or.inl P.lattice.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨fun i => (hp.1 i).neg, fun i => ?_, fun j => logE_neg P (hp.2.2 j)⟩
    show IsAlgebraic ℚ (Complex.exp (-p.2.1 i))
    rw [Complex.exp_neg]; exact (hp.2.1 i).inv

lemma lamLog_le_Lam (P : PeriodPair) (hg₂ : IsAlgebraic ℚ P.g₂) :
    ((lamLog (d0 := d0) (d1 := d1) (m := m) P hg₂ : Set (Tan d0 d1 m))) ⊆ Lam (fun _ => P) :=
  fun _ hp => ⟨hp.1, hp.2.1, fun j => (hp.2.2 j).imp id fun h => h.1⟩

variable {L : CMLattice} {r : ℕ} {b : Fin r → ℂ}

/-- `E0` of a single elliptic logarithm is a vector of elliptic logarithms. -/
lemma E0_single_logE (hCM : CMMulLogE L) (p : Fin r × Fin 2) {u : ℂ} (hu : LogE L.pp u) (j : Fin r) :
    LogE L.pp (E0 L (Pi.single p u) j) := by
  rw [E0_apply]
  obtain ⟨j', k⟩ := p
  have h0 : LogE L.pp 0 := Or.inl L.pp.lattice.zero_mem
  by_cases hj : j = j'
  · subst hj
    fin_cases k
    · simpa [Pi.single_apply] using hu
    · simpa [Pi.single_apply] using hCM u hu
  · simpa [Pi.single_apply, hj] using h0

/-- **Thm11KappaMGK from the standard model** (`L` with `α` integral and acting on elliptic logarithms). -/
theorem thm11KappaMGK_of_std (L : CMLattice) (hS : HypStdCMAt L.pp 0) (hint : ∃ a c : ℤ, L.α ^ 2 = a + c * L.α)
    (hCM : CMMulLogE L) : Thm11KappaMGK L := by
  intro hg₂ hg₃ r b hb
  refine hyperplaneKappa_transport (gmMGK L b) (gmStd 0 _ (fun _ : Fin r => L.pp)) (phiMG hb) ?_ ?_ ?_ ?_ ?_
    (hS _ r hg₂ hg₃)
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
    refine ⟨D, hD, lamLog_le_Lam L.pp hg₂ ?_⟩
    have hle : AddSubgroup.closure (lamMGK L b) ≤
        (lamLog (d0 := 0) (m := r) L.pp hg₂).comap (phiMG hb).toLinearMap.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro g ((⟨j, x, hx, rfl⟩ | ⟨j, x, hx, rfl⟩) | ⟨p, u, hu, rfl⟩)
      · show phiMG hb (tor1 j x) ∈ lamLog _ hg₂
        rw [phiMG_apply]
        refine ⟨fun i => i.elim0, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _ (fun i => ?_)
          (fun i => by simpa [tor1] using isAlgebraic_one),
          fun j' => by simp only [tor1, map_zero, Pi.zero_apply]; exact Or.inl L.pp.lattice.zero_mem⟩
        simp only [tor1, Pi.single_apply]; split_ifs
        exacts [hx, by simpa using isAlgebraic_one]
      · show phiMG hb (tor2 j x) ∈ lamLog _ hg₂
        rw [phiMG_apply]
        refine ⟨fun i => i.elim0, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _
          (fun i => by simpa [tor2] using isAlgebraic_one) (fun i => ?_),
          fun j' => by simp only [tor2, map_zero, Pi.zero_apply]; exact Or.inl L.pp.lattice.zero_mem⟩
        simp only [tor2, Pi.single_apply]; split_ifs
        exacts [hx, by simpa using isAlgebraic_one]
      · show phiMG hb (qv (Submodule.Quotient.mk (Pi.single p u) : Qm L b)) ∈ lamLog _ hg₂
        rw [phiMG_apply]
        refine ⟨fun i => i.elim0, phiT_apply_forall (P := fun z => IsAlgebraic ℚ (Complex.exp z)) _
          (fun i => by simpa [qv] using isAlgebraic_one) (fun i => by simpa [qv] using isAlgebraic_one),
          fun j => ?_⟩
        show LogE L.pp (phiE hb (Submodule.Quotient.mk (Pi.single p u)) j)
        rw [phiE_mk]
        exact E0_single_logE hCM p hu j
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
  · -- subgroups (uniform condition)
    rintro S ⟨H, rfl⟩ hne
    right
    by_cases hU : torusLie H.U = ⊥
    · -- the abelian part is nonzero
      have ht : H.t ≠ ⊥ := by
        intro ht; apply hne
        rw [SubgroupData.tan, hU, ht, show H.h0 = ⊥ from Subsingleton.elim _ _]
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
      refine ⟨qv (ι := Fin r × Fin 2) (Submodule.Quotient.mk w : Qm L b), ?_, ⟨fun _ => isAlgebraic_zero,
        fun _ => isAlgebraic_zero, w, fun p => ?_, rfl⟩, ?_⟩
      · show phiMG hb _ ∈ H.tan
        rw [phiMG_apply]
        refine ⟨H.h0.zero_mem, ?_, ?_⟩
        · have : phiT (Fin r × Fin 2) (qv (ι := Fin r × Fin 2) (Submodule.Quotient.mk w : Qm L b)).1 = 0 := by
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
        simp only [qv, map_zero, zero_add, Prod.snd_zero] at h2
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
      refine ⟨((u, (0 : Qm L b))), ?_, ⟨fun j => ?_, fun j => ?_, 0, fun _ => isAlgebraic_zero, by simp⟩, ?_⟩
      · show phiMG hb _ ∈ H.tan
        rw [phiMG_apply]
        refine ⟨H.h0.zero_mem, ?_, ?_⟩
        · simp only [hu, LinearEquiv.apply_symm_apply]
          rw [show torusLie H.U = K11.cspan (K11.annQ H.U) from K11.annC_eq_cspan H.U]
          exact K11.castL_mem_cspan hq
        · simp [H.t.zero_mem]
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
  · -- the count
    show Fintype.card ((Fin r × Fin 2) ⊕ (Fin r × Fin 2)) + 2 * r ≤
      2 * Fintype.card (Fin r × Fin 2) + 2 * finrank ℂ (Qm L b)
    rw [(phiE hb).finrank_eq, Fintype.card_sum]
    simp
    omega

end CM4E.Bridge
