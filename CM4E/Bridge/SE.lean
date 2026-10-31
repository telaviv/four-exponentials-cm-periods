/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.Std
import CM4E.Bridge.Transport
import CM4E.Bridge.MG
import CM4E.Bridge.ELog
import CM4E.AbVar.SE
import CM4E.Final
import LSG.W88.K5dNonIsog

/-!
# Theorem SE from the standard model (two non-isogenous CM curves)

* `hyperplaneKappa_gmES`: the model `gmES Ls a₁ a₂` of `G_a² × E₁ × ⋯ × E_m` (`CM4E/AbVar/SE.lean`) is the standard model
  `gmStd 2 0 Ls` in other coordinates (`phiFX : (q, s₁, s₂) ↦ ((s₁, s₂), (), q)`), so `HyperplaneKappa (gmStd 2 0 Ls)`
  implies `HyperplaneKappa (gmES Ls a₁ a₂)` once every nonzero abelian tangent `t` contains an algebraic vector on which
  `μ₁ = Σ a₁(j) z_j` or `μ₂` does not vanish (the uniform subgroup condition; the `G_a²` part is automatic).
  Logarithms go through the additive subgroup `lamLogF` of `Lam` (addition law, `Bridge.logE_add`, curve by curve).
* `uniform_SE`: the condition for the slot forms of Theorem SE (`aSE1 γ`, `aSE2 γ γ'`) when `E_L`, `E_{L'}` are not
  isogenous. Abelian tangents are `ℚ̄`-rational and split along the two curve types (`lean_lsg`:
  `K5d.abTan_rat_nonIsog`, `K5d.mul_mem_of_blockConst`); a nonzero lattice vector `z ∈ t` gives lattice vectors
  `z_E, z_{E'} ∈ t` on the two blocks, and `μ₁(z_E) = μ₂(z_E) = μ₂(z_{E'}) = 0` forces `z = 0` by the `k`-independence of
  `γ` and the `k'`-independence of `γ'` (`b_kindep`).
* `thm11KappaSE_of_nonIsog`: `Thm11KappaSE L L'` from `LSG.W88.hypStd_of_pair` (`lean_lsg` 6ebc17f).
* `transcendental_div_of_nonIsog`: for non-isogenous curves with algebraic invariants, `ω'/ω ∉ ℚ̄` for nonzero periods
  `ω, ω'` (the part of Lemma SE0 that Theorem SE uses). Proof: W88 §5d on `E × E'` (`gmStd 0 0 ![E, E']`) with
  `V = W = ℂ(1, β)` and `Y = ℚ(ω, ω')` (`m = 1 > 0 = (…)·(d − 1 − t)`): `V` would contain the tangent space of a nonzero
  abelian subvariety, which splits (`mul_mem_of_blockConst`), impossible on the graph of `z ↦ βz` with `β ≠ 0`.
* `thmSE_of_nonIsog`: **Theorem SE (SE) for two non-isogenous CM lattices**, with no form of W88 assumed;
  `thmSE_varpi_omegaRho`: the instance `E = E_i`, `E' = E_ρ`, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen CM4E.AbVar LSG.W88

namespace CM4E.Bridge

variable {d0 d1 m : ℕ}

/-- The coordinate isomorphism `T(G_a² × E₁ × ⋯ × E_m) = ℂ^m × ℂ² ≅ ℂ² × ℂ⁰ × ℂ^m`. -/
noncomputable def phiFX (m : ℕ) : TX (Fin m → ℂ) ≃ₗ[ℂ] Tan 2 0 m where
  toFun v := (![v.2.1, v.2.2], 0, v.1)
  invFun w := (w.2.2, w.1 0, w.1 1)
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
    · exact Subsingleton.elim _ _
    · simp

lemma phiFX_apply (v : TX (Fin m → ℂ)) : phiFX m v = (![v.2.1, v.2.2], 0, v.1) := rfl

/-- The logarithms whose `E_j`-coordinates are elliptic logarithms of algebraic points of `E_j` (all `g₂` algebraic):
an additive subgroup of `Lam`. -/
def lamLogF (Ls : Fin m → PeriodPair) (hg₂ : ∀ j, IsAlgebraic ℚ (Ls j).g₂) : AddSubgroup (Tan d0 d1 m) where
  carrier := {p | AlgVec p.1 ∧ (∀ i, IsAlgebraic ℚ (Complex.exp (p.2.1 i))) ∧ ∀ j, LogE (Ls j) (p.2.2 j)}
  add_mem' {p q} hp hq := by
    refine ⟨fun i => (hp.1 i).add (hq.1 i), fun i => ?_, fun j => logE_add (Ls j) (hg₂ j) (hp.2.2 j) (hq.2.2 j)⟩
    show IsAlgebraic ℚ (Complex.exp (p.2.1 i + q.2.1 i))
    rw [Complex.exp_add]; exact (hp.2.1 i).mul (hq.2.1 i)
  zero_mem' := ⟨fun _ => isAlgebraic_zero, fun _ => by simpa using isAlgebraic_one,
    fun j => Or.inl (Ls j).lattice.zero_mem⟩
  neg_mem' {p} hp := by
    refine ⟨fun i => (hp.1 i).neg, fun i => ?_, fun j => logE_neg (Ls j) (hp.2.2 j)⟩
    show IsAlgebraic ℚ (Complex.exp (-p.2.1 i))
    rw [Complex.exp_neg]; exact (hp.2.1 i).inv

lemma lamLogF_le_Lam (Ls : Fin m → PeriodPair) (hg₂ : ∀ j, IsAlgebraic ℚ (Ls j).g₂) :
    ((lamLogF (d0 := d0) (d1 := d1) Ls hg₂ : Set (Tan d0 d1 m))) ⊆ Lam Ls :=
  fun _ hp => ⟨hp.1, hp.2.1, fun j => (hp.2.2 j).imp id fun h => h.1⟩

/-- **The model `gmES` from the standard model `gmStd 2 0 Ls`**, given the uniform subgroup condition on abelian
tangents. -/
theorem hyperplaneKappa_gmES (Ls : Fin m → PeriodPair) (hg₂ : ∀ j, IsAlgebraic ℚ (Ls j).g₂)
    (a₁ a₂ : Fin m → ℂ) (hS : HyperplaneKappa (gmStd 2 0 Ls))
    (huni : ∀ t : Submodule ℂ (Fin m → ℂ), IsAbelianTangent Ls t → t ≠ ⊥ →
      ∃ z ∈ t, (∀ j, IsAlgebraic ℚ (z j)) ∧ (dotL a₁ z ≠ 0 ∨ dotL a₂ z ≠ 0)) :
    HyperplaneKappa (gmES Ls a₁ a₂) := by
  refine hyperplaneKappa_transport (gmES Ls a₁ a₂) (gmStd 2 0 Ls) (phiFX m) ?_ ?_ ?_ ?_ ?_ hS
  · -- algebraic vectors
    rintro v ⟨h1, h2, h3⟩
    refine ⟨fun i => ?_, fun i => i.elim0, h1⟩
    fin_cases i
    exacts [h2, h3]
  · -- logarithms
    intro v hv
    obtain ⟨D, hD, hDv⟩ := exists_nsmul_mem_closure _ hv
    refine ⟨D, hD, lamLogF_le_Lam Ls hg₂ ?_⟩
    have hle : AddSubgroup.closure (lamES Ls) ≤
        (lamLogF (d0 := 2) (d1 := 0) Ls hg₂).comap (phiFX m).toLinearMap.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro g (⟨j, w, hw, rfl⟩ | ⟨c₁, c₂, h1, h2, rfl⟩)
      · show phiFX m (genE j w) ∈ lamLogF _ hg₂
        refine ⟨fun i => ?_, fun i => i.elim0, fun j' => ?_⟩
        · fin_cases i <;> simp [phiFX_apply, genE, isAlgebraic_zero]
        · show LogE (Ls j') ((Pi.single j w : Fin m → ℂ) j')
          by_cases h : j' = j
          · subst h; simpa using hw
          · simp only [Pi.single_apply, h, ite_false]; exact Or.inl (Ls j').lattice.zero_mem
      · show phiFX m (((0 : Fin m → ℂ), c₁, c₂) : TX (Fin m → ℂ)) ∈ lamLogF _ hg₂
        refine ⟨fun i => ?_, fun i => i.elim0, fun j' => ?_⟩
        · fin_cases i
          exacts [h1, h2]
        · show LogE (Ls j') ((0 : Fin m → ℂ) j')
          exact Or.inl (Ls j').lattice.zero_mem
    exact hle hDv
  · -- periods
    intro v hv
    have hle : Submodule.span ℚ (perES Ls) ≤
        (Submodule.span ℚ (Per (d0 := 2) (d1 := 0) Ls : Set (Tan 2 0 m))).comap (ratMap (phiFX m)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, w, hw, rfl⟩
      apply Submodule.subset_span
      rw [ratMap_apply, phiFX_apply]
      refine ⟨by funext i; fin_cases i <;> simp [genE], fun i => i.elim0, fun j' => ?_⟩
      show (Pi.single j w : Fin m → ℂ) j' ∈ (Ls j').lattice
      by_cases h : j' = j
      · subst h; simpa using hw
      · simp only [Pi.single_apply, h, ite_false]; exact (Ls j').lattice.zero_mem
    exact hle hv
  · -- subgroups (uniform condition)
    rintro S ⟨H, rfl⟩ hne
    right
    by_cases h0 : H.h0 = ⊥
    · have ht : H.t ≠ ⊥ := by
        intro ht; apply hne
        rw [SubgroupData.tan, h0, ht, show torusLie H.U = ⊥ from Subsingleton.elim _ _]
        simp
      obtain ⟨z, hzt, hzalg, hz⟩ := huni H.t H.t_ab ht
      refine ⟨((z, 0, 0) : TX (Fin m → ℂ)), ?_, ⟨hzalg, isAlgebraic_zero, isAlgebraic_zero⟩, ?_⟩
      · show phiFX m (z, 0, 0) ∈ H.tan
        rw [phiFX_apply]
        refine ⟨?_, (torusLie H.U).zero_mem, hzt⟩
        have : (![(0 : ℂ), 0] : Fin 2 → ℂ) = 0 := by funext i; fin_cases i <;> rfl
        simp only [this]
        exact H.h0.zero_mem
      · rw [PsiX_apply]
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [add_zero, Prod.fst_zero, Prod.snd_zero] at h1 h2
        rcases hz with hz | hz
        exacts [hz h1, hz h2]
    · -- the `G_a` part is nonzero: an algebraic vector
      obtain ⟨a, ha, ha0⟩ : ∃ a ∈ H.h0, AlgVec a ∧ a ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply h0
        rw [H.h0_rat, Submodule.span_eq_bot]
        rintro x ⟨hx, hxa⟩
        exact hcon x hx hxa
      refine ⟨(((0 : Fin m → ℂ), a 0, a 1) : TX (Fin m → ℂ)), ?_,
        ⟨fun _ => isAlgebraic_zero, ha0.1 0, ha0.1 1⟩, ?_⟩
      · show phiFX m _ ∈ H.tan
        rw [phiFX_apply]
        refine ⟨?_, (torusLie H.U).zero_mem, H.t.zero_mem⟩
        have : (![(a 0), (a 1)] : Fin 2 → ℂ) = a := by funext i; fin_cases i <;> rfl
        simpa [this] using ha
      · rw [PsiX_apply]
        intro h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [map_zero, zero_add, Prod.fst_zero, Prod.snd_zero] at h1 h2
        apply ha0.2
        funext i; fin_cases i
        · exact h1
        · exact h2
  · -- the count
    show 0 + 2 * m ≤ 0 + 2 * finrank ℂ (Fin m → ℂ)
    simp

/-! ## The uniform subgroup condition for Theorem SE -/

/-- A nonzero abelian tangent contains a nonzero lattice vector. -/
lemma exists_lattice_ne_zero {Ls : Fin m → PeriodPair} {t : Submodule ℂ (Fin m → ℂ)}
    (hab : IsAbelianTangent Ls t) (ht : t ≠ ⊥) : ∃ z ∈ t, (∀ j, z j ∈ (Ls j).lattice) ∧ z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply ht
  have hspan : Submodule.span ℝ {z : Fin m → ℂ | z ∈ t ∧ ∀ j, z j ∈ (Ls j).lattice} = ⊥ := by
    rw [Submodule.span_eq_bot]
    exact fun z hz => hcon z hz.1 hz.2
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ (t.restrictScalars ℝ : Submodule ℝ (Fin m → ℂ)) := hx
  rw [hab, hspan] at this
  exact this

/-- Lattice vectors `y ∈ Λ_L^r` with `Σ γ_i y_i = 0` vanish (`γ` independent over `k = ℚ(α)`). -/
lemma lattice_eq_zero {L : CMLattice} {r : ℕ} {γ : Fin r → ℂ} (hb : IsAdaptedFieldBasis L.α γ) (y : Fin r → ℂ)
    (hy : ∀ i, y i ∈ L.pp.lattice) (h : ∑ i, γ i * y i = 0) : y = 0 := by
  choose mm nn hmn using fun i => PeriodPair.mem_lattice.mp (hy i)
  have hω := L.ω_ne_zero
  have hyj : ∀ i, y i = L.ω * (((mm i : ℚ) : ℂ) + ((nn i : ℚ) : ℂ) * L.α) := by
    intro i; rw [← hmn i, L.hω₁, L.hω₂]; push_cast; ring
  have h' : ∑ i, γ i * (((mm i : ℚ) : ℂ) + ((nn i : ℚ) : ℂ) * L.α) = 0 := by
    have : ∑ i, γ i * y i = L.ω * ∑ i, γ i * (((mm i : ℚ) : ℂ) + ((nn i : ℚ) : ℂ) * L.α) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hyj i]; ring
    rw [this] at h
    exact (mul_eq_zero.mp h).resolve_left hω
  obtain ⟨hu, hv⟩ := b_kindep hb (fun i => (mm i : ℚ)) (fun i => (nn i : ℚ)) h'
  funext i
  have hm : (mm i : ℚ) = 0 := congrFun hu i
  have hn : (nn i : ℚ) = 0 := congrFun hv i
  rw [hyj i, hm, hn]
  simp

lemma ne_of_nonIsog {P P' : PeriodPair} (h : NonIsog P P') : P ≠ P' := by
  rintro rfl
  exact h 1 one_ne_zero fun ω hω => by rw [one_mul]; exact hω

/-- **The uniform subgroup condition for Theorem SE** (`E_L`, `E_{L'}` not isogenous). -/
theorem uniform_SE (L L' : CMLattice) (hni : NonIsog L.pp L'.pp) (hni' : NonIsog L'.pp L.pp) {r : ℕ}
    {γ γ' : Fin r → ℂ} (hb : IsAdaptedFieldBasis L.α γ) (hb' : IsAdaptedFieldBasis L'.α γ')
    (t : Submodule ℂ (Fin (r + r + r) → ℂ)) (hab : IsAbelianTangent (lsSE L.pp L'.pp r) t) (ht : t ≠ ⊥) :
    ∃ z ∈ t, (∀ j, IsAlgebraic ℚ (z j)) ∧ (dotL (aSE1 γ) z ≠ 0 ∨ dotL (aSE2 γ γ') z ≠ 0) := by
  classical
  have hne := ne_of_nonIsog hni
  have hniall := hni_of_pair (lsSE_cases (r := r) L.pp L'.pp) hni hni'
  by_contra hcon
  push Not at hcon
  have hker : ∀ z ∈ t, dotL (aSE1 γ) z = 0 ∧ dotL (aSE2 γ γ') z = 0 := by
    have hrat := K5d.abTan_rat_nonIsog _ hniall t hab
    have hle : t ≤ LinearMap.ker (dotL (aSE1 γ)) ⊓ LinearMap.ker (dotL (aSE2 γ γ')) := by
      rw [hrat, Submodule.span_le]
      rintro z ⟨hz, hza⟩
      exact hcon z hz hza
    intro z hz
    exact hle hz
  obtain ⟨z, hzt, hzl, hz0⟩ := exists_lattice_ne_zero hab ht
  set D : Fin (r + r + r) → ℂ := fun j => if lsSE L.pp L'.pp r j = L.pp then 1 else 0 with hDdef
  have hD : ∀ j k, lsSE L.pp L'.pp r j = lsSE L.pp L'.pp r k → D j = D k := fun j k h => by
    simp only [hDdef, h]
  have hzE : D * z ∈ t := K5d.mul_mem_of_blockConst hniall hab hD hzt
  have hzR : z - D * z ∈ t := sub_mem hzt hzE
  have D1 : ∀ i, D (b1 i) = 1 := fun i => by simp [hDdef]
  have D2 : ∀ i, D (b2 i) = 1 := fun i => by simp [hDdef]
  have D3 : ∀ i, D (b3 i) = 0 := fun i => by simp [hDdef, Ne.symm hne]
  obtain ⟨e1, e2⟩ := hker _ hzE
  obtain ⟨-, e3⟩ := hker _ hzR
  rw [dotL_apply, sum_blocks] at e1 e2 e3
  simp only [Pi.mul_apply, Pi.sub_apply, D1, D2, D3, aSE1_b1, aSE1_b2, aSE1_b3, aSE2_b1, aSE2_b2, aSE2_b3,
    one_mul, zero_mul, mul_zero, sub_self, sub_zero, Finset.sum_const_zero, add_zero, zero_add] at e1 e2 e3
  have z1 := lattice_eq_zero hb (fun i => z (b1 i)) (fun i => by simpa using hzl (b1 i)) e1
  have z2 := lattice_eq_zero hb (fun i => z (b2 i)) (fun i => by simpa using hzl (b2 i)) e2
  have z3 := lattice_eq_zero hb' (fun i => z (b3 i)) (fun i => by simpa using hzl (b3 i)) e3
  apply hz0
  funext j
  exact forall_blocks (P := fun j => z j = 0) (fun i => congrFun z1 i) (fun i => congrFun z2 i)
    (fun i => congrFun z3 i) j

/-- **`Thm11KappaSE` for non-isogenous CM curves** (from `lean_lsg`'s `hypStd_of_pair`). -/
theorem thm11KappaSE_of_nonIsog (L L' : CMLattice) : Thm11KappaSE L L' := by
  intro hni hni' hg₂ hg₃ hg₂' hg₃' r γ γ' hb hb'
  refine hyperplaneKappa_gmES (lsSE L.pp L'.pp r) (fun j => ?_) _ _ ?_ (uniform_SE L L' hni hni' hb hb')
  · rcases lsSE_cases L.pp L'.pp j with h | h <;> rw [h]
    exacts [hg₂, hg₂']
  · exact LSG.W88.hypStd_of_pair (lsSE L.pp L'.pp r) (lsSE_cases L.pp L'.pp) ⟨hg₂, hg₃⟩ ⟨hg₂', hg₃'⟩ hni hni' 2 0

/-! ## Lemma SE0 (the part used): `Ω'/Ω ∉ ℚ̄` -/

/-- **Periods of non-isogenous curves have transcendental ratio** (curves with algebraic invariants). -/
theorem transcendental_div_of_nonIsog (P P' : PeriodPair) (hg : IsAlgebraic ℚ P.g₂ ∧ IsAlgebraic ℚ P.g₃)
    (hg' : IsAlgebraic ℚ P'.g₂ ∧ IsAlgebraic ℚ P'.g₃) (hni : NonIsog P P') (hni' : NonIsog P' P) {ω ω' : ℂ}
    (hω : ω ∈ P.lattice) (hω0 : ω ≠ 0) (hω' : ω' ∈ P'.lattice) (hω'0 : ω' ≠ 0) :
    Transcendental ℚ (ω' / ω) := by
  intro hβ
  set β := ω' / ω with hβdef
  have hβ0 : β ≠ 0 := div_ne_zero hω'0 hω0
  have hne := ne_of_nonIsog hni
  set Ls : Fin 2 → PeriodPair := ![P, P'] with hLsdef
  have hLs : ∀ j, Ls j = P ∨ Ls j = P' := by intro j; fin_cases j <;> simp [Ls]
  have hS : HyperplaneKappa (gmStd 0 0 Ls) := LSG.W88.hypStd_of_pair Ls hLs hg hg' hni hni' 0 0
  set v₀ : Tan 0 0 2 := (0, 0, ![1, β]) with hv₀def
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have := congrArg (fun x : Tan 0 0 2 => x.2.2 0) h
    simp [v₀] at this
  set V := Submodule.span ℂ {v₀} with hVdef
  have hfV : finrank ℂ V = 1 := finrank_span_singleton hv₀
  have hfT : finrank ℂ (Tan 0 0 2) = 2 := by simp [Tan, Module.finrank_prod]
  set y : Fin 1 → Tan 0 0 2 := fun _ => (0, 0, ![ω, ω']) with hydef
  have hy0 : y 0 ≠ 0 := by
    intro h
    have := congrArg (fun x : Tan 0 0 2 => x.2.2 0) h
    simp [y] at this
    exact hω0 this
  have hy : ∀ i, y i = ω • v₀ := by
    intro i
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_)
    funext j; fin_cases j
    · simp [y, v₀]
    · simp [y, v₀, hβdef]; field_simp
  have hyV : ∀ i, y i ∈ V := fun i => by
    rw [hy i]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hyL : ∀ i, y i ∈ (gmStd 0 0 Ls).lam := fun i =>
    ⟨fun k => k.elim0, fun k => k.elim0, fun j => Or.inl (by fin_cases j <;> simpa [y, Ls])⟩
  have hfy : finrank ℚ (Submodule.span ℚ (Set.range y)) = 1 := by
    have : Set.range y = {y 0} := by
      ext x; simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨i, hi⟩ => by rw [← hi, Subsingleton.elim i 0], fun h => ⟨0, h.symm⟩⟩
    rw [this]
    exact finrank_span_singleton hy0
  obtain ⟨S, ⟨H, rfl⟩, hne', hle⟩ := hS V V 1 y (by rw [hfV, hfT]) le_rfl
    ⟨{v₀}, by
      rintro v rfl
      refine ⟨fun k => k.elim0, fun k => k.elim0, fun j => ?_⟩
      fin_cases j
      · simpa [v₀] using isAlgebraic_one
      · simpa [v₀] using hβ, rfl⟩
    (fun i => ⟨hyV i, hyL i⟩)
    (by
      rw [hfy, hfT, hfV]
      show ((1 : ℕ) : ℤ) > ((0 : ℕ) + 2 * ((2 : ℕ) : ℤ) - _) * (((2 : ℕ) : ℤ) - 1 - ((1 : ℕ) : ℤ))
      simp)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
  have hxt : x.2.2 ∈ H.t := hx.2.2
  set D : Fin 2 → ℂ := ![1, 0] with hDdef
  have hD : ∀ j k, Ls j = Ls k → D j = D k := by
    intro j k h
    fin_cases j <;> fin_cases k
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl
  have hDt : D * x.2.2 ∈ H.t := K5d.mul_mem_of_blockConst (hni_of_pair hLs hni hni') H.t_ab hD hxt
  have hDV : (((0 : Fin 0 → ℂ), (0 : Fin 0 → ℂ), D * x.2.2) : Tan 0 0 2) ∈ V :=
    hle ⟨H.h0.zero_mem, (torusLie H.U).zero_mem, hDt⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hDV
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp (hle hx)
  have e0 := congrArg (fun z : Tan 0 0 2 => z.2.2 0) ha
  have e1 := congrArg (fun z : Tan 0 0 2 => z.2.2 1) ha
  have f0 := congrArg (fun z : Tan 0 0 2 => z.2.2 0) ha'
  have f1 := congrArg (fun z : Tan 0 0 2 => z.2.2 1) ha'
  simp [v₀, D] at e0 e1 f0 f1
  have ha0 : a = 0 := by
    rcases e1 with h | h
    · exact h
    · exact absurd h hβ0
  apply hx0
  refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_)
  funext j; fin_cases j
  · show x.2.2 0 = 0
    rw [← e0, ha0]
  · show x.2.2 1 = 0
    rw [← f1, f0, ← e0, ha0, zero_mul]

/-! ## Theorem SE -/

/-- **Theorem SE, part (SE), for two non-isogenous CM lattices** (paper addition seed 2, Theorem `thm:SE` (1)), with no
form of W88 assumed: if `E_L`, `E_{L'}` have algebraic invariants, are not isogenous, and complex multiplication acts on
their elliptic logarithms of algebraic points, then for `c ∈ ℚ̄ˣ`, `t = c·L'.ω/L.ω` and `u₁, u₂ ∈ 𝓛̃_{E_L}` with
`L.ω, u₁, u₂` linearly independent over `ℚ̄`, the numbers `tu₁, tu₂` are not both in
`ℚ̄ + ℚ̄𝓛_{E_L} + ℚ̄𝓛_{E_{L'}}`. -/
theorem thmSE_of_nonIsog (L L' : CMLattice) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hg₂' : IsAlgebraic ℚ L'.pp.g₂) (hg₃' : IsAlgebraic ℚ L'.pp.g₃) (hni : NonIsog L.pp L'.pp)
    (hni' : NonIsog L'.pp L.pp) (hCM : CMMulLogE L) (hCM' : CMMulLogE L') (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) (u₁ u₂ : ℂ) (hu₁ : u₁ ∈ LtildeE L.pp) (hu₂ : u₂ ∈ LtildeE L.pp)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * L.ω + a₁ * u₁ + a₂ * u₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * L'.ω / L.ω * u₁ ∈ LtildeEE L.pp L'.pp ∧ c * L'.ω / L.ω * u₂ ∈ LtildeEE L.pp L'.pp) := by
  rintro ⟨h1, h2⟩
  refine thmSE L L' (thm11KappaSE_of_nonIsog L L') hni hni' hg₂ hg₃ hg₂' hg₃' hCM hCM'
    (transcendental_div_of_nonIsog L.pp L'.pp ⟨hg₂, hg₃⟩ ⟨hg₂', hg₃'⟩ hni hni'
      (L.hω₁ ▸ L.pp.ω₁_mem_lattice) L.ω_ne_zero (L'.hω₁ ▸ L'.pp.ω₁_mem_lattice) L'.ω_ne_zero)
    c hc hc0 ![u₁, u₂] (fun j => by fin_cases j; exacts [hu₁, hu₂]) (by simpa using hind)
    (fun j => by fin_cases j; exacts [h1, h2])

lemma nonIsog_latI_latRho : NonIsog latI.pp latRho.pp :=
  LSG.W88.nonIsog_I_rho rfl (by linear_combination MX.rho_sq) rfl

lemma nonIsog_latRho_latI : NonIsog latRho.pp latI.pp :=
  LSG.W88.nonIsog_rho_I (by linear_combination MX.rho_sq) rfl rfl

/-- **`Ω_ρ/ϖ` is transcendental**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄` (the hypothesis `hM` of Theorems MX, MX′). -/
theorem transcendental_omegaRho_div_varpi_of (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) :
    Transcendental ℚ ((omegaRho : ℂ) / varpi) :=
  transcendental_div_of_nonIsog latI.pp latRho.pp ⟨Final.hg₂, g₃_lemniscatic_isAlgebraic⟩ ⟨Final.hg₂', hg₃'⟩
    nonIsog_latI_latRho nonIsog_latRho_latI lemniscatic.ω₁_mem_lattice latI.ω_ne_zero
    MX.equianharmonic.ω₁_mem_lattice latRho.ω_ne_zero

/-- **Theorem SE (SE) for `E = E_i` (`ϖℤ[i]`) and `E' = E_ρ` (`Ω_ρℤ[ρ]`)**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`: for
`c ∈ ℚ̄ˣ`, `t = cΩ_ρ/ϖ` and `u₁, u₂ ∈ 𝓛̃_{E_i}` with `ϖ, u₁, u₂` linearly independent over `ℚ̄`, the numbers `tu₁, tu₂` are
not both in `ℚ̄ + ℚ̄𝓛_{E_i} + ℚ̄𝓛_{E_ρ}`. -/
theorem thmSE_varpi_omegaRho (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) (u₁ u₂ : ℂ) (hu₁ : u₁ ∈ LtildeE lemniscatic) (hu₂ : u₂ ∈ LtildeE lemniscatic)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * varpi + a₁ * u₁ + a₂ * u₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * omegaRho / varpi * u₁ ∈ LtildeEE lemniscatic MX.equianharmonic ∧
      c * omegaRho / varpi * u₂ ∈ LtildeEE lemniscatic MX.equianharmonic) :=
  thmSE_of_nonIsog latI latRho Final.hg₂ g₃_lemniscatic_isAlgebraic Final.hg₂' hg₃' nonIsog_latI_latRho
    nonIsog_latRho_latI cmMulLogE_latI cmMulLogE_latRho c hc hc0 u₁ u₂ hu₁ hu₂ hind

end CM4E.Bridge
