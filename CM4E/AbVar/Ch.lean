/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.Basis

/-!
# (Ch): Dedekind independence of characters, and a common adapted basis

Paper, §`sec:setting`, (Ch): for a CM field `F = ℚ(α)` with distinct embeddings `σ_s` (`s < g`), the vectors
`(σ_s(x))_s`, `x ∈ F`, span `K^g` over any field `K ⊇ σ_s(F)`. With `κ_s = σ_s(α)` (distinct roots of the minimal
polynomial of `α`) and the `ℚ`-basis `1, α, …, α^{d−1}` of `F` this says: the rows `(κ_s^e)_{e<d}` are `K`-linearly
independent, so every `t ∈ K^g` is `Σ_e c_e (κ_s^e)_s` with `c ∈ K^d`.

* `ch_rows_indep`: the rows are linearly independent over `ℂ`. Proof: the characters `e ↦ κ_s^e` of the monoid
  `Multiplicative ℕ` are distinct, hence linearly independent (`linearIndependent_monoidHom`, Dedekind/Artin); and a
  relation for `e < d` propagates to all `e` because every `κ_s` is a root of the same minimal polynomial.
* `ch_span`: the `K`-version (prescribing slot coordinates with coefficients in `K`).
* `exists_adapted_common`: for finitely many algebraic `α_j` and a finite set `S` of algebraic numbers there is one
  number field `K ⊇ S ∪ {α_j}` and, for each `j`, a `ℚ(α_j)`-basis `b_j` of `K` (`IsAdaptedBasisD`, with
  `KspanD (α j) d_j (b j) = K`).
-/

open Polynomial

namespace CM4E.AbVar

/-- A relation `Σ_s c_s κ_s^e = 0` for `e < d` holds for every exponent `e`. -/
lemma ch_all_pow {α : ℂ} (hα : IsAlgebraic ℚ α) {g : ℕ} (κ : Fin g → ℂ)
    (hroot : ∀ s, aeval (κ s) (minpoly ℚ α) = 0) (c : Fin g → ℂ)
    (hc : ∀ e < (minpoly ℚ α).natDegree, ∑ s, c s * κ s ^ e = 0) (n : ℕ) :
    ∑ s, c s * κ s ^ n = 0 := by
  set p := minpoly ℚ α
  have hmon : p.Monic := minpoly.monic hα.isIntegral
  have hpos : 0 < p.natDegree := minpoly.natDegree_pos hα.isIntegral
  have hne : p ≠ 1 := fun h => by simp [h] at hpos
  set q : ℚ[X] := X ^ n %ₘ p
  have hq : q.natDegree < p.natDegree := natDegree_modByMonic_lt _ hmon hne
  have hκ : ∀ s, κ s ^ n = ∑ i ∈ Finset.range p.natDegree, q.coeff i • κ s ^ i := by
    intro s
    rw [← aeval_eq_sum_range' hq]
    have h := congrArg (aeval (κ s)) (modByMonic_add_div (X ^ n : ℚ[X]) p)
    rw [map_add, map_mul, hroot s, zero_mul, add_zero, map_pow, aeval_X] at h
    exact h.symm
  simp_rw [hκ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have := hc i (Finset.mem_range.mp hi)
  calc ∑ s, c s * (q.coeff i • κ s ^ i) = q.coeff i • ∑ s, c s * κ s ^ i := by
        rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [mul_smul_comm]
    _ = 0 := by rw [this, smul_zero]

/-- **(Ch), over `ℂ`.** Distinct roots `κ_s` of the minimal polynomial of `α` give `ℂ`-linearly independent rows
`(κ_s^e)_{e < d}`. -/
theorem ch_rows_indep {α : ℂ} (hα : IsAlgebraic ℚ α) {g : ℕ} (κ : Fin g → ℂ) (hκ : Function.Injective κ)
    (hroot : ∀ s, aeval (κ s) (minpoly ℚ α) = 0) (c : Fin g → ℂ)
    (hc : ∀ e < (minpoly ℚ α).natDegree, ∑ s, c s * κ s ^ e = 0) : c = 0 := by
  have hall := ch_all_pow hα κ hroot c hc
  have hli : LinearIndependent ℂ (fun s => ((powersHom ℂ (κ s) : Multiplicative ℕ →* ℂ) :
      Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp _
      ((powersHom ℂ).injective.comp hκ)
  rw [Fintype.linearIndependent_iff] at hli
  funext s
  refine hli c ?_ s
  funext e
  simp [hall]

/-- **(Ch), over a subfield `K` containing the `κ_s`**: every `t ∈ K^g` is `Σ_e c_e (κ_s^e)_s` with `c_e ∈ K`. -/
theorem ch_span (K : Subfield ℂ) {α : ℂ} (hα : IsAlgebraic ℚ α) {g : ℕ} (κ : Fin g → ℂ)
    (hκ : Function.Injective κ) (hroot : ∀ s, aeval (κ s) (minpoly ℚ α) = 0) (hκK : ∀ s, κ s ∈ K)
    (t : Fin g → ℂ) (ht : ∀ s, t s ∈ K) :
    ∃ c : Fin (minpoly ℚ α).natDegree → ℂ, (∀ e, c e ∈ K) ∧ ∀ s, ∑ e, c e * κ s ^ (e : ℕ) = t s := by
  set d := (minpoly ℚ α).natDegree
  let k : Fin g → K := fun s => ⟨κ s, hκK s⟩
  let φ : (Fin d → K) →ₗ[K] (Fin g → K) :=
    { toFun := fun c s => ∑ e, c e * k s ^ (e : ℕ)
      map_add' := fun c c' => by
        funext s; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext s; simp [Finset.mul_sum, mul_assoc] }
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := (LinearMap.range φ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    set c' : Fin g → K := fun s => f (fun j => if s = j then 1 else 0)
    have hfe : ∀ y, f y = ∑ s, y s * c' s := fun y => by
      rw [LinearMap.pi_apply_eq_sum_univ]; rfl
    have hrel : ∀ e < d, ∑ s, ((c' s : K) : ℂ) * κ s ^ e = 0 := by
      intro e he
      have hmem : φ (fun e' => if (e' : ℕ) = e then 1 else 0) ∈ LinearMap.ker f :=
        hle (LinearMap.mem_range_self φ _)
      rw [LinearMap.mem_ker, hfe] at hmem
      have hφ : ∀ s, φ (fun e' => if (e' : ℕ) = e then 1 else 0) s = k s ^ e := by
        intro s
        change ∑ e' : Fin d, (if (e' : ℕ) = e then (1 : K) else 0) * k s ^ (e' : ℕ) = _
        rw [Finset.sum_eq_single (⟨e, he⟩ : Fin d)]
        · simp
        · intro b _ hb
          have : (b : ℕ) ≠ e := fun h => hb (Fin.ext h)
          simp [this]
        · simp
      simp_rw [hφ] at hmem
      have := congrArg (fun x : K => (x : ℂ)) hmem
      simpa [k, mul_comm] using this
    have hc0 := ch_rows_indep hα κ hκ hroot (fun s => (c' s : ℂ)) hrel
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hfe, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    have : (c' s : ℂ) = 0 := congrFun hc0 s
    rw [show c' s = 0 from Subtype.ext this, mul_zero]
  obtain ⟨c, hc⟩ := hsurj (fun s => ⟨t s, ht s⟩)
  refine ⟨fun e => (c e : ℂ), fun e => (c e).2, fun s => ?_⟩
  have := congrArg (fun x : K => (x : ℂ)) (congrFun hc s)
  simpa [φ, k] using this

open IntermediateField in
/-- Variant of `exists_adapted_basisD` with `K = ℚ(α, T)` identified explicitly. -/
lemma exists_adapted_basisD_adjoin (α : ℂ) (hα : IsAlgebraic ℚ α) (T : Set ℂ) (hTf : T.Finite)
    (hTa : ∀ s ∈ T, IsAlgebraic ℚ s) :
    ∃ r : ℕ, ∃ b : Fin r → ℂ, IsAdaptedBasisD α (minpoly ℚ α).natDegree b ∧
      ∀ x, x ∈ KspanD α (minpoly ℚ α).natDegree b ↔ x ∈ IntermediateField.adjoin ℚ ({α} ∪ T) := by
  have hαi : IsIntegral ℚ α := hα.isIntegral
  set d := (minpoly ℚ α).natDegree
  set pb := adjoin.powerBasis hαi
  have hdim : pb.dim = d := by rw [adjoin.powerBasis_dim]
  set bk : Module.Basis (Fin d) ℚ ℚ⟮α⟯ := pb.basis.reindex (finCongr hdim)
  have hbk : ∀ e : Fin d, ((bk e : ℚ⟮α⟯) : ℂ) = α ^ (e : ℕ) := by
    intro e
    simp [bk, Module.Basis.reindex_apply, PowerBasis.coe_basis, pb, adjoin.powerBasis_gen]
  have : FiniteDimensional ℚ ℚ⟮α⟯ := adjoin.finiteDimensional hαi
  set K : IntermediateField ℚ⟮α⟯ ℂ := IntermediateField.adjoin ℚ⟮α⟯ T
  have hT : ∀ x ∈ T, IsIntegral ℚ⟮α⟯ x := fun x hx => (hTa x hx).isIntegral.tower_top
  have : Finite T := hTf.to_subtype
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
  have hKeq : ∀ x, x ∈ K ↔ x ∈ IntermediateField.adjoin ℚ ({α} ∪ T) := by
    intro x
    rw [← adjoin_adjoin_left]
    rfl
  have halg : ∀ x ∈ K, IsAlgebraic ℚ x := by
    intro x hx
    have : Module.Finite ℚ K := Module.Finite.trans ℚ⟮α⟯ K
    have : IsIntegral ℚ (⟨x, hx⟩ : K) := IsIntegral.of_finite ℚ _
    exact (this.map (K.val.restrictScalars ℚ)).isAlgebraic
  refine ⟨r, b, ⟨?_, ?_, ?_, ?_, ?_⟩, fun x => (hspan x).trans (hKeq x)⟩
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

open IntermediateField in
/-- **A common adapted basis**: one number field `K` containing `S` and all `α_j`, with a `ℚ(α_j)`-basis `b_j` of `K`
for every `j`. -/
theorem exists_adapted_common {m : ℕ} (α : Fin m → ℂ) (hα : ∀ j, IsAlgebraic ℚ (α j)) (S : Finset ℂ)
    (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ (K : Submodule ℚ ℂ) (r : Fin m → ℕ) (b : (j : Fin m) → Fin (r j) → ℂ),
      (∀ j, IsAdaptedBasisD (α j) (minpoly ℚ (α j)).natDegree (b j)) ∧
      (∀ j, KspanD (α j) (minpoly ℚ (α j)).natDegree (b j) = K) ∧ (∀ s ∈ S, s ∈ K) ∧ (∀ j, α j ∈ K) := by
  set T : Set ℂ := (S : Set ℂ) ∪ Set.range α
  have hTf : T.Finite := S.finite_toSet.union (Set.finite_range α)
  have hTa : ∀ s ∈ T, IsAlgebraic ℚ s := by
    rintro s (hs | ⟨j, rfl⟩)
    · exact hS s hs
    · exact hα j
  have hex := fun j => exists_adapted_basisD_adjoin (α j) (hα j) T hTf hTa
  choose r b hb hmem using hex
  have hins : ∀ j, ({α j} ∪ T : Set ℂ) = T := fun j =>
    Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr (Or.inr ⟨j, rfl⟩))
  set L := IntermediateField.adjoin ℚ T
  refine ⟨L.toSubalgebra.toSubmodule, r, b, hb, fun j => ?_, fun s hs => ?_, fun j => ?_⟩
  · ext x
    rw [hmem j x, hins j]
    rfl
  · exact subset_adjoin ℚ T (Or.inl hs)
  · exact subset_adjoin ℚ T (Or.inr ⟨j, rfl⟩)

end CM4E.AbVar
