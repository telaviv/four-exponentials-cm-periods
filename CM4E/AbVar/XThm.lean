/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.XGen
import CM4E.AbVar.Ch
import CM4E.AbVar.X7

/-!
# Proposition 15 and Theorem X (paper [II], §`sec:X`), generic form

**Set-up** (`XSetup`). The isogeny classes among the slots are `AV : Fin m → CMAV`, each taken once; slot `j`
(`a, b, c, d = 0, 1, 2, 3`) is the eigen-coordinate `sl j` of `AV (cls j)`. The slots are pairwise distinct
(`Distinct`: two slots on one variety have different coordinates). `G = ∏_i A_i × G_a²` has tangent space `LieG`;
`Λ_K(A)` is the `K`-span of the logarithms `[α^e]ℓ` (`ℓ ∈ LA ∪ {γ}`; `lamK`), and
`Ψ(λ, q₁, q₂) = (z_a(λ) + z_d(λ) + q₁, z_c(λ) + z_b(λ) + q₂)`. With the first-kind relation (R) `P_aP_b = μP_cP_d`
(a hypothesis, as in the paper), `w = (P_a, βP_c)`, `w' = (P_d, βP_b/μ)` and `V = ℂw`:

* `propX15`: **Proposition 15**, `V ∩ Ψ(Λ_K(G)) = Kw + Kw'`, for a number field `K` containing the conjugates `κ`
  (the Galois closures), `μ` and `β`, with `[K : ℚ] ≥ 5`. `⊆` is `propXA_K` (W88 for the block group of
  `CM4E/AbVar/XGen.lean`); `⊇` (`w, w' ∈ Ψ(Ω_K(G))`) uses (Ch) (`ch_span`, Dedekind) to prescribe the slot coordinates
  of one element of `Ω_K(A_i)` for all slots on `A_i` at once.
* `thmXA`: **Theorem X**: data `v_j ∈ ℚ̄Λ(A_j)`, `q₁, q₂ ∈ ℚ̄` with `(z_a(v_a) + z_d(v_d) + q₁)·βP_c =
  (z_c(v_c) + z_b(v_b) + q₂)·P_a` force `q₁ = q₂ = 0` and `z_j(v_j) ∈ ℚ̄P_j`. As in the paper: (Ch) puts the data into
  one point of `Λ_K(G)` (slots on one variety may carry different logarithms), Proposition 15 applies, and Wüstholz's
  slot splitting (`WuestholzSplitXA`, named input) finishes.

The `[K : ℚ] ≥ 5` in `propX15` comes from the frame `gmFX`, which counts `G_a²` in `d₂` (the paper's count has no such
condition); `thmXA` chooses `K` itself and has no such hypothesis.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen Polynomial

namespace CM4E.AbVar

/-- The data of `A` are those of a simple CM abelian variety: the `κ_s` are distinct algebraic conjugates (roots of
one minimal polynomial), and `2g ≤ [F : ℚ]`. -/
structure CMAV.Good (A : CMAV) : Prop where
  alg : ∀ s, IsAlgebraic ℚ (A.κ s)
  inj : Function.Injective A.κ
  conj : ∀ s s', aeval (A.κ s) (minpoly ℚ (A.κ s')) = 0
  cm : ∀ s, 2 * A.g ≤ (minpoly ℚ (A.κ s)).natDegree

/-- `Λ_K(A)`: the `K`-span of the logarithms `[α^e]ℓ`, `ℓ ∈ LA ∪ {γ}`, in eigen-coordinates. -/
noncomputable def lamK (A : CMAV) (K : IntermediateField ℚ ℂ) : Submodule K (Fin A.g → ℂ) :=
  Submodule.span K {u | ∃ e : ℕ, ∃ ℓ ∈ insert A.P A.LA, u = fun s => A.κ s ^ e * ℓ s}

/-- The set-up of Theorem X: isogeny classes `AV i`, slot `j` = coordinate `sl j` of `AV (cls j)`. -/
structure XSetup where
  m : ℕ
  AV : Fin m → CMAV
  cls : Fin 4 → Fin m
  sl : (j : Fin 4) → Fin (AV (cls j)).g

namespace XSetup

variable (X : XSetup)

/-- Slot `j` as a first-kind slot. -/
def slot (j : Fin 4) : FKSlot := ⟨X.AV (X.cls j), X.sl j⟩

/-- The tangent space of `∏_i A_i`. -/
abbrev LieG := (i : Fin X.m) → Fin (X.AV i).g → ℂ

/-- The slot coordinate `z_j`. -/
def z (j : Fin 4) (l : X.LieG) : ℂ := l (X.cls j) (X.sl j)

/-- `Ψ(λ, q₁, q₂) = (z_a + z_d + q₁, z_c + z_b + q₂)`. -/
def Psi (l : X.LieG) (q₁ q₂ : ℂ) : ℂ × ℂ := (X.z 0 l + X.z 3 l + q₁, X.z 2 l + X.z 1 l + q₂)

/-- `Ψ(Λ_K(G))`, `G = ∏_i A_i × G_a²` (`Λ(G_a) = ℚ̄`). -/
def psiLamK (K : IntermediateField ℚ ℂ) : Set (ℂ × ℂ) :=
  {v | ∃ l : X.LieG, (∀ i, l i ∈ lamK (X.AV i) K) ∧ ∃ q₁ q₂ : ℂ, IsAlgebraic ℚ q₁ ∧ IsAlgebraic ℚ q₂ ∧
    v = X.Psi l q₁ q₂}

/-- The slots are pairwise distinct. -/
def Distinct : Prop := ∀ j j', j ≠ j' → X.cls j = X.cls j' → (X.sl j : ℕ) ≠ X.sl j'

/-- The slot period `P_j`. -/
def per (j : Fin 4) : ℂ := (X.slot j).per

end XSetup

/-- `ℚ̄ z_j(Λ(A_j))`: `ℚ̄`-combinations of slot coordinates of logarithms (and of `γ`). -/
def zQbar (S : FKSlot) : Set ℂ :=
  {x | ∃ (N : ℕ) (c : Fin N → ℂ) (ℓ : Fin N → Fin S.A.g → ℂ), (∀ k, IsAlgebraic ℚ (c k)) ∧
    (∀ k, ℓ k ∈ insert S.A.P S.A.LA) ∧ x = ∑ k, c k * ℓ k S.s}

/-- **Named input (Wüstholz 1989; slot splitting, paper [II] proof of Theorem X).** A relation
`x + x' + q = cP_a + c'P_d` (resp. with slots `c, b`) with `x ∈ ℚ̄z_a(Λ(A_a))`, `x' ∈ ℚ̄z_d(Λ(A_d))` and `q, c, c'`
algebraic splits slot by slot. -/
def WuestholzSplitXA (S : Fin 4 → FKSlot) : Prop :=
  (∀ x x' q c c' : ℂ, x ∈ zQbar (S 0) → x' ∈ zQbar (S 3) → IsAlgebraic ℚ q → IsAlgebraic ℚ c →
      IsAlgebraic ℚ c' → x + x' + q = c * (S 0).per + c' * (S 3).per →
        q = 0 ∧ x = c * (S 0).per ∧ x' = c' * (S 3).per) ∧
    (∀ x x' q c c' : ℂ, x ∈ zQbar (S 2) → x' ∈ zQbar (S 1) → IsAlgebraic ℚ q → IsAlgebraic ℚ c →
      IsAlgebraic ℚ c' → x + x' + q = c * (S 2).per + c' * (S 1).per →
        q = 0 ∧ x = c * (S 2).per ∧ x' = c' * (S 1).per)

/-! ## Number fields and adapted bases -/

lemma isAlgebraic_of_mem_field (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {x : ℂ} (hx : x ∈ K) :
    IsAlgebraic ℚ x := by
  have : IsIntegral ℚ (⟨x, hx⟩ : K) := IsIntegral.of_finite ℚ _
  exact (this.map (K.val.restrictScalars ℚ)).isAlgebraic

/-- For `α` in a number field `K`, a `ℚ(α)`-basis of `K`. -/
lemma exists_adapted_of_field (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {α : ℂ} (hαK : α ∈ K) :
    ∃ r : ℕ, ∃ b : Fin r → ℂ, IsAdaptedBasisD α (minpoly ℚ α).natDegree b ∧
      ∀ x, x ∈ KspanD α (minpoly ℚ α).natDegree b ↔ x ∈ K := by
  set B := Module.finBasis ℚ K
  set T : Set ℂ := Set.range (fun i => (B i : ℂ))
  have hTf : T.Finite := Set.finite_range _
  have hTK : T ⊆ K := by rintro _ ⟨i, rfl⟩; exact (B i).2
  obtain ⟨r, b, hb, hspan⟩ := exists_adapted_basisD_adjoin α (isAlgebraic_of_mem_field K hαK) T hTf
    (fun s hs => isAlgebraic_of_mem_field K (hTK hs))
  have heq : IntermediateField.adjoin ℚ ({α} ∪ T) = K := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) ?_
    · rintro x (hx | hx)
      · rw [Set.mem_singleton_iff.mp hx]; exact hαK
      · exact hTK hx
    · intro x hx
      have hsum := B.sum_repr ⟨x, hx⟩
      have : x = ∑ i, (B.repr ⟨x, hx⟩ i : ℂ) * (B i : ℂ) := by
        have := congrArg (fun y : K => (y : ℂ)) hsum
        simpa [Algebra.smul_def] using this.symm
      rw [this]
      exact sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.subset_adjoin _ _ (Or.inr ⟨i, rfl⟩))
  exact ⟨r, b, hb, fun x => (hspan x).trans (by rw [heq])⟩

/-- (Ch) for `Λ_K(A)`: for a log `ℓ` and `T ∈ K^g` there is `u ∈ Λ_K(A)` with `u_s = T_s ℓ_s` for all `s`. -/
lemma exists_coord_log {A : CMAV} (hA : A.Good) (K : IntermediateField ℚ ℂ) (hκK : ∀ s, A.κ s ∈ K)
    {ℓ : Fin A.g → ℂ} (hℓ : ℓ ∈ insert A.P A.LA) (T : Fin A.g → ℂ) (hT : ∀ s, T s ∈ K) :
    ∃ u ∈ lamK A K, ∀ s, u s = T s * ℓ s := by
  by_cases hg : A.g = 0
  · refine ⟨0, Submodule.zero_mem _, fun s => (Fin.cast hg s).elim0⟩
  set s₀ : Fin A.g := ⟨0, Nat.pos_of_ne_zero hg⟩
  obtain ⟨c, hcK, hc⟩ := ch_span K.toSubfield (hA.alg s₀) A.κ hA.inj (fun s => hA.conj s s₀) hκK T hT
  refine ⟨∑ e, (⟨c e, hcK e⟩ : K) • (fun s => A.κ s ^ (e : ℕ) * ℓ s), ?_, fun s => ?_⟩
  · exact Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, ℓ, hℓ, rfl⟩)
  · rw [← hc s]
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by simp [Algebra.smul_def]; ring

namespace XSetup

variable (X : XSetup)

/-- Adapted bases for the four slots, all for one number field `K`. -/
lemma exists_adapted_slots (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hκK : ∀ i s, (X.AV i).κ s ∈ K) :
    ∃ (r : Fin 4 → ℕ) (b : (j : Fin 4) → Fin (r j) → ℂ), IsAdaptedX X.slot b ∧
      ∀ x, x ∈ KspanD (X.slot 0).α (X.slot 0).d (b 0) ↔ x ∈ K := by
  have h := fun j : Fin 4 => exists_adapted_of_field K (hκK (X.cls j) (X.sl j))
  choose r b hb hspan using h
  refine ⟨r, b, ⟨fun j => hb j, fun j => ?_⟩, hspan 0⟩
  ext x
  exact (hspan j x).trans (hspan 0 x).symm

/-- **Proposition 15, `⊆`.** -/
theorem propX15_sub (hX : ∀ i, (X.AV i).Good) (hW : Thm11KappaXA X.slot) (hWB : WuestholzXA X.slot)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK5 : 5 ≤ finrank ℚ K) (hκK : ∀ i s, (X.AV i).κ s ∈ K)
    (μ : ℂ) (hμK : μ ∈ K) (hμ0 : μ ≠ 0) (hR : X.per 0 * X.per 1 = μ * X.per 2 * X.per 3)
    (β : ℂ) (hβK : β ∈ K) (hβ0 : β ≠ 0) (v : ℂ × ℂ) (hvV : ∃ t : ℂ, v = (t * X.per 0, t * (β * X.per 2)))
    (hv : v ∈ X.psiLamK K) :
    ∃ x y : ℂ, x ∈ K ∧ y ∈ K ∧ v = (x * X.per 0 + y * X.per 3, x * (β * X.per 2) + y * (β / μ * X.per 1)) := by
  obtain ⟨r, b, hb, hK⟩ := X.exists_adapted_slots K hκK
  obtain ⟨t, rfl⟩ := hvV
  obtain ⟨l, hl, q₁, q₂, hq₁, hq₂, hlv⟩ := hv
  -- the data of each slot
  have hdat := fun j : Fin 4 => (Submodule.mem_span_set' (R := K)).mp (hl (X.cls j))
  choose N f g hfg using hdat
  have hg' := fun j k => (g j k).2
  choose e ℓ hℓ hgeq using hg'
  have hb0 := hb.basis 0
  have hKalg : ∀ z ∈ K, IsAlgebraic ℚ z := fun z hz => isAlgebraic_of_mem_field K hz
  have hcK : ∀ j k, (f j k : ℂ) * (X.slot j).α ^ e j k ∈ KspanD (X.slot 0).α (X.slot 0).d (b 0) := by
    intro j k
    rw [hK]
    exact mul_mem (f j k).2 (pow_mem (hκK _ _) _)
  have hval : ∀ j, X.z j l = slotVal X.slot (fun j k => (f j k : ℂ) * (X.slot j).α ^ e j k) ℓ j := by
    intro j
    simp only [XSetup.z, slotVal]
    rw [← hfg j]
    simp only [Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hgeq j k]
    simp [Algebra.smul_def, FKSlot.α, slot]
    ring
  have hP0 : X.per 0 ≠ 0 := by
    intro h0
    obtain ⟨-, h1, -⟩ := hWB 0 1 0 0 0 isAlgebraic_zero isAlgebraic_one isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_zero (by simp only [per] at h0; rw [h0]; ring)
    exact one_ne_zero h1
  have h1 := congrArg Prod.fst hlv
  have h2 := congrArg Prod.snd hlv
  simp only [Psi, hval] at h1 h2
  have hrel : (slotVal X.slot (fun j k => (f j k : ℂ) * (X.slot j).α ^ e j k) ℓ 0 +
      slotVal X.slot (fun j k => (f j k : ℂ) * (X.slot j).α ^ e j k) ℓ 3 + q₁) * (β * (X.slot 2).per) =
      (slotVal X.slot (fun j k => (f j k : ℂ) * (X.slot j).α ^ e j k) ℓ 2 +
        slotVal X.slot (fun j k => (f j k : ℂ) * (X.slot j).α ^ e j k) ℓ 1 + q₂) * (X.slot 0).per := by
    rw [← h1, ← h2]; simp only [per]; ring
  have hn : 5 ≤ r 0 * (X.slot 0).d := by
    have hc := finrank_span_eq_card hb0.indep
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    have : KspanD (X.slot 0).α (X.slot 0).d (b 0) = K.toSubalgebra.toSubmodule.restrictScalars ℚ := by
      ext x; rw [hK]; rfl
    rw [← KspanD, this] at hc
    rw [← hc]
    exact hK5.trans_eq (IntermediateField.finrank_eq_finrank_subalgebra K).symm
  obtain ⟨x, y, hx, hy, hxy⟩ := propXA_K hb (hW r b hb)
    (fun j => (hX (X.cls j)).cm (X.sl j)) hn hWB μ ((hK μ).mpr hμK) hμ0 hR β ((hK β).mpr hβK) hβ0
    (fun j k => (f j k : ℂ) * (X.slot j).α ^ e j k) ℓ hcK hℓ q₁ q₂ hq₁ hq₂ hrel
  refine ⟨x, y, (hK x).mp hx, (hK y).mp hy, Prod.ext ?_ ?_⟩
  · simp only
    rw [h1]
    simpa only [per] using hxy
  · simp only
    have e1 : t * X.per 0 = x * X.per 0 + y * X.per 3 := by rw [h1]; simpa only [per] using hxy
    have key : (t * (β * X.per 2) - (x * (β * X.per 2) + y * (β / μ * X.per 1))) * (μ * X.per 0) = 0 := by
      rw [show (t * (β * X.per 2) - (x * (β * X.per 2) + y * (β / μ * X.per 1))) * (μ * X.per 0) =
        β * X.per 2 * μ * (t * X.per 0) - β * X.per 2 * μ * x * X.per 0 - y * β * X.per 1 * X.per 0 * (μ / μ) by
          ring, div_self hμ0]
      linear_combination (β * X.per 2 * μ) * e1 - (y * β) * hR
    exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (mul_ne_zero hμ0 hP0))

/-- **Proposition 15, `⊇`** (uses (Ch)). -/
theorem propX15_sup (hX : ∀ i, (X.AV i).Good) (hD : X.Distinct) (hWB : WuestholzXA X.slot)
    (K : IntermediateField ℚ ℂ) (hκK : ∀ i s, (X.AV i).κ s ∈ K)
    (μ : ℂ) (hμK : μ ∈ K) (hμ0 : μ ≠ 0) (hR : X.per 0 * X.per 1 = μ * X.per 2 * X.per 3)
    (β : ℂ) (hβK : β ∈ K) (x y : ℂ) (hx : x ∈ K) (hy : y ∈ K) :
    let v : ℂ × ℂ := (x * X.per 0 + y * X.per 3, x * (β * X.per 2) + y * (β / μ * X.per 1))
    (∃ t : ℂ, v = (t * X.per 0, t * (β * X.per 2))) ∧ v ∈ X.psiLamK K := by
  intro v
  have hP0 : X.per 0 ≠ 0 := by
    intro h0
    obtain ⟨-, h1, -⟩ := hWB 0 1 0 0 0 isAlgebraic_zero isAlgebraic_one isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_zero (by simp only [per] at h0; rw [h0]; ring)
    exact one_ne_zero h1
  refine ⟨⟨x + y * X.per 3 / X.per 0, Prod.ext ?_ ?_⟩, ?_⟩
  · simp only [v]; field_simp
  · simp only [v]
    field_simp
    linear_combination (y * β) * hR
  -- the coefficients of the slots
  set co : Fin 4 → ℂ := ![x, y * (β / μ), x * β, y] with hco
  have hcoK : ∀ j, co j ∈ K := by
    have hβμ : y * (β / μ) ∈ K := mul_mem hy (div_mem hβK hμK)
    intro j; fin_cases j
    exacts [hx, hβμ, mul_mem hx hβK, hy]
  -- the target of `AV i`: `co j` at the coordinate of each slot `j` on `AV i`
  let T : (i : Fin X.m) → Fin (X.AV i).g → ℂ := fun i s =>
    ∑ j, if X.cls j = i ∧ (X.sl j : ℕ) = s then co j else 0
  have hTK : ∀ i s, T i s ∈ K := fun i s =>
    sum_mem fun j _ => by split_ifs; exacts [hcoK j, zero_mem _]
  have hu := fun i => exists_coord_log (hX i) K (hκK i) (Set.mem_insert _ _) (T i) (hTK i)
  choose u hu hus using hu
  have hz : ∀ j, X.z j u = co j * X.per j := by
    intro j
    rw [XSetup.z, hus, per, slot, FKSlot.per]
    congr 1
    simp only [T]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      refine ite_eq_right_iff.mpr fun h => absurd h ?_
      rintro ⟨h1, h2⟩
      exact hD j' j hj' h1 h2
    · simp
  refine ⟨u, hu, 0, 0, isAlgebraic_zero, isAlgebraic_zero, Prod.ext ?_ ?_⟩
  · simp only [v, Psi, hz, hco]; simp
  · simp only [v, Psi, hz, hco]; simp; ring

/-- **Proposition 15** (paper [II], `prop:X`): `V ∩ Ψ(Λ_K(G)) = Kw + Kw'`. -/
theorem propX15 (hX : ∀ i, (X.AV i).Good) (hD : X.Distinct) (hW : Thm11KappaXA X.slot) (hWB : WuestholzXA X.slot)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK5 : 5 ≤ finrank ℚ K) (hκK : ∀ i s, (X.AV i).κ s ∈ K)
    (μ : ℂ) (hμK : μ ∈ K) (hμ0 : μ ≠ 0) (hR : X.per 0 * X.per 1 = μ * X.per 2 * X.per 3)
    (β : ℂ) (hβK : β ∈ K) (hβ0 : β ≠ 0) :
    {v | (∃ t : ℂ, v = (t * X.per 0, t * (β * X.per 2))) ∧ v ∈ X.psiLamK K} =
      {v | ∃ x y : ℂ, x ∈ K ∧ y ∈ K ∧
        v = (x * X.per 0 + y * X.per 3, x * (β * X.per 2) + y * (β / μ * X.per 1))} := by
  ext v
  constructor
  · rintro ⟨hV, hv⟩
    exact X.propX15_sub hX hW hWB K hK5 hκK μ hμK hμ0 hR β hβK hβ0 v hV hv
  · rintro ⟨x, y, hx, hy, rfl⟩
    exact X.propX15_sup hX hD hWB K hκK μ hμK hμ0 hR β hβK x y hx hy

/-- The data value `z_j(v_j) = Σ_k c_k z_j(v_k)` of slot `j` (`v_k ∈ LieG`; only the component on `A_j` matters). -/
def dataVal {N : Fin 4 → ℕ} (c : (j : Fin 4) → Fin (N j) → ℂ) (v : (j : Fin 4) → Fin (N j) → X.LieG)
    (j : Fin 4) : ℂ :=
  ∑ k, c j k * X.z j (v j k)

/-- A number field containing a finite set of algebraic numbers and `ζ₇` (so `[K : ℚ] ≥ 6`). -/
lemma exists_field (F : Finset ℂ) (hF : ∀ x ∈ F, IsAlgebraic ℚ x) :
    ∃ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K ∧ 5 ≤ finrank ℚ K ∧ ∀ x ∈ F, x ∈ K := by
  set T : Set ℂ := insert zeta7 (F : Set ℂ)
  have hT : ∀ x ∈ T, IsIntegral ℚ x := by
    rintro x (rfl | hx)
    exacts [isAlgebraic_zeta7.isIntegral, (hF x hx).isIntegral]
  have : Finite T := (F.finite_toSet.insert zeta7).to_subtype
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) := IntermediateField.finiteDimensional_adjoin hT
  refine ⟨_, hfd, ?_, fun x hx => IntermediateField.subset_adjoin _ _ (Or.inr hx)⟩
  have hle : IntermediateField.adjoin ℚ {zeta7} ≤ IntermediateField.adjoin ℚ T :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin ℚ T (Set.mem_insert _ _)))
  have h6 : finrank ℚ (IntermediateField.adjoin ℚ {zeta7}) = 6 := by
    rw [IntermediateField.adjoin.finrank isAlgebraic_zeta7.isIntegral, natDegree_minpoly_zeta7]
  have := IntermediateField.finrank_le_of_le_right hle
  omega

/-- **Theorem X** (paper [II], `thm:X`, generic): for pairwise distinct first-kind slots with the relation
`P_aP_b = μP_cP_d` (`μ ∈ ℚ̄ˣ`), `β ∈ ℚ̄ˣ`, data `z_j(v_j) ∈ ℚ̄ z_j(Λ(A_j))` and `q₁, q₂ ∈ ℚ̄` with
`(z_a(v_a) + z_d(v_d) + q₁)·βP_c = (z_c(v_c) + z_b(v_b) + q₂)·P_a`, one has `q₁ = q₂ = 0` and `z_j(v_j) ∈ ℚ̄P_j`. Assumes
W88 for the block groups (`hW`), and Wüstholz's theorem in the forms `WuestholzXA`, `WuestholzSplitXA`. -/
theorem thmXA (hX : ∀ i, (X.AV i).Good) (hD : X.Distinct) (hW : Thm11KappaXA X.slot) (hWB : WuestholzXA X.slot)
    (hSp : WuestholzSplitXA X.slot) (μ : ℂ) (hμ : IsAlgebraic ℚ μ) (hμ0 : μ ≠ 0)
    (hR : X.per 0 * X.per 1 = μ * X.per 2 * X.per 3) (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0)
    {N : Fin 4 → ℕ} (c : (j : Fin 4) → Fin (N j) → ℂ) (v : (j : Fin 4) → Fin (N j) → X.LieG)
    (hc : ∀ j k, IsAlgebraic ℚ (c j k))
    (hv : ∀ j k, v j k (X.cls j) ∈ insert (X.AV (X.cls j)).P (X.AV (X.cls j)).LA)
    (q₁ q₂ : ℂ) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂)
    (hrel : (X.dataVal c v 0 + X.dataVal c v 3 + q₁) * (β * X.per 2) =
      (X.dataVal c v 2 + X.dataVal c v 1 + q₂) * X.per 0) :
    q₁ = 0 ∧ q₂ = 0 ∧ ∀ j, ∃ a : ℂ, IsAlgebraic ℚ a ∧ X.dataVal c v j = a * X.per j := by
  classical
  -- the field
  set F : Finset ℂ := {μ, β} ∪ Finset.univ.biUnion (fun j : Fin 4 => Finset.univ.image (c j)) ∪
    Finset.univ.biUnion (fun i : Fin X.m => Finset.univ.image (X.AV i).κ) with hFdef
  obtain ⟨K, hfd, hK5, hFK⟩ := exists_field F (by
    intro x hx
    simp only [hFdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_biUnion,
      Finset.mem_univ, Finset.mem_image, true_and] at hx
    rcases hx with ((rfl | rfl) | ⟨j, k, rfl⟩) | ⟨i, s, rfl⟩
    exacts [hμ, hβ, hc j k, (hX i).alg s])
  have hμK : μ ∈ K := hFK μ (by simp [hFdef])
  have hβK : β ∈ K := hFK β (by simp [hFdef])
  have hcK : ∀ j k, c j k ∈ K := by
    intro j k
    apply hFK
    simp only [hFdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact Or.inl (Or.inr ⟨j, k, rfl⟩)
  have hκK : ∀ i s, (X.AV i).κ s ∈ K := by
    intro i s
    apply hFK
    simp only [hFdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    exact Or.inr ⟨i, s, rfl⟩
  have hKalg : ∀ z ∈ K, IsAlgebraic ℚ z := fun z hz => isAlgebraic_of_mem_field K hz
  -- (Ch): one point of `Λ_K(G)` carrying all the data
  have hU : ∀ j k i, ∃ u ∈ lamK (X.AV i) K,
      ∀ s, u s = (if i = X.cls j ∧ (s : ℕ) = X.sl j then 1 else 0) * v j k i s := by
    intro j k i
    by_cases h : i = X.cls j
    · subst h
      exact exists_coord_log (hX _) K (hκK _) (hv j k) _ (fun s => by split_ifs; exacts [one_mem _, zero_mem _])
    · exact ⟨0, Submodule.zero_mem _, fun s => by simp [h]⟩
  choose U hU hUs using hU
  set l : X.LieG := fun i => ∑ j, ∑ k, (⟨c j k, hcK j k⟩ : K) • U j k i with hldef
  have hl : ∀ i, l i ∈ lamK (X.AV i) K := fun i =>
    Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hU j k i)
  have hz : ∀ j', X.z j' l = X.dataVal c v j' := by
    intro j'
    simp only [XSetup.z, hldef, Finset.sum_apply, Pi.smul_apply, dataVal]
    rw [Finset.sum_eq_single j']
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hUs]; simp [Algebra.smul_def, XSetup.z]
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hUs, ite_eq_right_iff.mpr (fun h => absurd h (fun h' => hD j j' hj h'.1.symm h'.2.symm))]
      simp
    · simp
  have hP0 : X.per 0 ≠ 0 := by
    intro h0
    obtain ⟨-, h1, -⟩ := hWB 0 1 0 0 0 isAlgebraic_zero isAlgebraic_one isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_zero (by simp only [per] at h0; rw [h0]; ring)
    exact one_ne_zero h1
  -- Proposition 15
  obtain ⟨x, y, hx, hy, hxy⟩ := X.propX15_sub hX hW hWB K hK5 hκK μ hμK hμ0 hR β hβK hβ0 (X.Psi l q₁ q₂)
    ⟨(X.dataVal c v 0 + X.dataVal c v 3 + q₁) / X.per 0, by
      refine Prod.ext ?_ ?_
      · simp only [Psi, hz]; field_simp
      · simp only [Psi, hz]; field_simp; linear_combination -hrel⟩
    ⟨l, hl, q₁, q₂, hq₁, hq₂, rfl⟩
  have e1 := congrArg Prod.fst hxy
  have e2 := congrArg Prod.snd hxy
  simp only [Psi, hz] at e1 e2
  have hzQ : ∀ j, X.dataVal c v j ∈ zQbar (X.slot j) := fun j =>
    ⟨N j, c j, fun k => v j k (X.cls j), hc j, hv j, rfl⟩
  obtain ⟨f1, f2, f3⟩ := hSp.1 _ _ q₁ x y (hzQ 0) (hzQ 3) hq₁ (hKalg _ hx) (hKalg _ hy) (by
    simpa only [per] using e1)
  have hβμ : IsAlgebraic ℚ (y * (β / μ)) := by
    rw [← mem_algebraicClosure_iff]
    exact mul_mem (mem_algebraicClosure_iff.mpr (hKalg _ hy))
      (div_mem (mem_algebraicClosure_iff.mpr hβ) (mem_algebraicClosure_iff.mpr hμ))
  obtain ⟨g1, g2, g3⟩ := hSp.2 _ _ q₂ (x * β) (y * (β / μ)) (hzQ 2) (hzQ 1) hq₂ ((hKalg _ hx).mul hβ) hβμ (by
    simp only [per] at e2; rw [e2]; ring)
  refine ⟨f1, g1, fun j => ?_⟩
  fin_cases j
  · exact ⟨x, hKalg _ hx, f2⟩
  · exact ⟨_, hβμ, g3⟩
  · exact ⟨_, (hKalg _ hx).mul hβ, g2⟩
  · exact ⟨y, hKalg _ hy, f3⟩

end XSetup

end CM4E.AbVar
