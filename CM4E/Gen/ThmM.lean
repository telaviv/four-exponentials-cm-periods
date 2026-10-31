/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Common
import CM4E.Gen.FrameM
import CM4E.Gen.MG
import CM4E.Gen.SMG

/-!
# Theorem M (paper [I], §`sec:M`, first proof)

Let `L = ω ℤ[α]` be a CM lattice with algebraic `g₂, g₃`, `Ω = cω` (`c ∈ ℚ̄ˣ`). If `u ∈ ℚ̄𝓛_E`, `ℓ ∈ 𝓛̃` and
`iπu = Ωℓ`, then `u = sΩ` and `ℓ = s·iπ` with `s ∈ ℚ̄` (`thmM`).

The paper's first proof applies Roy–Waldschmidt to `G = E × G_m × G_a`, `Ψ(e, t, a) = (e, t + a)`, `V = ℂ(Ω, iπ)`
(`κ = 1`, `α_K(G) = 2`). Here the `K`-structure is made explicit as for Theorem MG: with an adapted basis `θ` of a number
field `K ⊇ k` containing the coefficients, the group is `G'' = A'' × G_m^n × G_a`, `A'' = E^n / B_{ker ψ}` (the abelian
variety of `CM4E/Gen/MG.lean`, of dimension `≤ r = n/2`), and `Ψ''([z], y, s) = (θᵀz, θᵀy + s)`. W88 §5d is applied to
`V'' = Ψ''⁻¹(ℂ(Ω, iπ))` with the `n` period lifts of `θ_h(Ω, iπ)` and one lift of `(u, ℓ)`: `m = n + 1`, `κ ≥ n`,
`d₁ + 2d₂ − κ ≤ n` (`CM4E/Gen/FrameM.lean`). The CM structure enters through `d₂ = dim A'' ≤ n/2`; without CM the
count ties, as the paper notes.

Soundness of `gmM L b` (not checked by Lean): `G''` is the product `A'' × G_m^n × G_a`, so `d₀ = 1`, `d₁ = n`,
`d₂ = dim A''`. The logarithms: the image in `T(A'')` of `u e_j` with `u ∈ 𝓛_E` is a logarithm of an algebraic point of
`A''` (`E^n → A''` is an isogeny-quotient defined over `ℚ̄`); `l e_h` with `e^l ∈ ℚ̄` and `c ∈ ℚ̄` are logarithms in
`G_m^n` and `G_a`. The periods: `perQm` (as in `MG.lean`) and `2πi e_h`. Subgroups: a connected algebraic subgroup of
`A'' × G_m^n × G_a` is a product `B × T × (0 or G_a)` (no nonzero homomorphisms between the three kinds of factor). A
nonzero `B` has `θᵀ ≠ 0` on `T(B)` (as in `MG.lean`); a nonzero subtorus `T_ℒ` has `θᵀ ≠ 0` on its rational tangent
vectors, since `θ` is `ℚ`-independent; `G_a` has `Ψ''(0, 0, 1) = (0, 1)`. Each tangent space is spanned by algebraic
vectors, so one of them has `Ψ'' ≠ 0`.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

/-- `u ∈ 𝓛_E`: `u` is a period, or `exp_E(u)` is an algebraic affine point. -/
def LogE (P : PeriodPair) (u : ℂ) : Prop :=
  u ∈ P.lattice ∨ (IsAlgebraic ℚ (P.weierstrassP u) ∧ IsAlgebraic ℚ (P.derivWeierstrassP u))

/-- `ℚ̄𝓛_E`. -/
def QbarLogE (P : PeriodPair) : Set ℂ :=
  {u | ∃ (N : ℕ) (β v : Fin N → ℂ), (∀ k, IsAlgebraic ℚ (β k)) ∧ (∀ k, LogE P (v k)) ∧ u = ∑ k, β k * v k}

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- A logarithm of `E` in slot `j` of `E^n`, pushed to `A''`. -/
noncomputable def eSlot (j : Fin r × Fin 2) (u : ℂ) : TM (Fin r × Fin 2) (Qm L b) :=
  (Submodule.Quotient.mk (Pi.single j u), 0, 0)

/-- A logarithm in slot `h` of `G_m^n`. -/
noncomputable def mSlot (h : Fin r × Fin 2) (l : ℂ) : TM (Fin r × Fin 2) (Qm L b) := (0, Pi.single h l, 0)

/-- A logarithm of `G_a`. -/
noncomputable def aSlot (c : ℂ) : TM (Fin r × Fin 2) (Qm L b) := (0, 0, c)

/-- Generators of the logarithms of `A'' × G_m^n × G_a`. -/
def lamMS : Set (TM (Fin r × Fin 2) (Qm L b)) :=
  {v | ∃ j u, LogE L.pp u ∧ v = eSlot L b j u} ∪
    {v | ∃ h l, IsAlgebraic ℚ (Complex.exp l) ∧ v = mSlot L b h l} ∪ {v | ∃ c, IsAlgebraic ℚ c ∧ v = aSlot L b c}

/-- Generators of the periods of `A'' × G_m^n × G_a`. -/
def perMS : Set (TM (Fin r × Fin 2) (Qm L b)) :=
  (fun q => (q, (0 : Fin r × Fin 2 → ℂ), (0 : ℂ))) '' perQm L b ∪
    Set.range (fun h => mSlot L b h (2 * Real.pi * I))

/-- The model of `A'' × G_m^n × G_a`. -/
noncomputable def gmM : GroupModel (TM (Fin r × Fin 2) (Qm L b)) :=
  gmFM (theta L.α b) (algQm L b) (lamMS L b) (perMS L b) (lamM L b) (finrank ℂ (Qm L b))

/-- **The hypothesis for Theorem M**: W88 §5d for `A'' × G_m^n × G_a`, for every adapted basis. -/
def Thm11KappaM : Prop :=
  IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmM L b)

lemma finrank_Qm_le : finrank ℂ (Qm L b) ≤ r := by
  show finrank ℂ ((Fin r × Fin 2 → ℂ) ⧸ Wpsi L b) ≤ _
  have h1 := Submodule.finrank_quotient_add_finrank (Wpsi L b)
  have h2 := finrank_Wpsi_ge L b
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at h1 ⊢
  omega

lemma PsiM_eSlot (j : Fin r × Fin 2) (u : ℂ) :
    PsiM (theta L.α b) (lamM L b) (eSlot L b j u) = (theta L.α b j * u, 0) := by
  simp [PsiM_apply, eSlot, lamM_mk, dotL_single]

lemma PsiM_mSlot (h : Fin r × Fin 2) (l : ℂ) :
    PsiM (theta L.α b) (lamM L b) (mSlot L b h l) = (0, theta L.α b h * l) := by
  simp [PsiM_apply, mSlot, dotL_single]

lemma PsiM_aSlot (c : ℂ) : PsiM (theta L.α b) (lamM L b) (aSlot L b c) = (0, c) := by
  simp [PsiM_apply, aSlot]

lemma PsiM_qsmul (q : ℚ) (v : TM (Fin r × Fin 2) (Qm L b)) :
    PsiM (theta L.α b) (lamM L b) (q • v) =
      ((q : ℂ) * (PsiM (theta L.α b) (lamM L b) v).1, (q : ℂ) * (PsiM (theta L.α b) (lamM L b) v).2) := by
  rw [map_rat_smul]
  exact Prod.ext (by rw [Prod.smul_fst, Rat.smul_def]) (by rw [Prod.smul_snd, Rat.smul_def])

/-- **Theorem M** (`Ω = cω`, `c ∈ ℚ̄ˣ`): if `u ∈ ℚ̄𝓛_E`, `ℓ ∈ 𝓛̃` and `iπu = Ωℓ`, then `u = sΩ` and `ℓ = s·iπ` with
`s ∈ ℚ̄`. Hypotheses: W88 §5d for the groups `A'' × G_m^n × G_a` (`hW`), algebraic `g₂, g₃`, and the transcendence of
`ω/π` (Schneider). -/
theorem thmM (hW : Thm11KappaM L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ (L.ω / Real.pi)) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (u ℓ : ℂ) (hu : u ∈ QbarLogE L.pp) (hℓ : ℓ ∈ Ltilde) (hrel : I * Real.pi * u = c * L.ω * ℓ) :
    ∃ s : ℂ, IsAlgebraic ℚ s ∧ u = s * (c * L.ω) ∧ ℓ = s * (I * Real.pi) := by
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : I ≠ 0 := I_ne_zero
  have hA : c * L.ω ≠ 0 := mul_ne_zero hc0 hω
  suffices hsuf : ∃ s : ℂ, IsAlgebraic ℚ s ∧ u = s * (c * L.ω) by
    obtain ⟨s, hs, hus⟩ := hsuf
    refine ⟨s, hs, hus, mul_left_cancel₀ hA ?_⟩
    rw [← hrel, hus]; ring
  by_contra hcon
  have hx : ∀ s : ℂ, IsAlgebraic ℚ s → u ≠ s * (c * L.ω) := fun s hs h => hcon ⟨s, hs, h⟩
  obtain ⟨N, β, v, hβ, hv, rfl⟩ := hu
  obtain ⟨M, β₀, γ, l, hβ₀, hγ, hl, rfl⟩ := hℓ
  obtain ⟨r, hr, b, hb, hS⟩ := exists_adapted_basis L.α L.isAlgebraic_α L.him.ne' ⟨L.p, L.q, L.hquad⟩
    (insert c (Finset.univ.image β ∪ Finset.univ.image γ)) (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hs
      rcases hs with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
      exacts [hc, hβ k, hγ k])
  have hcK : c ∈ Kspan L.α b := hS c (by simp)
  have hβK : ∀ k, β k ∈ Kspan L.α b := fun k => hS _ (by simp)
  have hγK : ∀ k, γ k ∈ Kspan L.α b := fun k => hS _ (by simp)
  have hθalg := theta_isAlgebraic L.isAlgebraic_α hb.alg
  have hr1 : 1 ≤ r := by omega
  set i0 : Fin r × Fin 2 := (⟨0, by omega⟩, 0)
  have h0 : (theta L.α b) i0 ≠ 0 := hb.indep.ne_zero i0
  -- `σ = iπ/Ω` is transcendental
  have hσ : Transcendental ℚ (I * Real.pi / (c * L.ω)) := by
    intro halg
    apply hT
    have : L.ω / Real.pi = I / (c * (I * Real.pi / (c * L.ω))) := by field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (mem_algebraicClosure_iff.mpr isAlgebraic_I)
      (mul_mem (mem_algebraicClosure_iff.mpr hc) (mem_algebraicClosure_iff.mpr halg))
  -- the period lifts
  have hxK : ∀ h, theta L.α b h * c ∈ Kspan L.α b := fun h =>
    hb.mul_mem _ (Submodule.subset_span ⟨h, rfl⟩) _ hcK
  choose m hm using fun h => exists_coords (hxK h)
  have hωL : LogE L.pp L.ω := Or.inl (L.hω₁ ▸ L.pp.ω₁_mem_lattice)
  have hexpπ : IsAlgebraic ℚ (Complex.exp (I * Real.pi)) := by
    rw [mul_comm, Complex.exp_pi_mul_I]; exact isAlgebraic_one.neg
  let p : Fin r × Fin 2 → TM (Fin r × Fin 2) (Qm L b) := fun h =>
    ∑ j, (m h j : ℚ) • eSlot L b j L.ω + mSlot L b h (I * Real.pi)
  have hpl : ∀ h, p h ∈ Submodule.span ℚ (lamMS L b) := fun h =>
    add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl ⟨j, L.ω, hωL, rfl⟩))))
      (Submodule.subset_span (Or.inl (Or.inr ⟨h, _, hexpπ, rfl⟩)))
  have hpp : ∀ h, p h ∈ Submodule.span ℚ (perMS L b) := by
    intro h
    refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl ⟨_, Or.inl ⟨j, rfl⟩, rfl⟩))) ?_
    have : mSlot L b h (I * Real.pi) = (1 / 2 : ℚ) • mSlot L b h (2 * Real.pi * I) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [mSlot]
      · funext k
        simp only [mSlot, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, Pi.single_apply, Rat.smul_def]
        split_ifs <;> push_cast <;> ring
      · simp [mSlot]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨h, rfl⟩))
  have hpΨ : ∀ h, PsiM (theta L.α b) (lamM L b) (p h) =
      (theta L.α b h * (c * L.ω), I * Real.pi / (c * L.ω) * (theta L.α b h * (c * L.ω))) := by
    intro h
    simp only [p, map_add, map_sum, PsiM_qsmul, PsiM_eSlot, PsiM_mSlot]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, add_zero]
      rw [show theta L.α b h * (c * L.ω) = (theta L.α b h * c) * L.ω by ring, ← hm h, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [Prod.snd_add, Prod.snd_sum, mul_zero, Finset.sum_const_zero, zero_add]
      field_simp
  -- the data lift
  let D : TM (Fin r × Fin 2) (Qm L b) :=
    ∑ k, ∑ j, (coordsA L.α b (β k) j : ℚ) • eSlot L b j (v k) +
      ∑ k, ∑ h, (coordsA L.α b (γ k) h : ℚ) • mSlot L b h (l k) + aSlot L b β₀
  have hDl : D ∈ Submodule.span ℚ (lamMS L b) :=
    add_mem (add_mem
      (Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inl (Or.inl ⟨j, v k, hv k, rfl⟩))))
      (Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Or.inl (Or.inr ⟨h, l k, hl k, rfl⟩)))))
      (Submodule.subset_span (Or.inr ⟨β₀, hβ₀, rfl⟩))
  have hDΨ : PsiM (theta L.α b) (lamM L b) D =
      (∑ k, β k * v k, I * Real.pi / (c * L.ω) * ∑ k, β k * v k) := by
    simp only [D, map_add, map_sum, PsiM_qsmul, PsiM_eSlot, PsiM_mSlot, PsiM_aSlot]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, mul_zero, Finset.sum_const_zero, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show β k * v k = (∑ j, (coordsA L.α b (β k) j : ℂ) * theta L.α b j) * v k by
        rw [coordsA_spec (hβK k)], Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    · simp only [Prod.snd_add, Prod.snd_sum, mul_zero, Finset.sum_const_zero, zero_add]
      have e : ∑ k, ∑ h, (coordsA L.α b (γ k) h : ℂ) * (theta L.α b h * l k) = ∑ k, γ k * l k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show γ k * l k = (∑ h, (coordsA L.α b (γ k) h : ℂ) * theta L.α b h) * l k by
          rw [coordsA_spec (hγK k)], Finset.sum_mul]
        exact Finset.sum_congr rfl fun h _ => by ring
      rw [e]
      field_simp
      linear_combination -hrel
  refine frameM_false (theta L.α b) hb.indep hθalg (algQm L b) (lamMS L b) (perMS L b) (lamM L b)
    (finrank ℂ (Qm L b)) (hW hg₂ hg₃ r b hb) (by have := finrank_Qm_le L b; simp; omega) (by simp; omega)
    ⟨0, fun _ => isAlgebraic_zero, by simp⟩ ?_
    (Set.range fun j => (Submodule.Quotient.mk
      (((theta L.α b) i0) • Pi.single j 1 - ((theta L.α b) j) • Pi.single i0 1 : Fin r × Fin 2 → ℂ) : Qm L b))
    ?_ ?_ _ hσ _ hA p hpl hpp hpΨ D _ hDl hDΨ hx
  · rintro q ⟨w, hw, rfl⟩
    rw [lamM_mk, dotL_apply, ← mem_algebraicClosure_iff]
    exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
      (mem_algebraicClosure_iff.mpr (hw j))
  · rintro _ ⟨j, rfl⟩
    refine ⟨_, fun k => ?_, rfl⟩
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    exact ((hθalg i0).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero)).sub
      ((hθalg j).mul (isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero))
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp [lamM_mk, map_sub, map_smul, dotL_single, mul_comm]
    · intro x hx
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, lamM_mk] at hx
      have hdec := decomp_x h0 w hx
      rw [show (Submodule.Quotient.mk w : Qm L b) = (Wpsi L b).mkQ (∑ j, (w j / (theta L.α b) i0) •
          (((theta L.α b) i0) • Pi.single j 1 - ((theta L.α b) j) • Pi.single i0 1 :
            Fin r × Fin 2 → ℂ)) by rw [hdec]; rfl, map_sum]
      exact Submodule.sum_mem _ fun j _ => by
        rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end CM4E.Gen
