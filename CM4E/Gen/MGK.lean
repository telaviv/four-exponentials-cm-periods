/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Frame2
import CM4E.Gen.SMG
import CM4E.Gen.ThmM

/-!
# Theorem MG in its `K`-dimension form (paper [I], `thm:MG`)

For a CM lattice `ω ℤ[α]`, `c ∈ ℚ̄ˣ`, `s = cω/π` and a number field `K ⊇ k(i, c)`,
`S_K = {x ∈ K𝓛 : sx ∈ K𝓛 + K𝓛_E}` has `dim_K S_K ≤ 2`; since `2πi ∈ S_K`, this says that there are no
`x₁, x₂ ∈ S_K` with `2πi, x₁, x₂` linearly independent over `K` (`mg_K`). The paper first enlarges `K` (by Baker's
theorem `K`-independence in `K𝓛` survives base change); here `K` is assumed to contain `i` and `c`, as in the paper's
proof after that reduction.

The group is that of the paper's proof, `G'' = G_m^{2n} × A''`, `A'' = E^n / B_{ker ψ}`, with
`Ψ''(x, y, [z]) = (θᵀx, θᵀy + θᵀz)`. The model `gmMGK` differs from `gmMG` (`CM4E/Gen/MG.lean`) only in that its
logarithms also contain the images of elliptic logarithms `u e_j`, `u ∈ 𝓛_E` (needed for the data in `K𝓛_E`), and in
using the uniform subgroup condition of `CM4E/Gen/Frame2.lean`.

Soundness of `gmMGK L b` (not checked by Lean): `G''` is the product `G_m^{2n} × A''` (`d₀ = 0`, `d₁ = 2n`,
`d₂ = dim A''`); the logarithms and periods are as for `gmMG` and `gmM` (`CM4E/Gen/ThmM.lean`); connected subgroups are
products `T_L × B`, and a nonzero one has an algebraic tangent vector with `Ψ'' ≠ 0` (`θ` is `ℚ`-independent, and `θᵀ`
does not vanish on a nonzero abelian subvariety of `A''`, as in the proof of Theorem MG).
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

/-- `K𝓛`: `K`-combinations of logarithms of algebraic numbers. -/
def KLog (K : Submodule ℚ ℂ) : Set ℂ :=
  {x | ∃ (N : ℕ) (β ℓ : Fin N → ℂ), (∀ k, β k ∈ K) ∧ (∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) ∧
    x = ∑ k, β k * ℓ k}

/-- `K𝓛_E`: `K`-combinations of elliptic logarithms. -/
def KLogE (K : Submodule ℚ ℂ) (P : PeriodPair) : Set ℂ :=
  {x | ∃ (N : ℕ) (β u : Fin N → ℂ), (∀ k, β k ∈ K) ∧ (∀ k, LogE P (u k)) ∧ x = ∑ k, β k * u k}

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- Generators of the logarithms of `G_m^{2n} × A''`. -/
def lamMGK : Set (TF (Fin r × Fin 2) (Qm L b)) :=
  {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 i x} ∪
    {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 i x} ∪
    {v | ∃ i u, LogE L.pp u ∧ v = qv (Submodule.Quotient.mk (Pi.single i u) : Qm L b)}

/-- The model of `G_m^{2n} × A''` with elliptic logarithms. -/
noncomputable def gmMGK : GroupModel (TF (Fin r × Fin 2) (Qm L b)) :=
  gmF2 (theta L.α b) (algQm L b) (lamMGK L b) (perGen (ι := Fin r × Fin 2) (perQm L b)) 0 (lamM L b)
    (finrank ℂ (Qm L b))

/-- **The hypothesis for the `K`-form of Theorem MG**: W88 §5d for `G_m^{2n} × A''`, for every adapted basis. -/
def Thm11KappaMGK : Prop :=
  IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmMGK L b)

/-- A lift of `θ_h Σ β_k u_k` (`u_k ∈ 𝓛_E`) in `A''`. -/
noncomputable def eLift (h : Fin r × Fin 2) {N : ℕ} (β u : Fin N → ℂ) : TF (Fin r × Fin 2) (Qm L b) :=
  ∑ k, ∑ i, (coordsA L.α b (theta L.α b h * β k) i) • qv (Submodule.Quotient.mk (Pi.single i (u k)) : Qm L b)

variable {b}

lemma eLift_coords (hb : IsAdaptedFieldBasis L.α b) (h : Fin r × Fin 2) {N : ℕ} (β u : Fin N → ℂ)
    (hβ : ∀ k, β k ∈ Kspan L.α b) :
    (eLift L b h β u).1 = 0 ∧ lamM L b (eLift L b h β u).2 = theta L.α b h * ∑ k, β k * u k := by
  refine ⟨by simp [eLift, qv, Prod.fst_sum], ?_⟩
  simp only [eLift, qv, Prod.snd_sum, Prod.smul_snd, map_sum, map_rat_smul, lamM_mk, dotL_single,
    Rat.smul_def]
  rw [Finset.mul_sum]; congr 1; funext k
  have := coordsA_spec (hb.mul_mem _ (Submodule.subset_span ⟨h, rfl⟩) _ (hβ k))
  rw [show ∑ i, (coordsA L.α b (theta L.α b h * β k) i : ℂ) * (theta L.α b i * u k) =
      (∑ i, (coordsA L.α b (theta L.α b h * β k) i : ℂ) * theta L.α b i) * u k by
    rw [Finset.sum_mul]; congr 1; funext i; ring, this]
  ring

lemma eLift_mem (h : Fin r × Fin 2) {N : ℕ} (β u : Fin N → ℂ) (hu : ∀ k, LogE L.pp (u k)) :
    eLift L b h β u ∈ Submodule.span ℚ (lamMGK L b) :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, u k, hu k, rfl⟩))

/-- **Theorem MG, `K`-form**: for `s = cω/π` and `K ∋ i, c`, there are no `x₁, x₂ ∈ K𝓛` with
`sx₁, sx₂ ∈ K𝓛 + K𝓛_E` and `2πi, x₁, x₂` linearly independent over `K`. Hypotheses: W88 §5d for
`G_m^{2n} × A''` (`hW`), algebraic `g₂, g₃`, and the transcendence of `ω/π` (Schneider). -/
theorem mg_K (hW : Thm11KappaMGK L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ (L.ω / Real.pi)) (hb : IsAdaptedFieldBasis L.α b)
    (c : ℂ) (hcK : c ∈ Kspan L.α b) (hc0 : c ≠ 0) (hIK : I ∈ Kspan L.α b)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ KLog (Kspan L.α b))
    (hsx : ∀ k, ∃ y ∈ KLog (Kspan L.α b), ∃ e ∈ KLogE (Kspan L.α b) L.pp, c * L.ω / Real.pi * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Kspan L.α b → a₁ ∈ Kspan L.α b → a₂ ∈ Kspan L.α b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  set s := c * L.ω / Real.pi with hsdef
  choose N β ℓ hβ hℓ hxe using hx
  choose y hy e he hye using hsx
  choose N' β' ℓ' hβ' hℓ' hye' using hy
  choose N'' β'' u hβ'' hu he' using he
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθalg := theta_isAlgebraic L.isAlgebraic_α hb.alg
  have hr : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    subst hr0
    have := hb.one_mem
    rw [Kspan, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hc : IsAlgebraic ℚ c := by
    obtain ⟨m, hm⟩ := exists_coords hcK
    rw [← hm, ← mem_algebraicClosure_iff]
    exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (m j)))
      (mem_algebraicClosure_iff.mpr (hθalg j))
  -- period lifts
  have h2 : (2 : ℂ) ∈ Kspan L.α b := by
    have := Submodule.smul_mem _ (2 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hxK : ∀ h, 2 * I * c * theta L.α b h ∈ Kspan L.α b := fun h =>
    hb.mul_mem _ (hb.mul_mem _ (hb.mul_mem _ h2 _ hIK) _ hcK) _ (Submodule.subset_span ⟨h, rfl⟩)
  let qh : Fin r × Fin 2 → Qm L b := fun h =>
    ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℚ) • (Submodule.Quotient.mk (Pi.single j L.ω) : Qm L b)
  have hlqh : ∀ h, lamM L b (qh h) = s * (theta L.α b h * (2 * Real.pi * I)) := by
    intro h
    simp only [qh, map_sum, map_rat_smul, lamM_mk, dotL_single, Rat.smul_def]
    rw [show ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℂ) * (theta L.α b j * L.ω) =
        (∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℂ) * theta L.α b j) * L.ω by
      rw [Finset.sum_mul]; congr 1; funext j; ring, coordsA_spec (hxK h), hsdef]
    field_simp
  have hωL : LogE L.pp L.ω := Or.inl (L.hω₁ ▸ L.pp.ω₁_mem_lattice)
  have hqh_lam : ∀ h, qv (qh h) ∈ Submodule.span ℚ (lamMGK L b) := by
    intro h
    have : qv (qh h) = ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℚ) •
        (qv (Submodule.Quotient.mk (Pi.single j L.ω) : Qm L b) : TF (Fin r × Fin 2) (Qm L b)) := by
      simp [qv, qh, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨j, L.ω, hωL, rfl⟩))
  have hqh_per : ∀ h, qv (qh h) ∈ Submodule.span ℚ (perGen (ι := Fin r × Fin 2) (perQm L b)) := by
    intro h
    have : qv (qh h) = ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℚ) •
        (qv (Submodule.Quotient.mk (Pi.single j L.ω) : Qm L b) : TF (Fin r × Fin 2) (Qm L b)) := by
      simp [qv, qh, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨_, Or.inl ⟨j, rfl⟩, rfl⟩))
  -- `s` transcendental
  have hs : Transcendental ℚ s := by
    intro halg
    apply hT
    have : L.ω / Real.pi = s / c := by rw [hsdef]; field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (mem_algebraicClosure_iff.mpr halg) (mem_algebraicClosure_iff.mpr hc)
  have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
    rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  refine frame2_false_K (theta L.α b) hb.indep hθalg (algQm L b) (lamMGK L b)
    (perGen (ι := Fin r × Fin 2) (perQm L b)) 0 (lamM L b) (finrank ℂ (Qm L b)) (hW hg₂ hg₃ r b hb)
    (by have := finrank_Qm_le L b; simp; omega) ⟨0, fun _ => isAlgebraic_zero, by simp⟩
    (fun _ _ => isAlgebraic_zero) ?_
    (Set.range fun j => (Submodule.Quotient.mk (Pi.single j 1) : Qm L b)) ?_ ?_ s hs
    (fun h => tor1 h (2 * Real.pi * I) + qv (qh h)) ?_ ?_ ?_ x
    (fun k h => torLift1 (α := L.α) b h (β k) (ℓ k) + torLift2 (α := L.α) b h (β' k) (ℓ' k) +
      eLift L b h (β'' k) (u k)) ?_ ?_ ?_
  · rintro q ⟨v, hv, rfl⟩
    rw [lamM_mk, dotL_apply, ← mem_algebraicClosure_iff]
    exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
      (mem_algebraicClosure_iff.mpr (hv j))
  · rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, fun k => ?_, rfl⟩
    simp only [Pi.single_apply]; split_ifs
    exacts [isAlgebraic_one, isAlgebraic_zero]
  · rw [eq_top_iff]
    rintro q -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hdec : (Submodule.Quotient.mk v : Qm L b) =
        ∑ j, v j • (Submodule.Quotient.mk (Pi.single j 1) : Qm L b) := by
      calc (Submodule.Quotient.mk v : Qm L b)
          = (Wpsi L b).mkQ (∑ j, v j • Pi.single j 1) := by rw [sum_smul_single]; rfl
        _ = _ := by simp [map_sum, map_smul]
    rw [hdec]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, _, h2pi, rfl⟩))) (hqh_lam h)
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩))) (hqh_per h)
  · intro h
    simp only [PsiG_apply, tor1, qv, map_add, dotL_single, map_zero,
      add_zero, zero_add, hlqh, LinearMap.zero_apply]
    simp
  · intro k h
    exact add_mem (add_mem (torLift1_mem _ (fun i x hx => Or.inl (Or.inl ⟨i, x, hx, rfl⟩)) h _ _ (hℓ k))
      (torLift2_mem _ (fun i x hx => Or.inl (Or.inr ⟨i, x, hx, rfl⟩)) h _ _ (hℓ' k)))
      (eLift_mem L h _ _ (hu k))
  · intro k h
    obtain ⟨a1, a2, a3⟩ := torLift1_coords (Q := Qm L b) hb h (β k) (ℓ k) (hβ k)
    obtain ⟨c1, c2, c3⟩ := torLift2_coords (Q := Qm L b) hb h (β' k) (ℓ' k) (hβ' k)
    obtain ⟨e1, e2⟩ := eLift_coords L hb h (β'' k) (u k) (hβ'' k)
    have e1a : (eLift L b h (β'' k) (u k)).1.1 = 0 := by rw [e1]; rfl
    have e1b : (eLift L b h (β'' k) (u k)).1.2 = 0 := by rw [e1]; rfl
    simp only [PsiG_apply, map_add, a1, a2, a3, c1, c2, c3, e1a, e1b, e2,
      map_zero, LinearMap.zero_apply, add_zero, zero_add]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, add_zero]; rw [hxe k]
    · simp only [Prod.snd_add, zero_add]
      rw [show s * (theta L.α b h * x k) = theta L.α b h * (s * x k) by ring, hye k, hye' k, he' k]
      ring
  · exact hind

end CM4E.Gen
