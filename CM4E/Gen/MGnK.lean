/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MGK
import CM4E.Gen.MGn
import CM4E.MX
import CM4E.Gen.Instances

/-!
# Theorem MG♮ in its `K`-dimension form (paper [I], `thm:MGn`)

For a CM lattice `ω ℤ[α]` with `κ₁ = 0` (e.g. `ϖℤ[i]`, `Ω_ρℤ[ρ]`), `c ∈ ℚ̄ˣ`, `s = 1/(cω)` (`∈ ℚ̄ˣ η*/π`) and a number
field `K ∋ c` with `[K : ℚ] ≥ 4`, there are no `x₁, x₂ ∈ K𝓛` with `sx₁, sx₂ ∈ K𝓛 + K·(fibre values)` and
`2πi, x₁, x₂` linearly independent over `K` (`mgn_K`). Fibre values are the `w`-coordinates of `Λ(E^♮)`: `w` with
`(u, w) ∈ Λ(E^♮)` in the coordinates `exp(u, w) = (℘(u), ℘'(u), w − ζ(u))`, the conjugate-eigen ones when `κ₁ = 0`.

The group is that of `CM4E/Gen/MGn.lean`, `G'' = G_m^{2n} × Q''`, `Q'' = (E^♮)^n / U`, with the fibre coordinate
`θᵀw` as linear form. The model `gmMGnK` adds to `gmMGn` the logarithms `([u e_i], θ_i w)` of the images of the points
`(u e_i, w e_i)` of `(E^♮)^n`, and uses the uniform subgroup condition (`CM4E/Gen/Frame2.lean`).

Soundness of `gmMGnK L b` (not checked by Lean), for lattices with `κ₁ = 0` (so that `ζ* = ζ` and `η₀ = η*(ω)`, as for
the two instances, `CM4E/Gen/Instances.lean`): as for `gmMGn`; the new logarithms are images of logarithms of
algebraic points of `(E^♮)^n`; connected subgroups are products `T_L × H`, `θ` is `ℚ`-independent, and every nonzero
connected `H ⊂ Q''` contains the fibre, on which `λ ≠ 0`. For a lattice with `κ₁ ≠ 0` the generators would have to use
`ζ* = ζ − κ₁ z`; so the hypothesis `Thm11KappaMGnK L` is premised on `KappaOneZero L` (`ζ(αz) = ᾱζ(z)`, which makes the
standard `ζ` conjugate-eigen; defined in `CM4E/Gen/MGn.lean`, where `Thm11KappaMGn` carries the same premise), proved
here for `ϖℤ[i]` and `Ω_ρℤ[ρ]` (`kappaOneZero_latI`, `kappaOneZero_latRho`).
-/

open Complex Module CM4E.Waldschmidt CM4E.MX

namespace CM4E.Gen

/-- `ζ(iz) = −iζ(z)` on `ϖℤ[i]`. -/
lemma kappaOneZero_latI : KappaOneZero latI := by
  intro z
  show CM4E.Ext.Weierstrass.zeta lemniscatic (I * z) = starRingEnd ℂ I * CM4E.Ext.Weierstrass.zeta lemniscatic z
  rw [Complex.conj_I]
  calc CM4E.Ext.Weierstrass.zeta lemniscatic (I * z)
      = ∑' l : lemniscatic.lattice, CM4E.Ext.Weierstrass.zetaSummand ((mulI l : lemniscatic.lattice) : ℂ) (I * z) :=
        (mulI.tsum_eq (fun l : lemniscatic.lattice => CM4E.Ext.Weierstrass.zetaSummand (l : ℂ) (I * z))).symm
    _ = ∑' l : lemniscatic.lattice, -I * CM4E.Ext.Weierstrass.zetaSummand (l : ℂ) z := by
        congr 1 with l
        simp only [mulI, Equiv.coe_fn_mk, CM4E.Ext.Weierstrass.zetaSummand]
        rw [show I * z - I * (l : ℂ) = I * (z - l) by ring]
        simp only [mul_inv, mul_pow, Complex.I_sq, Complex.inv_I, div_eq_mul_inv, neg_one_mul, inv_neg]
        ring
    _ = -I * CM4E.Ext.Weierstrass.zeta lemniscatic z := tsum_mul_left

lemma rho_sq : rho ^ 2 = -1 - rho := by simp only [rho]; ring_nf; rw [Complex.I_sq, r3_sq]; ring

/-- `ρ` times a point of `Ω_ρℤ[ρ]` is a point of `Ω_ρℤ[ρ]`. -/
lemma rho_mul_mem_lattice {x : ℂ} (hx : x ∈ equianharmonic.lattice) : rho * x ∈ equianharmonic.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  refine PeriodPair.mem_lattice.mpr ⟨-n, m - n, ?_⟩
  simp only [equianharmonic]; push_cast
  linear_combination (-(n : ℂ) * omegaRho) * rho_sq

lemma rho_cube : rho ^ 3 = 1 := by linear_combination (rho - 1) * rho_sq

lemma rho_ne_zero : rho ≠ 0 := by
  intro h; have := rho_cube; rw [h] at this; norm_num at this

lemma rho_inv : rho⁻¹ = starRingEnd ℂ rho := by
  apply inv_eq_of_mul_eq_one_right
  have hr : starRingEnd ℂ r3 = r3 := by simp [r3, Complex.conj_ofReal]
  simp only [rho, map_div₀, map_add, map_neg, map_one, map_mul, Complex.conj_I, Complex.conj_ofNat, hr]
  linear_combination (-(r3 ^ 2) / 4) * Complex.I_sq + (1 / 4 : ℂ) * r3_sq

/-- Multiplication by `ρ` as a permutation of the lattice `Ω_ρℤ[ρ]`. -/
noncomputable def mulRho : equianharmonic.lattice ≃ equianharmonic.lattice where
  toFun l := ⟨rho * l, rho_mul_mem_lattice l.2⟩
  invFun l := ⟨rho * (rho * l), rho_mul_mem_lattice (rho_mul_mem_lattice l.2)⟩
  left_inv l := Subtype.ext (by simp only; linear_combination (l : ℂ) * rho_cube)
  right_inv l := Subtype.ext (by simp only; linear_combination (l : ℂ) * rho_cube)

/-- `ζ(ρz) = ρ̄ζ(z)` on `Ω_ρℤ[ρ]`. -/
lemma kappaOneZero_latRho : KappaOneZero latRho := by
  intro z
  show CM4E.Ext.Weierstrass.zeta equianharmonic (rho * z) = starRingEnd ℂ rho * CM4E.Ext.Weierstrass.zeta equianharmonic z
  rw [← rho_inv]
  have hρ := rho_ne_zero
  calc CM4E.Ext.Weierstrass.zeta equianharmonic (rho * z)
      = ∑' l : equianharmonic.lattice,
          CM4E.Ext.Weierstrass.zetaSummand ((mulRho l : equianharmonic.lattice) : ℂ) (rho * z) :=
        (mulRho.tsum_eq (fun l : equianharmonic.lattice =>
          CM4E.Ext.Weierstrass.zetaSummand (l : ℂ) (rho * z))).symm
    _ = ∑' l : equianharmonic.lattice, rho⁻¹ * CM4E.Ext.Weierstrass.zetaSummand (l : ℂ) z := by
        congr 1 with l
        simp only [mulRho, Equiv.coe_fn_mk, CM4E.Ext.Weierstrass.zetaSummand]
        rw [show rho * z - rho * (l : ℂ) = rho * (z - l) by ring]
        simp only [mul_inv, mul_pow, div_eq_mul_inv]
        field_simp
    _ = rho⁻¹ * CM4E.Ext.Weierstrass.zeta equianharmonic z := tsum_mul_left

/-- The quasi-period `η*((m + nα)ω) = (m + nᾱ)η₀` of a CM lattice. -/
noncomputable def etaL (L : CMLattice) (m n : ℤ) : ℂ := ((m : ℂ) + n * starRingEnd ℂ L.α) * L.η₀

/-- `K · (fibre values)`. -/
def KFib (K : Submodule ℚ ℂ) (L : CMLattice) : Set ℂ :=
  {x | ∃ (N : ℕ) (β u w : Fin N → ℂ), (∀ k, β k ∈ K) ∧ (∀ k, LogNat L.pp (etaL L) (u k) (w k)) ∧
    x = ∑ k, β k * w k}

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- Generators of the logarithms of `G_m^{2n} × Q''`. -/
def lamMGnK : Set (TF (Fin r × Fin 2) (Qn L b)) :=
  {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 i x} ∪
    {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 i x} ∪
    {v | ∃ i u w, LogNat L.pp (etaL L) u w ∧
      v = qv (((Submodule.Quotient.mk (Pi.single i u) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), theta L.α b i * w) :
        Qn L b)}

/-- The model of `G_m^{2n} × Q''` with logarithms of algebraic points of `(E^♮)^n`. -/
noncomputable def gmMGnK : GroupModel (TF (Fin r × Fin 2) (Qn L b)) :=
  gmF2 (theta L.α b) (algQn L b) (lamMGnK L b) (perGen (ι := Fin r × Fin 2) (perQn L b)) 0
    (LinearMap.snd ℂ _ ℂ) (finrank ℂ (Qn L b))

/-- **The hypothesis for the `K`-form of Theorem MG♮**: W88 §5d for `G_m^{2n} × Q''`, for every adapted basis.
Premised on `κ₁ = 0` (`KappaOneZero L`). -/
def Thm11KappaMGnK : Prop :=
  KappaOneZero L → IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmMGnK L b)

/-- A lift of `θ_h Σ β_k w_k` (`(u_k, w_k) ∈ Λ(E^♮)`) in `Q''`. -/
noncomputable def fLift (h : Fin r × Fin 2) {N : ℕ} (β u w : Fin N → ℂ) : TF (Fin r × Fin 2) (Qn L b) :=
  ∑ k, ∑ i, (coordsA L.α b (theta L.α b h * β k) i) •
    qv (((Submodule.Quotient.mk (Pi.single i (u k)) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), theta L.α b i * w k) :
      Qn L b)

variable {b}

lemma fLift_coords (hb : IsAdaptedFieldBasis L.α b) (h : Fin r × Fin 2) {N : ℕ} (β u w : Fin N → ℂ)
    (hβ : ∀ k, β k ∈ Kspan L.α b) :
    (fLift L b h β u w).1 = 0 ∧ (fLift L b h β u w).2.2 = theta L.α b h * ∑ k, β k * w k := by
  refine ⟨by simp [fLift, qv, Prod.fst_sum], ?_⟩
  simp only [fLift, qv, Prod.snd_sum, Prod.smul_snd, Rat.smul_def]
  rw [Finset.mul_sum]; congr 1; funext k
  have := coordsA_spec (hb.mul_mem _ (Submodule.subset_span ⟨h, rfl⟩) _ (hβ k))
  rw [show ∑ i, (coordsA L.α b (theta L.α b h * β k) i : ℂ) * (theta L.α b i * w k) =
      (∑ i, (coordsA L.α b (theta L.α b h * β k) i : ℂ) * theta L.α b i) * w k by
    rw [Finset.sum_mul]; congr 1; funext i; ring, this]
  ring

lemma fLift_mem (h : Fin r × Fin 2) {N : ℕ} (β u w : Fin N → ℂ)
    (hu : ∀ k, LogNat L.pp (etaL L) (u k) (w k)) :
    fLift L b h β u w ∈ Submodule.span ℚ (lamMGnK L b) :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, u k, w k, hu k, rfl⟩))

/-- **Theorem MG♮, `K`-form**: for `s = 1/(cω)`, `K ∋ c` with `[K : ℚ] ≥ 4`, there are no `x₁, x₂ ∈ K𝓛` with
`sx₁, sx₂ ∈ K𝓛 + K·(fibre values)` and `2πi, x₁, x₂` linearly independent over `K`. Hypotheses: W88 §5d for
`G_m^{2n} × Q''` (`hW`), algebraic `g₂, g₃`, and the transcendence of `ω` (Schneider). -/
theorem mgn_K (hW : Thm11KappaMGnK L) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ L.ω) (hb : IsAdaptedFieldBasis L.α b) (hr : 2 ≤ r)
    (c : ℂ) (hcK : c ∈ Kspan L.α b) (hc0 : c ≠ 0)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ KLog (Kspan L.α b))
    (hsx : ∀ k, ∃ y ∈ KLog (Kspan L.α b), ∃ e ∈ KFib (Kspan L.α b) L, (c * L.ω)⁻¹ * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Kspan L.α b → a₁ ∈ Kspan L.α b → a₂ ∈ Kspan L.α b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  choose N β ℓ hβ hℓ hxe using hx
  choose y hy e he hye using hsx
  choose N' β' ℓ' hβ' hℓ' hye' using hy
  choose N'' β'' u w hβ'' hu he' using he
  have hω := L.ω_ne_zero
  have hθalg := theta_isAlgebraic L.isAlgebraic_α hb.alg
  have hc : IsAlgebraic ℚ c := by
    obtain ⟨m, hm⟩ := exists_coords hcK
    rw [← hm, ← mem_algebraicClosure_iff]
    exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (m j)))
      (mem_algebraicClosure_iff.mpr (hθalg j))
  -- period lifts
  have hxK : ∀ h, (L.α - starRingEnd ℂ L.α) * theta L.α b h * c⁻¹ ∈ Kspan L.α b := fun h =>
    hb.mul_mem _ (hb.mul_mem _ (sub_mem (L.α_mem hb) (L.conj_α_mem hb)) _
      (Submodule.subset_span ⟨h, rfl⟩)) _ (hb.inv_mem _ hcK)
  choose m hm using fun h => exists_coords (hxK h)
  let qh : Fin r × Fin 2 → Qn L b := fun h =>
    ∑ j, (m h j : ℚ) • ((Submodule.Quotient.mk (Pi.single j L.ω) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b),
      theta L.α b j * L.η₀)
  have hlqh : ∀ h, (qh h).2 = (c * L.ω)⁻¹ * (theta L.α b h * (2 * Real.pi * I)) := by
    intro h
    simp only [qh, Prod.snd_sum, Prod.smul_snd, Rat.smul_def]
    have e : ∑ j, (m h j : ℂ) * (theta L.α b j * L.η₀) =
        L.η₀ * ((L.α - starRingEnd ℂ L.α) * theta L.α b h * c⁻¹) := by
      rw [← hm h, Finset.mul_sum]; congr 1; funext j; ring
    rw [e]
    have hleg := L.legendre
    field_simp
    linear_combination theta L.α b h * hleg
  have hωN : LogNat L.pp (etaL L) L.ω L.η₀ :=
    Or.inl ⟨1, 0, by rw [L.hω₁]; simp,
      by rw [show L.η₀ - etaL L 1 0 = 0 by simp [etaL]]; exact isAlgebraic_zero⟩
  have hqv : ∀ h, qv (qh h) = ∑ j, (m h j : ℚ) • (qv (((Submodule.Quotient.mk (Pi.single j L.ω) :
      (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), theta L.α b j * L.η₀) : Qn L b) : TF (Fin r × Fin 2) (Qn L b)) := by
    intro h
    simp [qv, qh, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
  have hqh_lam : ∀ h, qv (qh h) ∈ Submodule.span ℚ (lamMGnK L b) := by
    intro h
    rw [hqv h]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨j, L.ω, L.η₀, hωN, rfl⟩))
  have hqh_per : ∀ h, qv (qh h) ∈ Submodule.span ℚ (perGen (ι := Fin r × Fin 2) (perQn L b)) := by
    intro h
    rw [hqv h]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨_, Or.inl ⟨j, rfl⟩, rfl⟩))
  -- `s = 1/(cω)` is transcendental
  have hs : Transcendental ℚ (c * L.ω)⁻¹ := by
    intro halg
    apply hT
    have : L.ω = ((c * L.ω)⁻¹)⁻¹ / c := by field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (inv_mem (mem_algebraicClosure_iff.mpr halg)) (mem_algebraicClosure_iff.mpr hc)
  have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
    rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  refine frame2_false_K (theta L.α b) hb.indep hθalg (algQn L b) (lamMGnK L b)
    (perGen (ι := Fin r × Fin 2) (perQn L b)) 0 (LinearMap.snd ℂ _ ℂ) (finrank ℂ (Qn L b))
    (hW hκ hg₂ hg₃ r b hb) (finrank_Qn_lt L b hr) ⟨⟨0, fun _ => isAlgebraic_zero, by simp⟩, isAlgebraic_zero⟩
    (fun _ _ => isAlgebraic_zero) (fun q hq => hq.2)
    ({(0, 1)} ∪ Set.range fun j => ((Submodule.Quotient.mk (Pi.single j 1) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b),
      (0 : ℂ))) ?_ ?_ _ hs
    (fun h => tor1 h (2 * Real.pi * I) + qv (qh h)) ?_ ?_ ?_ x
    (fun k h => torLift1 (α := L.α) b h (β k) (ℓ k) + torLift2 (α := L.α) b h (β' k) (ℓ' k) +
      fLift L b h (β'' k) (u k) (w k)) ?_ ?_ hind
  · rintro q (hq | ⟨j, rfl⟩)
    · rw [Set.mem_singleton_iff] at hq; subst hq
      exact ⟨⟨0, fun _ => isAlgebraic_zero, by simp⟩, isAlgebraic_one⟩
    · refine ⟨⟨Pi.single j 1, fun k => ?_, rfl⟩, isAlgebraic_zero⟩
      simp only [Pi.single_apply]; split_ifs
      exacts [isAlgebraic_one, isAlgebraic_zero]
  · rw [eq_top_iff]
    rintro ⟨q, f⟩ -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hdec : ((Submodule.Quotient.mk v : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), f) = f • ((0, 1) : Qn L b) +
        ∑ j, v j • ((Submodule.Quotient.mk (Pi.single j 1) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), (0 : ℂ)) := by
      refine Prod.ext ?_ (by simp [Prod.snd_sum])
      simp only [Prod.fst_add, Prod.smul_fst, smul_zero, zero_add, Prod.fst_sum]
      calc (Submodule.Quotient.mk v : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b)
          = (Wphi L b).mkQ (∑ j, v j • Pi.single j 1) := by rw [sum_smul_single]; rfl
        _ = _ := by simp [map_sum, map_smul]
    rw [hdec]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl)))
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, _, h2pi, rfl⟩))) (hqh_lam h)
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩))) (hqh_per h)
  · intro h
    simp only [PsiG_apply, tor1, qv, map_add, dotL_single, map_zero,
      add_zero, zero_add, LinearMap.zero_apply, LinearMap.snd_apply, hlqh]
    simp
  · intro k h
    exact add_mem (add_mem (torLift1_mem _ (fun i x hx => Or.inl (Or.inl ⟨i, x, hx, rfl⟩)) h _ _ (hℓ k))
      (torLift2_mem _ (fun i x hx => Or.inl (Or.inr ⟨i, x, hx, rfl⟩)) h _ _ (hℓ' k)))
      (fLift_mem L h _ _ _ (hu k))
  · intro k h
    obtain ⟨a1, a2, a3⟩ := torLift1_coords (Q := Qn L b) hb h (β k) (ℓ k) (hβ k)
    obtain ⟨c1, c2, c3⟩ := torLift2_coords (Q := Qn L b) hb h (β' k) (ℓ' k) (hβ' k)
    obtain ⟨e1, e2⟩ := fLift_coords L hb h (β'' k) (u k) (w k) (hβ'' k)
    have e1a : (fLift L b h (β'' k) (u k) (w k)).1.1 = 0 := by rw [e1]; rfl
    have e1b : (fLift L b h (β'' k) (u k) (w k)).1.2 = 0 := by rw [e1]; rfl
    simp only [PsiG_apply, map_add, a1, a2, a3, c1, c2, c3, e1a, e1b,
      LinearMap.snd_apply, map_zero, LinearMap.zero_apply, add_zero, zero_add]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, add_zero]; rw [hxe k]
    · simp only [Prod.snd_add, zero_add, e2]
      rw [show (c * L.ω)⁻¹ * (theta L.α b h * x k) = theta L.α b h * ((c * L.ω)⁻¹ * x k) by ring, hye k,
        hye' k, he' k]
      ring

end CM4E.Gen
