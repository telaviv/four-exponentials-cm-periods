/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Frame2
import CM4E.Gen.MG
import CM4E.Gen.MGn

/-!
# Theorem S (strong four exponentials at CM periods), from Theorems SMG and SMG♮ of [II]

`𝓛̃ = ℚ̄ + ℚ̄𝓛` (`Ltilde`). Theorem S: for a CM lattice `L = ωℤ[α]`, `t ∈ ℚ̄ˣω ∪ ℚ̄ˣ/ω ∪ ℚ̄ˣω/π ∪ ℚ̄ˣπ/ω` and
`ℚ̄`-linearly independent `y₁, y₂`, the numbers `y₁, y₂, ty₁, ty₂` are not all in `𝓛̃`.

Both SMG and SMG♮ are instances of the frame `CM4E/Gen/Frame2.lean` (W88 §5d):
* SMG (`s = cω/π`): `G'' = G_a² × G_m^{2n} × A''` (`A'' = E^n/B_{ker ψ}`), `Q = ℂ × ℂ × T(A'')`, `μ = a₁`,
  `λ = a₂ + θᵀz`; `d₀ = 2`, `d₂ = dim A''`.
* SMG♮ (`s = cη₀/π`): `G'' = G_a × G_m^{2n} × Q''` (`Q''` of Theorem MG♮), `Q = ℂ × T(Q'')`, `μ = a`, `λ` = fibre;
  `d₀ = 1`, `d₂ = dim Q''`.
The data `y ∈ 𝓛̃` are split as algebraic part (in a `G_a` slot, resp. the fibre) plus a `K`-combination of logarithms
(written through the basis `θ` as a `ℚ`-combination in the toric slots).

Soundness facts (not checked by Lean): as for `gmMG`, `gmMGn` (`reviews/REFEREE_HYP_GEN.md`), plus: the `G_a` vectors
with algebraic entries and (for SMG♮) the fibre vectors `([0], f)`, `f ∈ ℚ̄`, are logarithms of algebraic points; and
no nonzero connected subgroup of `G''` has tangent space in `ker Ψ''` (paper [II], proof of Theorem SMG and Lemma
`lem:SMGnsub`: the subgroups are products `H × T_L × B`, resp. `T_L × R`, and `U` is the largest connected subgroup of
`G^n` with tangent space in `ker Φ`).
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.Gen

/-! ## `𝓛̃` -/

/-- `𝓛̃ = ℚ̄ + ℚ̄𝓛`. -/
def Ltilde : Set ℂ :=
  {z | ∃ (N : ℕ) (β₀ : ℂ) (β ℓ : Fin N → ℂ), IsAlgebraic ℚ β₀ ∧ (∀ k, IsAlgebraic ℚ (β k)) ∧
    (∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) ∧ z = β₀ + ∑ k, β k * ℓ k}

lemma Ltilde_add {z w : ℂ} (hz : z ∈ Ltilde) (hw : w ∈ Ltilde) : z + w ∈ Ltilde := by
  obtain ⟨N, β₀, β, ℓ, h0, hβ, hℓ, rfl⟩ := hz
  obtain ⟨M, γ₀, γ, m, g0, hγ, hm, rfl⟩ := hw
  refine ⟨N + M, β₀ + γ₀, Fin.append β γ, Fin.append ℓ m, h0.add g0, ?_, ?_, ?_⟩
  · intro k; refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [hβ, hγ]
  · intro k; refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [hℓ, hm]
  · rw [Fin.sum_univ_add]; simp; ring

lemma Ltilde_smul {c z : ℂ} (hc : IsAlgebraic ℚ c) (hz : z ∈ Ltilde) : c * z ∈ Ltilde := by
  obtain ⟨N, β₀, β, ℓ, h0, hβ, hℓ, rfl⟩ := hz
  refine ⟨N, c * β₀, fun k => c * β k, ℓ, hc.mul h0, fun k => hc.mul (hβ k), hℓ, ?_⟩
  rw [mul_add, Finset.mul_sum]; congr 1; congr 1; funext k; ring

lemma Ltilde_neg {z : ℂ} (hz : z ∈ Ltilde) : -z ∈ Ltilde := by
  simpa using Ltilde_smul (c := -1) (isAlgebraic_one.neg) hz

/-! ## Toric lifts of `K`-combinations of logarithms -/

section Lifts

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q]
variable {α : ℂ} {r : ℕ} (b : Fin r → ℂ)

/-- A lift of `θ_h Σ β_k ℓ_k` in the first toric block. -/
noncomputable def torLift1 (h : Fin r × Fin 2) {N : ℕ} (β ℓ : Fin N → ℂ) : TF (Fin r × Fin 2) Q :=
  ∑ k, ∑ i, (coordsA α b (theta α b h * β k) i) • tor1 i (ℓ k)
/-- A lift of `θ_h Σ β_k ℓ_k` in the second toric block. -/
noncomputable def torLift2 (h : Fin r × Fin 2) {N : ℕ} (β ℓ : Fin N → ℂ) : TF (Fin r × Fin 2) Q :=
  ∑ k, ∑ i, (coordsA α b (theta α b h * β k) i) • tor2 i (ℓ k)

variable {b}

lemma torLift1_coords (hb : IsAdaptedFieldBasis α b) (h : Fin r × Fin 2) {N : ℕ} (β ℓ : Fin N → ℂ)
    (hβ : ∀ k, β k ∈ Kspan α b) :
    dotL (theta α b) (torLift1 (Q := Q) (α := α) b h β ℓ).1.1 = theta α b h * ∑ k, β k * ℓ k ∧
      (torLift1 (Q := Q) (α := α) b h β ℓ).1.2 = 0 ∧ (torLift1 (Q := Q) (α := α) b h β ℓ).2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [torLift1, tor1, Prod.fst_sum, Prod.smul_fst, map_sum, map_rat_smul, dotL_single, Rat.smul_def]
    rw [Finset.mul_sum]; congr 1; funext k
    have := coordsA_spec (hb.mul_mem _ (Submodule.subset_span ⟨h, rfl⟩) _ (hβ k))
    rw [show ∑ i, (coordsA α b (theta α b h * β k) i : ℂ) * (theta α b i * ℓ k) =
        (∑ i, (coordsA α b (theta α b h * β k) i : ℂ) * theta α b i) * ℓ k by
      rw [Finset.sum_mul]; congr 1; funext i; ring, this]
    ring
  · simp [torLift1, tor1, Prod.fst_sum, Prod.snd_sum]
  · simp [torLift1, tor1, Prod.snd_sum]

lemma torLift2_coords (hb : IsAdaptedFieldBasis α b) (h : Fin r × Fin 2) {N : ℕ} (β ℓ : Fin N → ℂ)
    (hβ : ∀ k, β k ∈ Kspan α b) :
    (torLift2 (Q := Q) (α := α) b h β ℓ).1.1 = 0 ∧
      dotL (theta α b) (torLift2 (Q := Q) (α := α) b h β ℓ).1.2 = theta α b h * ∑ k, β k * ℓ k ∧
      (torLift2 (Q := Q) (α := α) b h β ℓ).2 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [torLift2, tor2, Prod.fst_sum]
  · simp only [torLift2, tor2, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, map_sum,
      map_rat_smul, dotL_single, Rat.smul_def]
    rw [Finset.mul_sum]; congr 1; funext k
    have := coordsA_spec (hb.mul_mem _ (Submodule.subset_span ⟨h, rfl⟩) _ (hβ k))
    rw [show ∑ i, (coordsA α b (theta α b h * β k) i : ℂ) * (theta α b i * ℓ k) =
        (∑ i, (coordsA α b (theta α b h * β k) i : ℂ) * theta α b i) * ℓ k by
      rw [Finset.sum_mul]; congr 1; funext i; ring, this]
    ring
  · simp [torLift2, tor2, Prod.snd_sum]

omit [Module ℂ Q] in
lemma torLift1_mem (lamS : Set (TF (Fin r × Fin 2) Q))
    (hS : ∀ i x, IsAlgebraic ℚ (Complex.exp x) → (tor1 i x : TF (Fin r × Fin 2) Q) ∈ lamS)
    (h : Fin r × Fin 2) {N : ℕ} (β ℓ : Fin N → ℂ) (hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) :
    torLift1 (Q := Q) (α := α) b h β ℓ ∈ Submodule.span ℚ lamS :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hS i _ (hℓ k)))

omit [Module ℂ Q] in
lemma torLift2_mem (lamS : Set (TF (Fin r × Fin 2) Q))
    (hS : ∀ i x, IsAlgebraic ℚ (Complex.exp x) → (tor2 i x : TF (Fin r × Fin 2) Q) ∈ lamS)
    (h : Fin r × Fin 2) {N : ℕ} (β ℓ : Fin N → ℂ) (hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) :
    torLift2 (Q := Q) (α := α) b h β ℓ ∈ Submodule.span ℚ lamS :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hS i _ (hℓ k)))

end Lifts

/-- The data of an element of `𝓛̃` with coefficients in a given set. -/
structure LtData (z : ℂ) where
  N : ℕ
  β₀ : ℂ
  β : Fin N → ℂ
  ℓ : Fin N → ℂ
  h0 : IsAlgebraic ℚ β₀
  hβ : ∀ k, IsAlgebraic ℚ (β k)
  hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))
  eq : z = β₀ + ∑ k, β k * ℓ k

lemma Ltilde.nonempty_data {z : ℂ} (hz : z ∈ Ltilde) : Nonempty (LtData z) := by
  obtain ⟨N, β₀, β, ℓ, h0, hβ, hℓ, e⟩ := hz
  exact ⟨⟨N, β₀, β, ℓ, h0, hβ, hℓ, e⟩⟩

/-! ## Theorem SMG: `G_a² × G_m^{2n} × A''` -/

section SMG

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- `T(G_a² × A'') = ℂ × ℂ × ℂ^n/ℂ·ker ψ`. -/
abbrev QS := ℂ × ℂ × Qm L b

/-- `μ = a₁`. -/
noncomputable def muS : QS L b →ₗ[ℂ] ℂ := LinearMap.fst ℂ ℂ _
/-- `λ = a₂ + θᵀz`. -/
noncomputable def lamS : QS L b →ₗ[ℂ] ℂ :=
  LinearMap.fst ℂ ℂ _ ∘ₗ LinearMap.snd ℂ ℂ _ + lamM L b ∘ₗ LinearMap.snd ℂ ℂ _ ∘ₗ LinearMap.snd ℂ ℂ _

lemma muS_apply (q : QS L b) : muS L b q = q.1 := rfl
lemma lamS_apply (q : QS L b) : lamS L b q = q.2.1 + lamM L b q.2.2 := rfl

/-- The `ℚ̄`-structure. -/
def algQS (q : QS L b) : Prop := IsAlgebraic ℚ q.1 ∧ IsAlgebraic ℚ q.2.1 ∧ algQm L b q.2.2

/-- `(0, 0, q)`. -/
def inQS (q : Qm L b) : QS L b := (0, 0, q)

/-- Logarithms: toric logarithms, algebraic `G_a` vectors, periods of `A''`. -/
def lamSS : Set (TF (Fin r × Fin 2) (QS L b)) :=
  {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 i x} ∪
    {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 i x} ∪
    {v | ∃ a a' : ℂ, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ a' ∧ v = qv ((a, a', 0) : QS L b)} ∪
    (fun q => qv (inQS L b q)) '' perQm L b

/-- Periods: `2πi` in a toric slot, periods of `A''`. -/
noncomputable def perSS : Set (TF (Fin r × Fin 2) (QS L b)) :=
  Set.range (fun j : Fin r × Fin 2 => (tor1 j (2 * Real.pi * I) : TF (Fin r × Fin 2) (QS L b))) ∪
    Set.range (fun j : Fin r × Fin 2 => (tor2 j (2 * Real.pi * I) : TF (Fin r × Fin 2) (QS L b))) ∪
    (fun q => qv (inQS L b q)) '' perQm L b

/-- The model of `G_a² × G_m^{2n} × A''` (`d₂ = dim A''`). -/
noncomputable def gmSMG : GroupModel (TF (Fin r × Fin 2) (QS L b)) :=
  gmF2 (theta L.α b) (algQS L b) (lamSS L b) (perSS L b) (muS L b) (lamS L b) (finrank ℂ (Qm L b))

/-- **The hypothesis for Theorem SMG**: W88 §5d for `G_a² × G_m^{2n} × A''`, every adapted basis. -/
def Thm11KappaSMG : Prop :=
  IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmSMG L b)

lemma inQS_mem_span (S : Set (TF (Fin r × Fin 2) (QS L b)))
    (hS : (fun q => qv (inQS L b q)) '' perQm L b ⊆ S) {q : Qm L b}
    (hq : q ∈ Submodule.span ℚ (perQm L b)) : qv (inQS L b q) ∈ Submodule.span ℚ S := by
  let f : Qm L b →ₗ[ℚ] TF (Fin r × Fin 2) (QS L b) :=
    LinearMap.inr ℚ _ _ ∘ₗ LinearMap.inr ℚ ℂ _ ∘ₗ LinearMap.inr ℚ ℂ _
  have : Submodule.map f (Submodule.span ℚ (perQm L b)) ≤ Submodule.span ℚ S := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨q', hq', rfl⟩
    exact Submodule.subset_span (hS ⟨q', hq', rfl⟩)
  exact this ⟨q, hq, rfl⟩

/-- **Theorem SMG** (data in `𝓛̃`): for `s = cω/π` and `y₁, y₂ ∈ 𝓛̃` with `2πi, y₁, y₂` linearly independent over
`ℚ̄`, `sy₁, sy₂` are not both in `𝓛̃`. -/
theorem smg_false (hW : Thm11KappaSMG L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ (L.ω / Real.pi)) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (y : Fin 2 → ℂ) (hy : ∀ k, y k ∈ Ltilde) (hsy : ∀ k, c * L.ω / Real.pi * y k ∈ Ltilde)
    (hind3 : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * (2 * Real.pi * I) + a₁ * y 0 + a₂ * y 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  set s := c * L.ω / Real.pi with hsdef
  have dY : ∀ k, LtData (y k) := fun k => (Ltilde.nonempty_data (hy k)).some
  have dS : ∀ k, LtData (s * y k) := fun k => (Ltilde.nonempty_data (hsy k)).some
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  classical
  let Sset : Finset ℂ := {c, I} ∪ (Finset.univ.image (dY 0).β ∪ Finset.univ.image (dY 1).β ∪
    Finset.univ.image (dS 0).β ∪ Finset.univ.image (dS 1).β)
  obtain ⟨r, hr, b, hb, hS⟩ := exists_adapted_basis L.α L.isAlgebraic_α L.him.ne' ⟨L.p, L.q, L.hquad⟩
    Sset (by
      intro z hz
      simp only [Sset, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and] at hz
      rcases hz with (rfl | rfl) | (((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨k, rfl⟩)
      exacts [hc, hI, (dY 0).hβ k, (dY 1).hβ k, (dS 0).hβ k, (dS 1).hβ k])
  have hcK : c ∈ Kspan L.α b := hS c (by simp [Sset])
  have hIK : I ∈ Kspan L.α b := hS I (by simp [Sset])
  have hβY : ∀ k j, (dY k).β j ∈ Kspan L.α b := by
    intro k j; fin_cases k
    · exact hS _ (by simp [Sset])
    · exact hS _ (by simp [Sset])
  have hβS : ∀ k j, (dS k).β j ∈ Kspan L.α b := by
    intro k j; fin_cases k
    · exact hS _ (by simp [Sset])
    · exact hS _ (by simp [Sset])
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθalg := theta_isAlgebraic L.isAlgebraic_α hb.alg
  have hr1 : 1 ≤ r := by omega
  -- period lifts
  have h2 : (2 : ℂ) ∈ Kspan L.α b := by
    have := Submodule.smul_mem _ (2 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hxK : ∀ h, 2 * I * c * theta L.α b h ∈ Kspan L.α b := fun h =>
    hb.mul_mem _ (hb.mul_mem _ (hb.mul_mem _ h2 _ hIK) _ hcK) _ (Submodule.subset_span ⟨h, rfl⟩)
  let qh : Fin r × Fin 2 → Qm L b := fun h =>
    ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℚ) • (Submodule.Quotient.mk (Pi.single j L.ω) : Qm L b)
  have hqh : ∀ h, qh h ∈ Submodule.span ℚ (perQm L b) := fun h =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨j, rfl⟩))
  have hlqh : ∀ h, lamM L b (qh h) = s * (theta L.α b h * (2 * Real.pi * I)) := by
    intro h
    simp only [qh, map_sum, map_rat_smul, lamM_mk, dotL_single, Rat.smul_def]
    rw [show ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℂ) * (theta L.α b j * L.ω) =
        (∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℂ) * theta L.α b j) * L.ω by
      rw [Finset.sum_mul]; congr 1; funext j; ring, coordsA_spec (hxK h), hsdef]
    field_simp
  -- `s` transcendental
  have hs : Transcendental ℚ s := by
    intro halg
    apply hT
    have : L.ω / Real.pi = s / c := by rw [hsdef]; field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (mem_algebraicClosure_iff.mpr halg) (mem_algebraicClosure_iff.mpr hc)
  have hlamMalg : ∀ q, algQm L b q → IsAlgebraic ℚ (lamM L b q) := by
    rintro q ⟨v, hv, rfl⟩
    rw [lamM_mk, dotL_apply, ← mem_algebraicClosure_iff]
    exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
      (mem_algebraicClosure_iff.mpr (hv j))
  refine frame2_false (theta L.α b) hb.indep hθalg (algQS L b) (lamSS L b) (perSS L b) (muS L b)
    (lamS L b) (finrank ℂ (Qm L b)) (hW hg₂ hg₃ r b hb) (finrank_Qm_lt L b hr1)
    ⟨isAlgebraic_zero, isAlgebraic_zero, ⟨0, fun _ => isAlgebraic_zero, by simp⟩⟩
    (fun q hq => hq.1) (fun q hq => by rw [lamS_apply]; exact hq.2.1.add (hlamMalg _ hq.2.2))
    ({(1, 0, 0), (0, 1, 0)} ∪ Set.range fun j => ((0 : ℂ), (0 : ℂ),
      (Submodule.Quotient.mk (Pi.single j 1) : Qm L b))) ?_ ?_ s hs
    (fun h => tor1 h (2 * Real.pi * I) + qv (inQS L b (qh h))) ?_ ?_ ?_ y
    (fun k h => torLift1 (α := L.α) b h (dY k).β (dY k).ℓ + torLift2 (α := L.α) b h (dS k).β (dS k).ℓ +
      qv ((theta L.α b h * (dY k).β₀, theta L.α b h * (dS k).β₀, 0) : QS L b)) ?_ ?_ hind3
  · rintro q ((rfl | rfl) | ⟨j, rfl⟩)
    · exact ⟨isAlgebraic_one, isAlgebraic_zero, ⟨0, fun _ => isAlgebraic_zero, by simp⟩⟩
    · exact ⟨isAlgebraic_zero, isAlgebraic_one, ⟨0, fun _ => isAlgebraic_zero, by simp⟩⟩
    · refine ⟨isAlgebraic_zero, isAlgebraic_zero, ⟨Pi.single j 1, fun k => ?_, rfl⟩⟩
      simp only [Pi.single_apply]; split_ifs
      exacts [isAlgebraic_one, isAlgebraic_zero]
  · rw [eq_top_iff]
    rintro ⟨a, a', q⟩ -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hdec : ((a, a', Submodule.Quotient.mk v) : QS L b) =
        a • ((1, 0, 0) : QS L b) + a' • ((0, 1, 0) : QS L b) +
          ∑ j, v j • ((0 : ℂ), (0 : ℂ), (Submodule.Quotient.mk (Pi.single j 1) : Qm L b)) := by
      refine Prod.ext (by simp [Prod.fst_sum]) (Prod.ext (by simp [Prod.fst_sum, Prod.snd_sum]) ?_)
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sum, smul_zero, zero_add, Prod.smul_mk]
      calc (Submodule.Quotient.mk v : Qm L b)
          = (Wpsi L b).mkQ (∑ j, v j • Pi.single j 1) := by rw [sum_smul_single]; rfl
        _ = _ := by simp [map_sum, map_smul]
    rw [hdec]
    refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl rfl))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr rfl))))) ?_
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
  · intro h
    have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
      rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨h, _, h2pi, rfl⟩))))
      (inQS_mem_span L b _ (fun v hv => Or.inr hv) (hqh h))
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩)))
      (inQS_mem_span L b _ (fun v hv => Or.inr hv) (hqh h))
  · intro h
    simp only [PsiG_apply, tor1, qv, inQS, Prod.fst_add, Prod.snd_add, map_add, dotL_single, map_zero,
      muS_apply, lamS_apply, add_zero, zero_add, hlqh]
    simp
  · intro k h
    refine add_mem (add_mem (torLift1_mem _ (fun i x hx => Or.inl (Or.inl (Or.inl ⟨i, x, hx, rfl⟩))) h _ _
      (dY k).hℓ) (torLift2_mem _ (fun i x hx => Or.inl (Or.inl (Or.inr ⟨i, x, hx, rfl⟩))) h _ _
      (dS k).hℓ)) (Submodule.subset_span (Or.inl (Or.inr ⟨_, _, (hθalg h).mul (dY k).h0,
        (hθalg h).mul (dS k).h0, rfl⟩)))
  · intro k h
    obtain ⟨a1, a2, a3⟩ := torLift1_coords (Q := QS L b) hb h (dY k).β (dY k).ℓ (hβY k)
    obtain ⟨c1, c2, c3⟩ := torLift2_coords (Q := QS L b) hb h (dS k).β (dS k).ℓ (hβS k)
    simp only [PsiG_apply, qv, Prod.fst_add, Prod.snd_add, map_add, a1, a2, a3, c1, c2, c3, map_zero,
      muS_apply, lamS_apply, add_zero, zero_add]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero, zero_add, add_zero, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor
    · linear_combination -(theta L.α b h) * (dY k).eq
    · linear_combination -(theta L.α b h) * (dS k).eq

end SMG

/-! ## Theorem SMG♮: `G_a × G_m^{2n} × Q''` -/

section SMGn

variable (L : CMLattice) {r : ℕ} (b : Fin r → ℂ)

/-- `T(G_a × Q'') = ℂ × (ℂ^n/ℂ·ker φ × ℂ)`. -/
abbrev QSn := ℂ × Qn L b

/-- `μ = a`. -/
noncomputable def muSn : QSn L b →ₗ[ℂ] ℂ := LinearMap.fst ℂ ℂ _
/-- `λ` = the fibre coordinate. -/
noncomputable def lamSn : QSn L b →ₗ[ℂ] ℂ := LinearMap.snd ℂ _ ℂ ∘ₗ LinearMap.snd ℂ ℂ _

lemma muSn_apply (q : QSn L b) : muSn L b q = q.1 := rfl
lemma lamSn_apply (q : QSn L b) : lamSn L b q = q.2.2 := rfl

/-- The `ℚ̄`-structure. -/
def algQSn (q : QSn L b) : Prop := IsAlgebraic ℚ q.1 ∧ algQn L b q.2

/-- Logarithms: toric logarithms, algebraic `G_a` vectors and fibre values, periods of `Q''`. -/
def lamSSn : Set (TF (Fin r × Fin 2) (QSn L b)) :=
  {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor1 i x} ∪
    {v | ∃ i x, IsAlgebraic ℚ (Complex.exp x) ∧ v = tor2 i x} ∪
    {v | ∃ a f : ℂ, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ f ∧ v = qv ((a, (0, f)) : QSn L b)} ∪
    (fun q => qv (((0 : ℂ), q) : QSn L b)) '' perQn L b

/-- Periods: `2πi` in a toric slot, periods of `Q''`. -/
noncomputable def perSSn : Set (TF (Fin r × Fin 2) (QSn L b)) :=
  Set.range (fun j : Fin r × Fin 2 => (tor1 j (2 * Real.pi * I) : TF (Fin r × Fin 2) (QSn L b))) ∪
    Set.range (fun j : Fin r × Fin 2 => (tor2 j (2 * Real.pi * I) : TF (Fin r × Fin 2) (QSn L b))) ∪
    (fun q => qv (((0 : ℂ), q) : QSn L b)) '' perQn L b

/-- The model of `G_a × G_m^{2n} × Q''` (`d₂ = dim Q''`). -/
noncomputable def gmSMGn : GroupModel (TF (Fin r × Fin 2) (QSn L b)) :=
  gmF2 (theta L.α b) (algQSn L b) (lamSSn L b) (perSSn L b) (muSn L b) (lamSn L b) (finrank ℂ (Qn L b))

/-- **The hypothesis for Theorem SMG♮**: W88 §5d for `G_a × G_m^{2n} × Q''`, every adapted basis. Premised on
`KappaOneZero L` (as `Thm11KappaMGn`): the periods `perQn` use `η₀`, which is the quasi-period `η(ω)` of the actual
`E^♮` exactly when `κ₁ = 0`; proved for `ϖℤ[i]`, `Ω_ρℤ[ρ]`. -/
def Thm11KappaSMGn : Prop :=
  KappaOneZero L → IsAlgebraic ℚ L.pp.g₂ → IsAlgebraic ℚ L.pp.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis L.α b → HyperplaneKappa (gmSMGn L b)

lemma inQSn_mem_span (S : Set (TF (Fin r × Fin 2) (QSn L b)))
    (hS : (fun q => qv (((0 : ℂ), q) : QSn L b)) '' perQn L b ⊆ S) {q : Qn L b}
    (hq : q ∈ Submodule.span ℚ (perQn L b)) : qv (((0 : ℂ), q) : QSn L b) ∈ Submodule.span ℚ S := by
  let f : Qn L b →ₗ[ℚ] TF (Fin r × Fin 2) (QSn L b) := LinearMap.inr ℚ _ _ ∘ₗ LinearMap.inr ℚ ℂ _
  have : Submodule.map f (Submodule.span ℚ (perQn L b)) ≤ Submodule.span ℚ S := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨q', hq', rfl⟩
    exact Submodule.subset_span (hS ⟨q', hq', rfl⟩)
  exact this ⟨q, hq, rfl⟩

/-- **Theorem SMG♮** (data in `𝓛̃`): for `s = cη₀/π` and `y₁, y₂ ∈ 𝓛̃` with `2πi, y₁, y₂` linearly independent over
`ℚ̄`, `sy₁, sy₂` are not both in `𝓛̃`. -/
theorem smgn_false (hW : Thm11KappaSMGn L) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ L.ω) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (y : Fin 2 → ℂ) (hy : ∀ k, y k ∈ Ltilde) (hsy : ∀ k, c * L.η₀ / Real.pi * y k ∈ Ltilde)
    (hind3 : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * (2 * Real.pi * I) + a₁ * y 0 + a₂ * y 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  set s := c * L.η₀ / Real.pi with hsdef
  have dY : ∀ k, LtData (y k) := fun k => (Ltilde.nonempty_data (hy k)).some
  have dS : ∀ k, LtData (s * y k) := fun k => (Ltilde.nonempty_data (hsy k)).some
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  classical
  let Sset : Finset ℂ := {c, I} ∪ (Finset.univ.image (dY 0).β ∪ Finset.univ.image (dY 1).β ∪
    Finset.univ.image (dS 0).β ∪ Finset.univ.image (dS 1).β)
  obtain ⟨r, hr, b, hb, hS⟩ := exists_adapted_basis L.α L.isAlgebraic_α L.him.ne' ⟨L.p, L.q, L.hquad⟩
    Sset (by
      intro z hz
      simp only [Sset, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
        Finset.mem_univ, true_and] at hz
      rcases hz with (rfl | rfl) | (((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨k, rfl⟩)
      exacts [hc, hI, (dY 0).hβ k, (dY 1).hβ k, (dS 0).hβ k, (dS 1).hβ k])
  have hcK : c ∈ Kspan L.α b := hS c (by simp [Sset])
  have hIK : I ∈ Kspan L.α b := hS I (by simp [Sset])
  have hβY : ∀ k j, (dY k).β j ∈ Kspan L.α b := by
    intro k j; fin_cases k
    · exact hS _ (by simp [Sset])
    · exact hS _ (by simp [Sset])
  have hβS : ∀ k j, (dS k).β j ∈ Kspan L.α b := by
    intro k j; fin_cases k
    · exact hS _ (by simp [Sset])
    · exact hS _ (by simp [Sset])
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθalg := theta_isAlgebraic L.isAlgebraic_α hb.alg
  -- period lifts
  have h2 : (2 : ℂ) ∈ Kspan L.α b := by
    have := Submodule.smul_mem _ (2 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hxK : ∀ h, 2 * I * c * theta L.α b h ∈ Kspan L.α b := fun h =>
    hb.mul_mem _ (hb.mul_mem _ (hb.mul_mem _ h2 _ hIK) _ hcK) _ (Submodule.subset_span ⟨h, rfl⟩)
  let qh : Fin r × Fin 2 → Qn L b := fun h =>
    ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℚ) •
      ((Submodule.Quotient.mk (Pi.single j L.ω) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), theta L.α b j * L.η₀)
  have hqh : ∀ h, qh h ∈ Submodule.span ℚ (perQn L b) := fun h =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨j, rfl⟩))
  have hlqh : ∀ h, (qh h).2 = s * (theta L.α b h * (2 * Real.pi * I)) := by
    intro h
    simp only [qh, Prod.snd_sum, Prod.smul_snd, Rat.smul_def]
    rw [show ∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℂ) * (theta L.α b j * L.η₀) =
        (∑ j, (coordsA L.α b (2 * I * c * theta L.α b h) j : ℂ) * theta L.α b j) * L.η₀ by
      rw [Finset.sum_mul]; congr 1; funext j; ring, coordsA_spec (hxK h), hsdef]
    field_simp
  -- `s` transcendental (Legendre: `η₀/π ∈ ℚ̄ˣ/ω`)
  have hs : Transcendental ℚ s := by
    intro halg
    apply hT
    have hleg := L.legendre
    have hd : L.α - starRingEnd ℂ L.α ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hleg
      exact (by simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * (Real.pi : ℂ) * I) ≠ 0) hleg.symm
    have hs0 : s ≠ 0 := by
      rw [hsdef]
      refine div_ne_zero (mul_ne_zero hc0 ?_) hpi
      intro h0; rw [h0, mul_zero, zero_mul] at hleg
      exact (by simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * (Real.pi : ℂ) * I) ≠ 0) hleg.symm
    have : L.ω = 2 * I * c / (s * (L.α - starRingEnd ℂ L.α)) := by
      rw [eq_div_iff (mul_ne_zero hs0 hd), hsdef]
      field_simp
      linear_combination hleg
    rw [this, ← mem_algebraicClosure_iff]
    have hαc : L.α - starRingEnd ℂ L.α ∈ algebraicClosure ℚ ℂ := by
      rw [L.conj_α]
      exact sub_mem (mem_algebraicClosure_iff.mpr L.isAlgebraic_α)
        (sub_mem (by simp) (mem_algebraicClosure_iff.mpr L.isAlgebraic_α))
    exact div_mem (mul_mem (mul_mem (by simp) (mem_algebraicClosure_iff.mpr hI))
      (mem_algebraicClosure_iff.mpr hc)) (mul_mem (mem_algebraicClosure_iff.mpr halg) hαc)
  refine frame2_false (theta L.α b) hb.indep hθalg (algQSn L b) (lamSSn L b) (perSSn L b) (muSn L b)
    (lamSn L b) (finrank ℂ (Qn L b)) (hW hκ hg₂ hg₃ r b hb) (finrank_Qn_lt L b hr)
    ⟨isAlgebraic_zero, ⟨0, fun _ => isAlgebraic_zero, by simp⟩, isAlgebraic_zero⟩
    (fun q hq => hq.1) (fun q hq => hq.2.2)
    ({(1, 0), (0, (0, 1))} ∪ Set.range fun j => ((0 : ℂ),
      ((Submodule.Quotient.mk (Pi.single j 1) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b), (0 : ℂ)))) ?_ ?_ s hs
    (fun h => tor1 h (2 * Real.pi * I) + qv (((0 : ℂ), qh h) : QSn L b)) ?_ ?_ ?_ y
    (fun k h => torLift1 (α := L.α) b h (dY k).β (dY k).ℓ + torLift2 (α := L.α) b h (dS k).β (dS k).ℓ +
      qv ((theta L.α b h * (dY k).β₀, (0, theta L.α b h * (dS k).β₀)) : QSn L b)) ?_ ?_ hind3
  · rintro q ((rfl | rfl) | ⟨j, rfl⟩)
    · exact ⟨isAlgebraic_one, ⟨0, fun _ => isAlgebraic_zero, by simp⟩, isAlgebraic_zero⟩
    · exact ⟨isAlgebraic_zero, ⟨0, fun _ => isAlgebraic_zero, by simp⟩, isAlgebraic_one⟩
    · refine ⟨isAlgebraic_zero, ⟨Pi.single j 1, fun k => ?_, rfl⟩, isAlgebraic_zero⟩
      simp only [Pi.single_apply]; split_ifs
      exacts [isAlgebraic_one, isAlgebraic_zero]
  · rw [eq_top_iff]
    rintro ⟨a, q, f⟩ -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hdec : ((a, (Submodule.Quotient.mk v, f)) : QSn L b) =
        a • ((1, 0) : QSn L b) + f • (((0 : ℂ), (0, 1)) : QSn L b) +
          ∑ j, v j • ((0 : ℂ), ((Submodule.Quotient.mk (Pi.single j 1) : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b),
            (0 : ℂ))) := by
      refine Prod.ext (by simp [Prod.fst_sum]) (Prod.ext ?_ (by simp [Prod.snd_sum]))
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sum, Prod.fst_add, Prod.smul_fst, Prod.fst_sum,
        smul_zero, zero_add, Prod.snd_zero, Prod.fst_zero]
      calc (Submodule.Quotient.mk v : (Fin r × Fin 2 → ℂ) ⧸ Wphi L b)
          = (Wphi L b).mkQ (∑ j, v j • Pi.single j 1) := by rw [sum_smul_single]; rfl
        _ = _ := by simp [map_sum, map_smul]
    rw [hdec]
    refine add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl rfl))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr rfl))))) ?_
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
  · intro h
    have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
      rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨h, _, h2pi, rfl⟩))))
      (inQSn_mem_span L b _ (fun v hv => Or.inr hv) (hqh h))
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩)))
      (inQSn_mem_span L b _ (fun v hv => Or.inr hv) (hqh h))
  · intro h
    simp only [PsiG_apply, tor1, qv, Prod.fst_add, Prod.snd_add, map_add, dotL_single, map_zero,
      muSn_apply, lamSn_apply, add_zero, zero_add, hlqh]
    simp
  · intro k h
    refine add_mem (add_mem (torLift1_mem _ (fun i x hx => Or.inl (Or.inl (Or.inl ⟨i, x, hx, rfl⟩))) h _ _
      (dY k).hℓ) (torLift2_mem _ (fun i x hx => Or.inl (Or.inl (Or.inr ⟨i, x, hx, rfl⟩))) h _ _
      (dS k).hℓ)) (Submodule.subset_span (Or.inl (Or.inr ⟨_, _, (hθalg h).mul (dY k).h0,
        (hθalg h).mul (dS k).h0, rfl⟩)))
  · intro k h
    obtain ⟨a1, a2, a3⟩ := torLift1_coords (Q := QSn L b) hb h (dY k).β (dY k).ℓ (hβY k)
    obtain ⟨c1, c2, c3⟩ := torLift2_coords (Q := QSn L b) hb h (dS k).β (dS k).ℓ (hβS k)
    simp only [PsiG_apply, qv, Prod.fst_add, Prod.snd_add, map_add, a1, a2, a3, c1, c2, c3, map_zero,
      muSn_apply, lamSn_apply, add_zero, zero_add]
    simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero, zero_add, add_zero, Prod.mk_add_mk,
      Prod.mk.injEq]
    constructor
    · linear_combination -(theta L.α b h) * (dY k).eq
    · linear_combination -(theta L.α b h) * (dS k).eq

end SMGn

/-! ## Theorem S -/

section ThmS

variable (L : CMLattice)

/-- **Named input ([II], Lemma `lem:notLt`; Wüstholz 1989).** The period `ω` and the quasi-period `η₀` are not in
`𝓛̃ = ℚ̄ + ℚ̄𝓛` (analytic subgroup theorem on `G_a × G_m^N × E`, resp. `× E^♮`). -/
def NotLtilde : Prop := L.ω ∉ Ltilde ∧ L.η₀ ∉ Ltilde

lemma isAlg_div {a b : ℂ} (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) : IsAlgebraic ℚ (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

lemma two_pi_I_ne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The core of Theorem S for one slope: if `s · 2πi ∈ ℚ̄ˣ P` with `P ∉ 𝓛̃`, and the generic case is excluded (`hgen`),
then `ℚ̄`-independent `z₁, z₂ ∈ 𝓛̃` cannot have `s z₁, s z₂ ∈ 𝓛̃`. -/
lemma thmS_core {s P d : ℂ} (hd : IsAlgebraic ℚ d) (hd0 : d ≠ 0) (hsP : s * (2 * Real.pi * I) = d * P)
    (hP : P ∉ Ltilde) (z : Fin 2 → ℂ) (hz : ∀ k, z k ∈ Ltilde) (hsz : ∀ k, s * z k ∈ Ltilde)
    (hind : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * z 0 + a₂ * z 1 = 0 → a₁ = 0 ∧ a₂ = 0)
    (hgen : (∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * (2 * Real.pi * I) + a₁ * z 0 + a₂ * z 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) → False) : False := by
  apply hgen
  intro a₀ a₁ a₂ h₀ h₁ h₂ hrel
  by_cases ha0 : a₀ = 0
  · subst ha0
    have := hind a₁ a₂ h₁ h₂ (by linear_combination hrel)
    exact ⟨rfl, this⟩
  · exfalso
    apply hP
    have h2pi : 2 * (Real.pi : ℂ) * I = -(a₁ / a₀) * z 0 + -(a₂ / a₀) * z 1 := by
      field_simp; linear_combination hrel
    have hmem : s * (2 * Real.pi * I) ∈ Ltilde := by
      rw [h2pi, mul_add, mul_left_comm, mul_left_comm s]
      exact Ltilde_add (Ltilde_smul ((isAlg_div h₁ h₀).neg) (hsz 0)) (Ltilde_smul ((isAlg_div h₂ h₀).neg) (hsz 1))
    have : P = d⁻¹ * (s * (2 * Real.pi * I)) := by rw [hsP]; field_simp
    rw [this]
    exact Ltilde_smul hd.inv hmem

/-- **Theorem S** ([II], Theorem S) for a CM lattice: for `t ∈ ℚ̄ˣω ∪ ℚ̄ˣ/ω ∪ ℚ̄ˣω/π ∪ ℚ̄ˣπ/ω` and `ℚ̄`-linearly
independent `y₁, y₂`, the numbers `y₁, y₂, ty₁, ty₂` are not all in `𝓛̃`. Hypotheses: W88 §5d for the groups of
SMG and SMG♮ (`hWa`, `hWb`), `κ₁ = 0` (`hκ`), algebraic `g₂, g₃`, Schneider (`ω`, `ω/π` transcendental), and `NotLtilde L`. -/
theorem thmS (hWa : Thm11KappaSMG L) (hWb : Thm11KappaSMGn L) (hκ : KappaOneZero L)
    (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃) (hTω : Transcendental ℚ L.ω) (hTωπ : Transcendental ℚ (L.ω / Real.pi))
    (hNot : NotLtilde L) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (t : ℂ)
    (ht : t = c * L.ω ∨ t = c / L.ω ∨ t = c * L.ω / Real.pi ∨ t = c * Real.pi / L.ω)
    (y₁ y₂ : ℂ) (hind : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * y₁ + a₂ * y₂ = 0 →
      a₁ = 0 ∧ a₂ = 0) :
    ¬ (y₁ ∈ Ltilde ∧ y₂ ∈ Ltilde ∧ t * y₁ ∈ Ltilde ∧ t * y₂ ∈ Ltilde) := by
  rintro ⟨hy₁, hy₂, hty₁, hty₂⟩
  have hω := L.ω_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hleg := L.legendre
  have hd : L.α - starRingEnd ℂ L.α ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hleg; exact two_pi_I_ne hleg.symm
  have hη : L.η₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_mul] at hleg; exact two_pi_I_ne hleg.symm
  have hαd : IsAlgebraic ℚ (L.α - starRingEnd ℂ L.α) := by
    rw [L.conj_α, ← mem_algebraicClosure_iff]
    exact sub_mem (mem_algebraicClosure_iff.mpr L.isAlgebraic_α)
      (sub_mem (by simp) (mem_algebraicClosure_iff.mpr L.isAlgebraic_α))
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  have halg2I : IsAlgebraic ℚ (2 * I) := by
    rw [← mem_algebraicClosure_iff]; exact mul_mem (by simp) (mem_algebraicClosure_iff.mpr hI)
  have h2I0 : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  -- the data and their independence after scaling by `t ≠ 0`
  have hy : ∀ k, ![y₁, y₂] k ∈ Ltilde := by intro k; fin_cases k <;> simpa
  have hty : ∀ k, t * ![y₁, y₂] k ∈ Ltilde := by intro k; fin_cases k <;> simpa
  have hind' : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₁ * ![y₁, y₂] 0 + a₂ * ![y₁, y₂] 1 = 0 → a₁ = 0 ∧ a₂ = 0 := by simpa using hind
  have hindt : t ≠ 0 → ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₁ * (t * ![y₁, y₂] 0) + a₂ * (t * ![y₁, y₂] 1) = 0 → a₁ = 0 ∧ a₂ = 0 := by
    intro ht0 a₁ a₂ h₁ h₂ h
    refine hind a₁ a₂ h₁ h₂ ?_
    have : t * (a₁ * y₁ + a₂ * y₂) = 0 := by simp at h; linear_combination h
    exact (mul_eq_zero.mp this).resolve_left ht0
  -- SMG at `s = c'ω/π` and SMG♮ at `s = c'η₀/π`, applied to `z` (with `s z ∈ 𝓛̃`)
  have caseA : ∀ c' : ℂ, IsAlgebraic ℚ c' → c' ≠ 0 → ∀ z : Fin 2 → ℂ, (∀ k, z k ∈ Ltilde) →
      (∀ k, c' * L.ω / Real.pi * z k ∈ Ltilde) →
      (∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * z 0 + a₂ * z 1 = 0 → a₁ = 0 ∧ a₂ = 0) →
      False := fun c' hc' hc0' z hz hsz hindz =>
    thmS_core (halg2I.mul hc') (mul_ne_zero h2I0 hc0') (by field_simp) hNot.1 z hz hsz hindz
      (smg_false L hWa hg₂ hg₃ hTωπ c' hc' hc0' z hz hsz)
  have caseB : ∀ c' : ℂ, IsAlgebraic ℚ c' → c' ≠ 0 → ∀ z : Fin 2 → ℂ, (∀ k, z k ∈ Ltilde) →
      (∀ k, c' * L.η₀ / Real.pi * z k ∈ Ltilde) →
      (∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * z 0 + a₂ * z 1 = 0 → a₁ = 0 ∧ a₂ = 0) →
      False := fun c' hc' hc0' z hz hsz hindz =>
    thmS_core (halg2I.mul hc') (mul_ne_zero h2I0 hc0') (by field_simp) hNot.2 z hz hsz hindz
      (smgn_false L hWb hκ hg₂ hg₃ hTω c' hc' hc0' z hz hsz)
  rcases ht with rfl | rfl | rfl | rfl
  · -- `t = cω`: `1/t = c''η₀/π`, data `t y`
    have ht0 : c * L.ω ≠ 0 := mul_ne_zero hc0 hω
    refine caseB ((L.α - starRingEnd ℂ L.α) / (2 * I * c)) (isAlg_div hαd (halg2I.mul hc))
      (div_ne_zero hd (mul_ne_zero h2I0 hc0)) (fun k => c * L.ω * ![y₁, y₂] k) hty (fun k => ?_)
      (hindt ht0)
    have : (L.α - starRingEnd ℂ L.α) / (2 * I * c) * L.η₀ / Real.pi * (c * L.ω * ![y₁, y₂] k) =
        ![y₁, y₂] k := by
      field_simp; linear_combination (![y₁, y₂] k) * hleg
    rw [this]; exact hy k
  · -- `t = c/ω = c'η₀/π`
    refine caseB (c * (L.α - starRingEnd ℂ L.α) / (2 * I)) (isAlg_div (hc.mul hαd) halg2I)
      (div_ne_zero (mul_ne_zero hc0 hd) h2I0) ![y₁, y₂] hy (fun k => ?_) hind'
    have : c * (L.α - starRingEnd ℂ L.α) / (2 * I) * L.η₀ / Real.pi = c / L.ω := by
      field_simp; linear_combination hleg
    rw [this]; exact hty k
  · -- `t = cω/π`
    exact caseA c hc hc0 ![y₁, y₂] hy hty hind'
  · -- `t = cπ/ω`: `1/t = (1/c)ω/π`, data `t y`
    have ht0 : c * Real.pi / L.ω ≠ 0 := div_ne_zero (mul_ne_zero hc0 hpi) hω
    refine caseA c⁻¹ hc.inv (inv_ne_zero hc0) (fun k => c * Real.pi / L.ω * ![y₁, y₂] k) hty (fun k => ?_)
      (hindt ht0)
    have : c⁻¹ * L.ω / Real.pi * (c * Real.pi / L.ω * ![y₁, y₂] k) = ![y₁, y₂] k := by field_simp
    rw [this]; exact hy k

end ThmS

end CM4E.Gen
