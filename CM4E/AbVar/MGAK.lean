/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.ThmAn
import CM4E.Gen.MGK

/-!
# The `K`-dimension forms of Theorems MG-A and MG♮-A (paper, `thm:MGA`, `thm:MGnA`)

With `A`, `ζ = ζ_N`, `κ`, `P`, `s₀` (`κ s₀ = 1`) as in `CM4E/AbVar/ThmA.lean` and an `F`-basis `b` of a number field
`K ∋ i, c` (`θ(j, e) = ζ^e b j`):
* `mgA_K`: for `s = cP_{s₀}/π` there are no `x₁, x₂ ∈ K𝓛` with `sx_k ∈ K𝓛 + K·z_{s₀}(Λ(A))` and `2πi, x₁, x₂` linearly
  independent over `K` (`dim_K S_K ≤ 2`, `2πi ∈ S_K`);
* `mgAn_K`: the same for `s = cP̄/π` and `sx_k ∈ K𝓛 + K·(σ̄-fibre values)`, with `σ̄ : ζ ↦ ζ^{N−1}` (`CM4E/AbVar/ThmAn.lean`).
`K` is assumed to contain `F`, `i` and `c`; this is the range of `K` for which the paper states Theorems MG-A, MG♮-A.

Lean has no abelian logarithms: the logarithms of `A` enter as a parameter `LA` of eigen-coordinate `g`-tuples
`(z_s(v))_s` (for MG♮-A, `LAn` of pairs (tuple, `σ̄`-fibre value)), always together with the period `γ` (resp. `γ̃`). The
models `gmAK`, `gmAnK` are the groups of `gmA`, `gmAn` on the frame `gmF2` (uniform subgroup condition), with the
logarithms `[ζ^e]v` in copy `j` (coordinates `ζ^{κ s · e} v_s`; fibre `b_j ζ^{(N−1)e} w`) added. They are sound when `LA`
(`LAn`) consists of coordinates of logarithms of algebraic points of `A` (`A^♮`), in the normalisation of the period
`P` (`P̄`); for `LA = ∅` they are the models of `ThmA`/`ThmAn` with the uniform subgroup condition (sound by the same
argument: no nonzero connected subgroup has tangent space in `ker Ψ''`).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

variable (N g : ℕ) (κ : Fin g → ℕ) {r : ℕ}

/-- `[ζ^e]v` in copy `j` of `A^r`. -/
noncomputable def twistA (j : Fin r) (e : ℕ) (v : Fin g → ℂ) : Fin g × Fin r → ℂ :=
  fun p => if p.2 = j then zetaN N ^ (κ p.1 * e) * v p.1 else 0

lemma lam_twistA (s₀ : Fin g) (b : Fin r → ℂ) (j : Fin r) (e : ℕ) (v : Fin g → ℂ) :
    dotL (thetaA g s₀ b) (twistA N g κ j e v) = b j * zetaN N ^ (κ s₀ * e) * v s₀ := by
  rw [dotL_apply, Finset.sum_eq_single (s₀, j)]
  · simp [thetaA, twistA]; ring
  · rintro ⟨s, j'⟩ - hne
    by_cases hs : s = s₀
    · subst hs
      have : j' ≠ j := fun h => hne (by rw [h])
      simp [thetaA, twistA, this]
    · simp [thetaA, hs]
  · simp

/-! ## Toric lifts over `θ(j, e) = ζ^e b j` -/

section TorLift

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q] {d : ℕ}

/-- A lift of `θ_h Σ β_k ℓ_k` in the first toric block. -/
noncomputable def tLift1 (α : ℂ) (b : Fin r → ℂ) (h : Fin r × Fin d) {M : ℕ} (β ℓ : Fin M → ℂ) :
    TF (Fin r × Fin d) Q :=
  ∑ k, ∑ p, (coordsD α d b (thetaD α d b h * β k) p) • tor1 p (ℓ k)

/-- A lift of `θ_h Σ β_k ℓ_k` in the second toric block. -/
noncomputable def tLift2 (α : ℂ) (b : Fin r → ℂ) (h : Fin r × Fin d) {M : ℕ} (β ℓ : Fin M → ℂ) :
    TF (Fin r × Fin d) Q :=
  ∑ k, ∑ p, (coordsD α d b (thetaD α d b h * β k) p) • tor2 p (ℓ k)

lemma sum_coordsD {α : ℂ} {b : Fin r → ℂ} (hb : IsAdaptedBasisD α d b) (h : Fin r × Fin d) {z : ℂ}
    (hz : z ∈ KspanD α d b) (w : ℂ) :
    ∑ p, (coordsD α d b (thetaD α d b h * z) p : ℂ) * (thetaD α d b p * w) = thetaD α d b h * z * w := by
  rw [show thetaD α d b h * z * w = (∑ p, (coordsD α d b (thetaD α d b h * z) p : ℂ) * thetaD α d b p) * w by
    rw [coordsD_spec (hb.mul_mem _ (Submodule.subset_span ⟨h, rfl⟩) _ hz)], Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

omit [Module ℂ Q] in
lemma tLift1_coords {α : ℂ} {b : Fin r → ℂ} (hb : IsAdaptedBasisD α d b) (h : Fin r × Fin d) {M : ℕ}
    (β ℓ : Fin M → ℂ) (hβ : ∀ k, β k ∈ KspanD α d b) :
    dotL (thetaD α d b) (tLift1 (Q := Q) α b h β ℓ).1.1 = thetaD α d b h * ∑ k, β k * ℓ k ∧
      (tLift1 (Q := Q) α b h β ℓ).1.2 = 0 ∧ (tLift1 (Q := Q) α b h β ℓ).2 = 0 := by
  refine ⟨?_, by simp [tLift1, tor1, Prod.fst_sum, Prod.snd_sum], by simp [tLift1, tor1, Prod.snd_sum]⟩
  simp only [tLift1, tor1, Prod.fst_sum, Prod.smul_fst, map_sum, map_rat_smul, dotL_single, Rat.smul_def]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [sum_coordsD hb h (hβ k)]; ring

omit [Module ℂ Q] in
lemma tLift2_coords {α : ℂ} {b : Fin r → ℂ} (hb : IsAdaptedBasisD α d b) (h : Fin r × Fin d) {M : ℕ}
    (β ℓ : Fin M → ℂ) (hβ : ∀ k, β k ∈ KspanD α d b) :
    (tLift2 (Q := Q) α b h β ℓ).1.1 = 0 ∧
      dotL (thetaD α d b) (tLift2 (Q := Q) α b h β ℓ).1.2 = thetaD α d b h * ∑ k, β k * ℓ k ∧
      (tLift2 (Q := Q) α b h β ℓ).2 = 0 := by
  refine ⟨by simp [tLift2, tor2, Prod.fst_sum], ?_, by simp [tLift2, tor2, Prod.snd_sum]⟩
  simp only [tLift2, tor2, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, map_sum, map_rat_smul,
    dotL_single, Rat.smul_def]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [sum_coordsD hb h (hβ k)]; ring

omit [Module ℂ Q] in
lemma tLift1_mem (α : ℂ) (b : Fin r → ℂ) (lamS : Set (TF (Fin r × Fin d) Q))
    (hS : ∀ i x, IsAlgebraic ℚ (Complex.exp x) → (tor1 i x : TF (Fin r × Fin d) Q) ∈ lamS)
    (h : Fin r × Fin d) {M : ℕ} (β ℓ : Fin M → ℂ) (hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) :
    tLift1 (Q := Q) α b h β ℓ ∈ Submodule.span ℚ lamS :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hS i _ (hℓ k)))

omit [Module ℂ Q] in
lemma tLift2_mem (α : ℂ) (b : Fin r → ℂ) (lamS : Set (TF (Fin r × Fin d) Q))
    (hS : ∀ i x, IsAlgebraic ℚ (Complex.exp x) → (tor2 i x : TF (Fin r × Fin d) Q) ∈ lamS)
    (h : Fin r × Fin d) {M : ℕ} (β ℓ : Fin M → ℂ) (hℓ : ∀ k, IsAlgebraic ℚ (Complex.exp (ℓ k))) :
    tLift2 (Q := Q) α b h β ℓ ∈ Submodule.span ℚ lamS :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hS i _ (hℓ k)))

end TorLift

/-! ## Theorem MG-A, `K`-form -/

section MGA

variable (P : Fin g → ℂ) (s₀ : Fin g) (b : Fin r → ℂ) (LA : Set (Fin g → ℂ))

/-- Generators of the logarithms of `G_m^{2n} × A^r`: toric logarithms and `[ζ^e]v` in copy `j`. -/
def lamAK : Set (TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ)) :=
  {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor1 i y} ∪
    {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor2 i y} ∪
    {x | ∃ (j : Fin r) (e : ℕ), ∃ v ∈ insert P LA, x = qv (twistA N g κ j e v)}

/-- The model of `G_m^{2n} × A^r` with logarithms of `A` (frame `gmF2`). -/
noncomputable def gmAK : GroupModel (TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ)) :=
  gmF2 (thetaD (zetaN N) N.totient b) (algA g) (lamAK N g κ P LA)
    (perGen (ι := Fin r × Fin N.totient) (perAgen N g κ P)) 0 (dotL (thetaA g s₀ b))
    (finrank ℂ (Fin g × Fin r → ℂ))

/-- **The hypothesis for the `K`-form of MG-A**: W88 §5d for `G_m^{2n} × A^r`, every `F`-basis `b`, restricted to the
toric-injective hyperplanes (`TorInj`: no nonzero period of `A^r` alone lies in `V`; this only weakens it, by
`HyperplaneKappa.on`, and the proof uses only `V''`, which is toric-injective by `perA_inj`). Claimed when `LA`
consists of eigen-coordinate tuples of logarithms of algebraic points of `A` (normalised as `P`). -/
def Thm11KappaAK : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b →
    HyperplaneKappaOn (gmAK N g κ P s₀ b LA) (TorInj (gmAK N g κ P s₀ b LA))

/-- `K · z_{s₀}(Λ(A))`: `K`-combinations of slot values of logarithms of `A` (or the period). -/
def KSlotA (K : Submodule ℚ ℂ) : Set ℂ :=
  {x | ∃ (M : ℕ) (β : Fin M → ℂ) (v : Fin M → Fin g → ℂ), (∀ k, β k ∈ K) ∧ (∀ k, v k ∈ insert P LA) ∧
    x = ∑ k, β k * v k s₀}

/-- A lift of `θ_h Σ β_k z_{s₀}(v_k)` in `A^r`. -/
noncomputable def aLiftA (h : Fin r × Fin N.totient) {M : ℕ} (β : Fin M → ℂ) (v : Fin M → Fin g → ℂ) :
    TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ) :=
  ∑ k, ∑ p, (coordsD (zetaN N) N.totient b (thetaD (zetaN N) N.totient b h * β k) p) •
    qv (twistA N g κ p.1 p.2 (v k))

variable {N g κ P s₀ b}

lemma aLiftA_coords (hb : IsAdaptedBasisD (zetaN N) N.totient b) (hκ : κ s₀ = 1) (h : Fin r × Fin N.totient)
    {M : ℕ} (β : Fin M → ℂ) (v : Fin M → Fin g → ℂ) (hβ : ∀ k, β k ∈ KspanD (zetaN N) N.totient b) :
    (aLiftA N g κ b h β v).1 = 0 ∧
      dotL (thetaA g s₀ b) (aLiftA N g κ b h β v).2 = thetaD (zetaN N) N.totient b h * ∑ k, β k * v k s₀ := by
  refine ⟨by simp [aLiftA, qv, Prod.fst_sum], ?_⟩
  simp only [aLiftA, qv, Prod.snd_sum, Prod.smul_snd, map_sum, map_rat_smul, lam_twistA, hκ, one_mul,
    Rat.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← sum_coordsD hb h (hβ k) (v k s₀)]
  exact Finset.sum_congr rfl fun p _ => by simp only [thetaD]; ring

lemma aLiftA_mem (h : Fin r × Fin N.totient) {M : ℕ} (β : Fin M → ℂ) (v : Fin M → Fin g → ℂ)
    (hv : ∀ k, v k ∈ insert P LA) : aLiftA N g κ b h β v ∈ Submodule.span ℚ (lamAK N g κ P LA) :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨p.1, p.2, v k, hv k, rfl⟩))

/-- **Theorem MG-A, `K`-form**: for `s = cP_{s₀}/π` and `K = span_ℚ θ ∋ i, c`, there are no `x₁, x₂ ∈ K𝓛` with
`sx_k ∈ K𝓛 + K·z_{s₀}(Λ(A))` and `2πi, x₁, x₂` linearly independent over `K`. Hypotheses: W88 §5d (`hW`), `2g ≤ φ(N)`,
`κ s₀ = 1`, every `κ s` prime to `N` (true for a CM type), `P_{s₀}/π ∉ ℚ̄`. -/
theorem mgA_K (hN : N ≠ 0) (hW : Thm11KappaAK N g κ P s₀ LA) (hg : 2 * g ≤ N.totient) (hκ : κ s₀ = 1)
    (hκN : ∀ s, (κ s).Coprime N)
    (hT : Transcendental ℚ (P s₀ / Real.pi)) (hb : IsAdaptedBasisD (zetaN N) N.totient b)
    (c : ℂ) (hcK : c ∈ KspanD (zetaN N) N.totient b) (hc0 : c ≠ 0) (hIK : I ∈ KspanD (zetaN N) N.totient b)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ KLog (KspanD (zetaN N) N.totient b))
    (hsx : ∀ k, ∃ y ∈ KLog (KspanD (zetaN N) N.totient b), ∃ e ∈ KSlotA g P s₀ LA (KspanD (zetaN N) N.totient b),
      c * P s₀ / Real.pi * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ KspanD (zetaN N) N.totient b → a₁ ∈ KspanD (zetaN N) N.totient b →
      a₂ ∈ KspanD (zetaN N) N.totient b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  set s := c * P s₀ / Real.pi with hsdef
  choose M β ℓ hβ hℓ hxe using hx
  choose y hy e he hye using hsx
  choose M' β' ℓ' hβ' hℓ' hye' using hy
  choose M'' β'' v hβ'' hv he' using he
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθalg := thetaD_isAlgebraic (isAlgebraic_zetaN N hN) N.totient hb.alg
  have hr : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    subst hr0
    have := hb.one_mem
    rw [KspanD, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    exact one_ne_zero this
  have ht0 : 0 < N.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)
  have hc : IsAlgebraic ℚ c := KspanD_isAlgebraic (isAlgebraic_zetaN N hN) hb.alg hcK
  have hθ'alg : ∀ p, IsAlgebraic ℚ (thetaA g s₀ b p) := by
    intro p; unfold thetaA; split_ifs
    exacts [hb.alg _, isAlgebraic_zero]
  -- period lifts
  have h2 : (2 : ℂ) ∈ KspanD (zetaN N) N.totient b := by
    have := Submodule.smul_mem _ (2 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hxK : ∀ h, 2 * I * c * thetaD (zetaN N) N.totient b h ∈ KspanD (zetaN N) N.totient b := fun h =>
    hb.mul_mem _ (hb.mul_mem _ (hb.mul_mem _ h2 _ hIK) _ hcK) _ (Submodule.subset_span ⟨h, rfl⟩)
  let qh : Fin r × Fin N.totient → (Fin g × Fin r → ℂ) := fun h =>
    ∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℚ) •
      twistA N g κ p.1 p.2 P
  have hlqh : ∀ h, dotL (thetaA g s₀ b) (qh h) = s * (thetaD (zetaN N) N.totient b h * (2 * Real.pi * I)) := by
    intro h
    simp only [qh, map_sum, map_rat_smul, lam_twistA, hκ, one_mul, Rat.smul_def]
    rw [show ∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℂ) *
        (b p.1 * zetaN N ^ (p.2 : ℕ) * P s₀) =
        (∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℂ) *
          thetaD (zetaN N) N.totient b p) * P s₀ by
      rw [Finset.sum_mul]; congr 1; funext p; simp [thetaD]; ring, coordsD_spec (hxK h), hsdef]
    field_simp
  have hqv : ∀ h, qv (qh h) = ∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℚ) •
      (qv (twistA N g κ p.1 p.2 P) : TF (Fin r × Fin N.totient) (Fin g × Fin r → ℂ)) := by
    intro h
    simp [qv, qh, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
  have hqh_lam : ∀ h, qv (qh h) ∈ Submodule.span ℚ (lamAK N g κ P LA) := by
    intro h; rw [hqv h]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨p.1, p.2, P, Set.mem_insert _ _, rfl⟩))
  have hqh_per : ∀ h, qv (qh h) ∈ Submodule.span ℚ (perGen (ι := Fin r × Fin N.totient) (perAgen N g κ P)) := by
    intro h; rw [hqv h]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨_, ⟨(p.1, p.2), rfl⟩, rfl⟩))
  -- `s` transcendental
  have hs : Transcendental ℚ s := by
    intro halg
    apply hT
    have : P s₀ / Real.pi = s / c := by rw [hsdef]; field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (mem_algebraicClosure_iff.mpr halg) (mem_algebraicClosure_iff.mpr hc)
  have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
    rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  have hfin : finrank ℂ (Fin g × Fin r → ℂ) < Fintype.card (Fin r × Fin N.totient) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    have : g < N.totient := by omega
    nlinarith
  -- `V''` is toric-injective
  have hP0 : P s₀ ≠ 0 := fun h => hT (by rw [h, zero_div]; exact isAlgebraic_zero)
  have hper0 : ∀ v ∈ Submodule.span ℚ (perGen (ι := Fin r × Fin N.totient) (perAgen N g κ P)), v.1 = 0 →
      dotL (thetaA g s₀ b) v.2 = s * (0 : (Fin g × Fin r → ℂ) →ₗ[ℂ] ℂ) v.2 → v = 0 := by
    intro v hv h1 hl
    rw [LinearMap.zero_apply, mul_zero] at hl
    exact Prod.ext h1 (perA_inj N g κ P s₀ b hN hb hκ hκN hP0 _ (snd_mem_span_perQ _ hv) hl)
  refine frame2_false_K_on (thetaD (zetaN N) N.totient b) hb.indep hθalg (algA g) (lamAK N g κ P LA)
    (perGen (ι := Fin r × Fin N.totient) (perAgen N g κ P)) 0 (dotL (thetaA g s₀ b))
    (finrank ℂ (Fin g × Fin r → ℂ)) (hW r b hb) hfin (fun _ => isAlgebraic_zero)
    (fun _ _ => isAlgebraic_zero) ?_ (Set.range fun p => (Pi.single p 1 : Fin g × Fin r → ℂ)) ?_ ?_ s hs hper0
    (fun h => tor1 h (2 * Real.pi * I) + qv (qh h)) ?_ ?_ ?_ x
    (fun k h => tLift1 (zetaN N) b h (β k) (ℓ k) + tLift2 (zetaN N) b h (β' k) (ℓ' k) +
      aLiftA N g κ b h (β'' k) (v k)) ?_ ?_ hind
  · intro q hq
    rw [dotL_apply, ← mem_algebraicClosure_iff]
    exact sum_mem fun p _ => mul_mem (mem_algebraicClosure_iff.mpr (hθ'alg p)) (mem_algebraicClosure_iff.mpr (hq p))
  · rintro _ ⟨p, rfl⟩ k
    simp only [Pi.single_apply]; split_ifs
    exacts [isAlgebraic_one, isAlgebraic_zero]
  · rw [eq_top_iff]
    rintro q -
    rw [← sum_smul_single q]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, _, h2pi, rfl⟩))) (hqh_lam h)
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩))) (hqh_per h)
  · intro h
    simp only [PsiG_apply, tor1, qv, map_add, dotL_single, map_zero, add_zero, zero_add, hlqh,
      LinearMap.zero_apply]
    simp
  · intro k h
    exact add_mem (add_mem (tLift1_mem _ _ _ (fun i y hy => Or.inl (Or.inl ⟨i, y, hy, rfl⟩)) h _ _ (hℓ k))
      (tLift2_mem _ _ _ (fun i y hy => Or.inl (Or.inr ⟨i, y, hy, rfl⟩)) h _ _ (hℓ' k)))
      (aLiftA_mem LA h _ _ (hv k))
  · intro k h
    obtain ⟨a1, a2, a3⟩ := tLift1_coords (Q := Fin g × Fin r → ℂ) hb h (β k) (ℓ k) (hβ k)
    obtain ⟨c1, c2, c3⟩ := tLift2_coords (Q := Fin g × Fin r → ℂ) hb h (β' k) (ℓ' k) (hβ' k)
    obtain ⟨e1, e2⟩ := aLiftA_coords (s₀ := s₀) hb hκ h (β'' k) (v k) (hβ'' k)
    have e1a : (aLiftA N g κ b h (β'' k) (v k)).1.1 = 0 := by rw [e1]; rfl
    have e1b : (aLiftA N g κ b h (β'' k) (v k)).1.2 = 0 := by rw [e1]; rfl
    simp only [PsiG_apply, map_add, a1, a2, a3, c1, c2, c3, e1a, e1b, e2, map_zero, LinearMap.zero_apply,
      add_zero, zero_add]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, add_zero]; rw [hxe k]
    · simp only [Prod.snd_add, zero_add]
      rw [show s * (thetaD (zetaN N) N.totient b h * x k) = thetaD (zetaN N) N.totient b h * (s * x k) by ring,
        hye k, hye' k, he' k]
      ring

end MGA

section MGAn

/-! ## Theorem MG♮-A, `K`-form -/

variable (P : Fin g → ℂ) (Pb : ℂ) (b : Fin r → ℂ) (LAn : Set ((Fin g → ℂ) × ℂ))

/-- `[ζ^e](v, w)` in copy `j` of `(A^♮)^r`, pushed to `Q''`: base `ζ^{κ s · e} v_s`, fibre `b_j ζ^{(N−1)e} w`. -/
noncomputable def twistAn (b : Fin r → ℂ) (j : Fin r) (e : ℕ) (vw : (Fin g → ℂ) × ℂ) : (Fin g × Fin r → ℂ) × ℂ :=
  (twistA N g κ j e vw.1, b j * zetaN N ^ ((N - 1) * e) * vw.2)

/-- Generators of the logarithms of `G_m^{2n} × Q''`. -/
def lamAnK : Set (TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ)) :=
  {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor1 i y} ∪
    {x | ∃ i y, IsAlgebraic ℚ (Complex.exp y) ∧ x = tor2 i y} ∪
    {x | ∃ (j : Fin r) (e : ℕ), ∃ vw ∈ insert (P, Pb) LAn, x = qv (twistAn N g κ b j e vw)}

/-- The model of `G_m^{2n} × Q''` with logarithms of `A^♮` (frame `gmF2`). -/
noncomputable def gmAnK : GroupModel (TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ)) :=
  gmF2 (thetaD (zetaN N) N.totient b) (algAn g) (lamAnK N g κ P Pb b LAn)
    (perGen (ι := Fin r × Fin N.totient) (perAngen N g κ P Pb b)) 0 (LinearMap.snd ℂ _ ℂ)
    (finrank ℂ ((Fin g × Fin r → ℂ) × ℂ))

/-- **The hypothesis for the `K`-form of MG♮-A**: W88 §5d for `G_m^{2n} × Q''`, every `F`-basis `b`. Claimed when `LAn`
consists of (eigen-coordinate tuple, `σ̄`-fibre value) pairs of logarithms of algebraic points of `A^♮` (normalised as
`(P, P̄)`). -/
def Thm11KappaAnK : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD (zetaN N) N.totient b → HyperplaneKappa (gmAnK N g κ P Pb b LAn)

/-- `K · (σ̄-fibre values)`. -/
def KFibA (K : Submodule ℚ ℂ) : Set ℂ :=
  {x | ∃ (M : ℕ) (β : Fin M → ℂ) (vw : Fin M → (Fin g → ℂ) × ℂ), (∀ k, β k ∈ K) ∧
    (∀ k, vw k ∈ insert (P, Pb) LAn) ∧ x = ∑ k, β k * (vw k).2}

/-- A lift of `θ_h Σ β_k w_k` in `Q''`. -/
noncomputable def aLiftAn (h : Fin r × Fin N.totient) {M : ℕ} (β : Fin M → ℂ) (vw : Fin M → (Fin g → ℂ) × ℂ) :
    TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ) :=
  ∑ k, ∑ p, (coordsD (zetaN N) N.totient b (thetaD (zetaN N) N.totient b h * β k) p) •
    qv (twistAn N g κ b p.1 ((N - 1) * p.2) (vw k))

variable {N g κ P b}

lemma aLiftAn_coords (hN : 2 ≤ N) (hb : IsAdaptedBasisD (zetaN N) N.totient b) (h : Fin r × Fin N.totient)
    {M : ℕ} (β : Fin M → ℂ) (vw : Fin M → (Fin g → ℂ) × ℂ) (hβ : ∀ k, β k ∈ KspanD (zetaN N) N.totient b) :
    (aLiftAn N g κ b h β vw).1 = 0 ∧
      (aLiftAn N g κ b h β vw).2.2 = thetaD (zetaN N) N.totient b h * ∑ k, β k * (vw k).2 := by
  refine ⟨by simp [aLiftAn, qv, Prod.fst_sum], ?_⟩
  simp only [aLiftAn, qv, twistAn, Prod.snd_sum, Prod.smul_snd, zetaN_pow_sq N hN, Rat.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← sum_coordsD hb h (hβ k) (vw k).2]
  exact Finset.sum_congr rfl fun p _ => by simp only [thetaD]; ring

lemma aLiftAn_mem (h : Fin r × Fin N.totient) {M : ℕ} (β : Fin M → ℂ) (vw : Fin M → (Fin g → ℂ) × ℂ)
    (hv : ∀ k, vw k ∈ insert (P, Pb) LAn) : aLiftAn N g κ b h β vw ∈ Submodule.span ℚ (lamAnK N g κ P Pb b LAn) :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨p.1, _, vw k, hv k, rfl⟩))

/-- **Theorem MG♮-A, `K`-form**: for `s = cP̄/π` and `K = span_ℚ θ ∋ i, c`, there are no `x₁, x₂ ∈ K𝓛` with
`sx_k ∈ K𝓛 + K·(σ̄-fibre values)` and `2πi, x₁, x₂` linearly independent over `K`. Hypotheses: W88 §5d (`hW`),
`2 ≤ g`, `2g ≤ φ(N)`, `P̄/π ∉ ℚ̄`. -/
theorem mgAn_K (hN : 2 ≤ N) (hW : Thm11KappaAnK N g κ P Pb LAn) (hg2 : 2 ≤ g) (hg : 2 * g ≤ N.totient)
    (hT : Transcendental ℚ (Pb / Real.pi)) (hb : IsAdaptedBasisD (zetaN N) N.totient b)
    (c : ℂ) (hcK : c ∈ KspanD (zetaN N) N.totient b) (hc0 : c ≠ 0) (hIK : I ∈ KspanD (zetaN N) N.totient b)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ KLog (KspanD (zetaN N) N.totient b))
    (hsx : ∀ k, ∃ y ∈ KLog (KspanD (zetaN N) N.totient b), ∃ e ∈ KFibA g P Pb LAn (KspanD (zetaN N) N.totient b),
      c * Pb / Real.pi * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ KspanD (zetaN N) N.totient b → a₁ ∈ KspanD (zetaN N) N.totient b →
      a₂ ∈ KspanD (zetaN N) N.totient b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False := by
  set s := c * Pb / Real.pi with hsdef
  choose M β ℓ hβ hℓ hxe using hx
  choose y hy e he hye using hsx
  choose M' β' ℓ' hβ' hℓ' hye' using hy
  choose M'' β'' vw hβ'' hv he' using he
  have hN0 : N ≠ 0 := by omega
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hθalg := thetaD_isAlgebraic (isAlgebraic_zetaN N hN0) N.totient hb.alg
  have hr : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    subst hr0
    have := hb.one_mem
    rw [KspanD, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hc : IsAlgebraic ℚ c := KspanD_isAlgebraic (isAlgebraic_zetaN N hN0) hb.alg hcK
  -- period lifts
  have h2 : (2 : ℂ) ∈ KspanD (zetaN N) N.totient b := by
    have := Submodule.smul_mem _ (2 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hxK : ∀ h, 2 * I * c * thetaD (zetaN N) N.totient b h ∈ KspanD (zetaN N) N.totient b := fun h =>
    hb.mul_mem _ (hb.mul_mem _ (hb.mul_mem _ h2 _ hIK) _ hcK) _ (Submodule.subset_span ⟨h, rfl⟩)
  let qh : Fin r × Fin N.totient → (Fin g × Fin r → ℂ) × ℂ := fun h =>
    ∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℚ) •
      twistAn N g κ b p.1 ((N - 1) * p.2) (P, Pb)
  have hlqh : ∀ h, LinearMap.snd ℂ _ ℂ (qh h) = s * (thetaD (zetaN N) N.totient b h * (2 * Real.pi * I)) := by
    intro h
    simp only [qh, LinearMap.snd_apply, Prod.snd_sum, Prod.smul_snd, twistAn, zetaN_pow_sq N hN, Rat.smul_def]
    rw [show ∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℂ) *
        (b p.1 * zetaN N ^ (p.2 : ℕ) * Pb) =
        (∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℂ) *
          thetaD (zetaN N) N.totient b p) * Pb by
      rw [Finset.sum_mul]; congr 1; funext p; simp only [thetaD]; ring, coordsD_spec (hxK h), hsdef]
    field_simp
  have hqv : ∀ h, qv (qh h) = ∑ p, (coordsD (zetaN N) N.totient b (2 * I * c * thetaD (zetaN N) N.totient b h) p : ℚ) •
      (qv (twistAn N g κ b p.1 ((N - 1) * p.2) (P, Pb)) :
        TF (Fin r × Fin N.totient) ((Fin g × Fin r → ℂ) × ℂ)) := by
    intro h
    simp [qv, qh, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]
  have hqh_lam : ∀ h, qv (qh h) ∈ Submodule.span ℚ (lamAnK N g κ P Pb b LAn) := by
    intro h; rw [hqv h]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨p.1, _, (P, Pb), Set.mem_insert _ _, rfl⟩))
  have hqh_per : ∀ h, qv (qh h) ∈
      Submodule.span ℚ (perGen (ι := Fin r × Fin N.totient) (perAngen N g κ P Pb b)) := by
    intro h; rw [hqv h]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inr ⟨_, ⟨(p.1, (N - 1) * p.2), rfl⟩, rfl⟩))
  -- `s` transcendental
  have hs : Transcendental ℚ s := by
    intro halg
    apply hT
    have : Pb / Real.pi = s / c := by rw [hsdef]; field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (mem_algebraicClosure_iff.mpr halg) (mem_algebraicClosure_iff.mpr hc)
  have h2pi : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * I)) := by
    rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  have hfin : finrank ℂ ((Fin g × Fin r → ℂ) × ℂ) < Fintype.card (Fin r × Fin N.totient) := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Module.finrank_self]
    nlinarith
  refine frame2_false_K (thetaD (zetaN N) N.totient b) hb.indep hθalg (algAn g) (lamAnK N g κ P Pb b LAn)
    (perGen (ι := Fin r × Fin N.totient) (perAngen N g κ P Pb b)) 0 (LinearMap.snd ℂ _ ℂ)
    (finrank ℂ ((Fin g × Fin r → ℂ) × ℂ)) (hW r b hb) hfin ⟨fun _ => isAlgebraic_zero, isAlgebraic_zero⟩
    (fun _ _ => isAlgebraic_zero) (fun q hq => hq.2)
    ({(0, 1)} ∪ Set.range fun p => ((Pi.single p 1 : Fin g × Fin r → ℂ), (0 : ℂ))) ?_ ?_ s hs
    (fun h => tor1 h (2 * Real.pi * I) + qv (qh h)) ?_ ?_ ?_ x
    (fun k h => tLift1 (zetaN N) b h (β k) (ℓ k) + tLift2 (zetaN N) b h (β' k) (ℓ' k) +
      aLiftAn N g κ b h (β'' k) (vw k)) ?_ ?_ hind
  · rintro q (hq | ⟨p, rfl⟩)
    · rw [Set.mem_singleton_iff] at hq; subst hq
      exact ⟨fun _ => isAlgebraic_zero, isAlgebraic_one⟩
    · refine ⟨fun k => ?_, isAlgebraic_zero⟩
      simp only [Pi.single_apply]; split_ifs
      exacts [isAlgebraic_one, isAlgebraic_zero]
  · rw [eq_top_iff]
    rintro ⟨q, f⟩ -
    have hdec : ((q, f) : (Fin g × Fin r → ℂ) × ℂ) = f • ((0, 1) : (Fin g × Fin r → ℂ) × ℂ) +
        ∑ p, q p • ((Pi.single p 1 : Fin g × Fin r → ℂ), (0 : ℂ)) := by
      refine Prod.ext ?_ (by simp [Prod.snd_sum])
      simp only [Prod.fst_add, Prod.smul_fst, smul_zero, zero_add, Prod.fst_sum]
      exact (sum_smul_single q).symm
    rw [hdec]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl)))
      (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨p, rfl⟩)))
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, _, h2pi, rfl⟩))) (hqh_lam h)
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, rfl⟩))) (hqh_per h)
  · intro h
    simp only [PsiG_apply, tor1, qv, map_add, dotL_single, map_zero, add_zero, zero_add, LinearMap.zero_apply]
    simp only [LinearMap.snd_apply] at hlqh
    simp [hlqh]
  · intro k h
    exact add_mem (add_mem (tLift1_mem _ _ _ (fun i y hy => Or.inl (Or.inl ⟨i, y, hy, rfl⟩)) h _ _ (hℓ k))
      (tLift2_mem _ _ _ (fun i y hy => Or.inl (Or.inr ⟨i, y, hy, rfl⟩)) h _ _ (hℓ' k)))
      (aLiftAn_mem Pb LAn h _ _ (hv k))
  · intro k h
    obtain ⟨a1, a2, a3⟩ := tLift1_coords (Q := (Fin g × Fin r → ℂ) × ℂ) hb h (β k) (ℓ k) (hβ k)
    obtain ⟨c1, c2, c3⟩ := tLift2_coords (Q := (Fin g × Fin r → ℂ) × ℂ) hb h (β' k) (ℓ' k) (hβ' k)
    obtain ⟨e1, e2⟩ := aLiftAn_coords hN hb h (β'' k) (vw k) (hβ'' k)
    have e1a : (aLiftAn N g κ b h (β'' k) (vw k)).1.1 = 0 := by rw [e1]; rfl
    have e1b : (aLiftAn N g κ b h (β'' k) (vw k)).1.2 = 0 := by rw [e1]; rfl
    simp only [PsiG_apply, map_add, a1, a2, a3, c1, c2, c3, e1a, e1b, LinearMap.snd_apply, map_zero,
      LinearMap.zero_apply, add_zero, zero_add]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, add_zero]; rw [hxe k]
    · simp only [Prod.snd_add, zero_add, e2]
      rw [show s * (thetaD (zetaN N) N.totient b h * x k) = thetaD (zetaN N) N.totient b h * (s * x k) by ring,
        hye k, hye' k, he' k]
      ring

end MGAn

end CM4E.AbVar
