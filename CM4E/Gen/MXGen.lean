/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.Frame
import CM4E.Gen.CMLattice
import CM4E.Gen.BasisExists
import CM4E.MX
import CM4E.Gen.Instances
import LSG.SchneiderMain

/-!
# Theorem MX, `K`-form, for every `β ∈ ℚ̄ˣ`

This generalises `CM4E/MX.lean` (`K = ℚ(i, √3)`) to every number field `K ∋ i` with an adapted basis `θ`
(`n = [K : ℚ]`), so that `β` can be any nonzero algebraic number (`K ⊇ ℚ(i, √3, β)`).

Group (paper, proof of Proposition D): `G'' = (E_i^♮ × E_ρ^♮ × G_a²)^n / U = G_a × G_ℓ`, tangent space
`ℂ × ℂ^n × ℂ^n × ℂ` with coordinates `(s₁, z_i, z_ρ, s₂)` and `Ψ'' = (s₁ + θᵀz_i + θᵀz_ρ, s₂)`; `d₀ = 1`, `d₁ = 0`,
`d₂ = 2n + 1`. The model `gmXG` generalises the `K = ℚ(i, √3)` model reviewed in `reviews/REFEREE_HYP_MX.md`
(general form: `reviews/REFEREE_HYP_MXG.md`). Soundness facts (not checked by Lean; they need only that `θ` is algebraic
and `ℚ`-independent):
1. `LogNat` describes `Λ(E^♮)` in coordinates with `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))`, and the quasi-periods are
   `η((m + ni)ϖ) = (m − ni)π/ϖ`, `η((m + nρ)Ω_ρ) = (m + nρ̄)·2π/(√3 Ω_ρ)`.
2. `lam` is the `ℚ`-span of images of elements of `Λ(G^n)` (one copy at a time); `Λ(G'')` is a `ℚ`-vector space.
3. `perXG` is the `ℚ`-span of the images of the periods of `G^n` (`U` is a vector group).
4. Every nonzero connected algebraic subgroup `H` of `G''` has `T_H ⊄ ker Ψ''`: if `H` meets the kernel `G_a × G_a` of
   `G'' → A` it contains `(c, 0, 0, d) ≠ 0`; otherwise `H` is a splitting over `B = B_i × B_ρ ≠ 0`, its `G_a`-part is
   trivial, a splitting forces `φ(S) = 0` (the anti-affine image of `B^♮` would otherwise contain the fibre), and
   `ker ψ ∩ ker φ = 0` gives `θᵀ ≠ 0` on `T_B`. Since `T_H` is spanned by algebraic vectors, this is `sub`.
5. `d₀ = 1`, `d₁ = 0` maximal (`G_ℓ` is a quotient of an anti-affine group), `d₂ = 2n + 1`.
6. `g₂, g₃` of both lattices are algebraic (premise of the hypothesis).

The period lifts of `θ_h w₁`, `θ_h w₂` are explicit: on `E_i^♮`, `m = u + iv ∈ ℚ(i)^n` has image
`(Σθ_j m_j ϖ, Σθ_j m̄_j π/ϖ) = ((U + iV)ϖ, (U − iV)π/ϖ)` with `U = θᵀu`, `V = θᵀv`; any `(xϖ, yπ/ϖ)` with `x, y ∈ K` is
reached by `U = (x + y)/2`, `V = (x − y)/(2i)`. Likewise on `E_ρ^♮` with `m = u + ρv`. (This is Lemma K, made explicit.)
-/

open Complex Module CM4E.Waldschmidt CM4E.MX

namespace CM4E.Gen

variable {r : ℕ}

/-- The tangent space `ℂ × ℂ^n × ℂ^n × ℂ` of `G_a × G_ℓ`. -/
abbrev TXG (r : ℕ) := ℂ × (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ) × ℂ

variable (b : Fin r → ℂ)

/-- `Ψ''₁ = s₁ + θᵀz_i + θᵀz_ρ`. -/
noncomputable def psiX1 : TXG r →ₗ[ℂ] ℂ :=
  LinearMap.fst ℂ _ _ + dotL (theta I b) ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _) +
    dotL (theta I b) ∘ₗ (LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _)

/-- `Ψ''₂ = s₂`. -/
noncomputable def psiX2 : TXG r →ₗ[ℂ] ℂ where
  toFun v := v.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma psiX1_apply (v : TXG r) :
    psiX1 b v = v.1 + dotL (theta I b) v.2.1 + dotL (theta I b) v.2.2.1 := by
  simp [psiX1]

lemma psiX2_apply (v : TXG r) : psiX2 (r := r) v = v.2.2.2 := rfl

/-- `(z, w) ∈ T(E_i^♮)` in copy `h`. -/
noncomputable def gXI (h : Fin r × Fin 2) (z w : ℂ) : TXG r := (0, Pi.single h z, 0, theta I b h * w)
/-- `(z, w) ∈ T(E_ρ^♮)` in copy `h`. -/
noncomputable def gXR (h : Fin r × Fin 2) (z w : ℂ) : TXG r := (0, 0, Pi.single h z, theta I b h * w)
/-- `(a₁, a₂) ∈ T(G_a²)` in copy `h`. -/
noncomputable def gXA (h : Fin r × Fin 2) (a t : ℂ) : TXG r :=
  (theta I b h * a, 0, 0, theta I b h * t)

/-- Generators of `lam`: images of logarithms of algebraic points of one factor of one copy. -/
def lamGenX : Set (TXG r) :=
  {v | ∃ h z w, LogNat lemniscatic etaLem z w ∧ v = gXI b h z w} ∪
    {v | ∃ h z w, LogNat equianharmonic etaR z w ∧ v = gXR b h z w} ∪
    {v | ∃ h a t, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ t ∧ v = gXA b h a t}

/-- Period generators `(ϖ, π/ϖ)`, `(iϖ, −iπ/ϖ)`, `(Ω_ρ, η_ρ)`, `(ρΩ_ρ, ρ̄η_ρ)` in copy `j`. -/
noncomputable def GX1 (j : Fin r × Fin 2) : TXG r := gXI b j varpi (Real.pi / varpi)
noncomputable def GX2 (j : Fin r × Fin 2) : TXG r := gXI b j (I * varpi) (-I * (Real.pi / varpi))
noncomputable def HX1 (j : Fin r × Fin 2) : TXG r := gXR b j omegaRho etaRho
noncomputable def HX2 (j : Fin r × Fin 2) : TXG r := gXR b j (rho * omegaRho) (rhoBar * etaRho)

/-- The `ℚ`-span of the periods of `G''`. -/
noncomputable def perXG : Submodule ℚ (TXG r) :=
  Submodule.span ℚ (Set.range (GX1 b) ∪ Set.range (GX2 b) ∪ Set.range (HX1 b) ∪ Set.range (HX2 b))

/-- Algebraic coordinates. -/
def algXG (v : TXG r) : Prop :=
  IsAlgebraic ℚ v.1 ∧ (∀ j, IsAlgebraic ℚ (v.2.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.2.2.1 j)) ∧
    IsAlgebraic ℚ v.2.2.2

/-- The model of `G'' = G_a × G_ℓ` for the adapted basis `θ = theta I b`. -/
noncomputable def gmXG : GroupModel (TXG r) where
  d₁ := 0
  d₂ := 2 * Fintype.card (Fin r × Fin 2) + 1
  alg := algXG
  lam := (Submodule.span ℚ (lamGenX b) : Set (TXG r))
  per := perXG b
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algXG x ∧ (psiX1 b x ≠ 0 ∨ psiX2 (r := r) x ≠ 0)

/-- **The hypothesis for Theorem MX (general `β`)**: W88 §5d for `G_a × G_ℓ`, for every adapted basis of a number field
containing `i`. Same form as all other hypotheses (`HyperplaneKappa` of a group model). -/
def Thm11KappaMXG : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ →
    IsAlgebraic ℚ equianharmonic.g₂ → IsAlgebraic ℚ equianharmonic.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b → HyperplaneKappa (gmXG b)

/-! ## `Ψ''` on generators, coordinates, explicit lifts -/

section Lifts

variable {b}

lemma psiX1_gXI (h : Fin r × Fin 2) (z w : ℂ) : psiX1 b (gXI b h z w) = theta I b h * z := by
  simp [psiX1_apply, gXI, dotL_single]
lemma psiX2_gXI (h : Fin r × Fin 2) (z w : ℂ) : psiX2 (gXI b h z w) = theta I b h * w := rfl
lemma psiX1_gXR (h : Fin r × Fin 2) (z w : ℂ) : psiX1 b (gXR b h z w) = theta I b h * z := by
  simp [psiX1_apply, gXR, dotL_single]
lemma psiX2_gXR (h : Fin r × Fin 2) (z w : ℂ) : psiX2 (gXR b h z w) = theta I b h * w := rfl
lemma psiX1_gXA (h : Fin r × Fin 2) (a t : ℂ) : psiX1 b (gXA b h a t) = theta I b h * a := by
  simp [psiX1_apply, gXA]
lemma psiX2_gXA (h : Fin r × Fin 2) (a t : ℂ) : psiX2 (gXA b h a t) = theta I b h * t := rfl

lemma psiX_rsmul (f : TXG r →ₗ[ℂ] ℂ) (q : ℚ) (v : TXG r) : f (q • v) = (q : ℂ) * f v := by
  rw [map_rat_smul f q v, Rat.smul_def]


lemma sum_coef (m : Fin r × Fin 2 → ℚ) (θ : Fin r × Fin 2 → ℂ) (c : ℂ) :
    ∑ j, (m j : ℂ) * (θ j * c) = (∑ j, (m j : ℂ) * θ j) * c := by
  rw [Finset.sum_mul]; congr 1; funext j; ring

variable (b) in
/-- A lift on `E_i^♮` with image `(xϖ, yπ/ϖ)`. -/
noncomputable def liftI (x y : ℂ) : TXG r :=
  ∑ j, (coordsA I b ((x + y) / 2) j) • GX1 b j + ∑ j, (coordsA I b ((x - y) / (2 * I)) j) • GX2 b j

variable (b) in
/-- A lift on `E_ρ^♮` with image `(xΩ_ρ, yη_ρ)`. -/
noncomputable def liftR (x y : ℂ) : TXG r :=
  ∑ j, (coordsA I b (x - rho * ((x - y) / (rho - rhoBar))) j) • HX1 b j +
    ∑ j, (coordsA I b ((x - y) / (rho - rhoBar)) j) • HX2 b j

lemma two_mem (hb : IsAdaptedFieldBasis I b) : (2 : ℂ) ∈ Kspan I b := by
  have := Submodule.smul_mem _ (2 : ℚ) hb.one_mem
  simpa [Rat.smul_def] using this

lemma rho_sub_rhoBar : rho - rhoBar = I * r3 := by simp [rho, rhoBar]; ring

lemma rho_mem (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) :
    rho ∈ Kspan I b := by
  rw [rho, div_eq_mul_inv]
  exact hb.mul_mem _ (add_mem (neg_mem hb.one_mem) (hb.mul_mem _ hI _ hr3)) _ (hb.inv_mem _ (two_mem hb))

lemma rhoBar_mem (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) :
    rhoBar ∈ Kspan I b := by
  rw [rhoBar, div_eq_mul_inv]
  exact hb.mul_mem _ (sub_mem (neg_mem hb.one_mem) (hb.mul_mem _ hI _ hr3)) _ (hb.inv_mem _ (two_mem hb))

lemma psi_liftI (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) {x y : ℂ} (hx : x ∈ Kspan I b)
    (hy : y ∈ Kspan I b) :
    psiX1 b (liftI b x y) = x * varpi ∧ psiX2 (liftI b x y) = y * (Real.pi / varpi) := by
  have hU : (x + y) / 2 ∈ Kspan I b := by
    rw [div_eq_mul_inv]; exact hb.mul_mem _ (add_mem hx hy) _ (hb.inv_mem _ (two_mem hb))
  have hV : (x - y) / (2 * I) ∈ Kspan I b := by
    rw [div_eq_mul_inv]
    exact hb.mul_mem _ (sub_mem hx hy) _ (hb.inv_mem _ (hb.mul_mem _ (two_mem hb) _ hI))
  have hv := varpi_ne_zero'
  constructor
  · simp only [liftI, GX1, GX2, map_add, map_sum, psiX_rsmul, psiX1_gXI]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    field_simp; ring_nf
  · simp only [liftI, GX1, GX2, map_add, map_sum, psiX_rsmul, psiX2_gXI]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    field_simp; ring_nf

lemma psi_liftR (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {x y : ℂ}
    (hx : x ∈ Kspan I b) (hy : y ∈ Kspan I b) :
    psiX1 b (liftR b x y) = x * omegaRho ∧ psiX2 (liftR b x y) = y * etaRho := by
  have hd : rho - rhoBar ≠ 0 := by rw [rho_sub_rhoBar]; exact mul_ne_zero Complex.I_ne_zero r3_ne_zero
  have hV : (x - y) / (rho - rhoBar) ∈ Kspan I b := by
    rw [div_eq_mul_inv]
    exact hb.mul_mem _ (sub_mem hx hy) _
      (hb.inv_mem _ (sub_mem (rho_mem hb hI hr3) (rhoBar_mem hb hI hr3)))
  have hU : x - rho * ((x - y) / (rho - rhoBar)) ∈ Kspan I b :=
    sub_mem hx (hb.mul_mem _ (rho_mem hb hI hr3) _ hV)
  constructor
  · simp only [liftR, HX1, HX2, map_add, map_sum, psiX_rsmul, psiX1_gXR]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    ring
  · simp only [liftR, HX1, HX2, map_add, map_sum, psiX_rsmul, psiX2_gXR]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    field_simp; ring

end Lifts

/-! ## Generators of `Y''` -/

section Gens

variable {b}

/-- Lift of `θ_h w₁ = θ_h (ϖ, β η_ρ)`. -/
noncomputable def P1 (b : Fin r → ℂ) (β : ℂ) (h : Fin r × Fin 2) : TXG r :=
  liftI b (theta I b h) 0 + liftR b 0 (theta I b h * β)
/-- Lift of `θ_h w₂ = θ_h (Ω_ρ, β (2/√3) π/ϖ)`. -/
noncomputable def P2 (b : Fin r → ℂ) (β : ℂ) (h : Fin r × Fin 2) : TXG r :=
  liftR b (theta I b h) 0 + liftI b 0 (theta I b h * β * (2 * r3 / 3))
/-- Lift of `θ_h v`, `v = Ψ(X, Y, a, t)`. -/
noncomputable def DX (b : Fin r → ℂ) (zX wX zY wY a t : ℂ) (h : Fin r × Fin 2) : TXG r :=
  gXI b h zX wX + gXR b h zY wY + gXA b h a t

/-- The `3n` generators. -/
noncomputable def genX (b : Fin r → ℂ) (β zX wX zY wY a t : ℂ) : Fin 3 × (Fin r × Fin 2) → TXG r :=
  fun p => ![P1 b β p.2, P2 b β p.2, DX b zX wX zY wY a t p.2] p.1

lemma psi_P1 (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {β : ℂ}
    (hβ : β ∈ Kspan I b) (h : Fin r × Fin 2) :
    psiX1 b (P1 b β h) = theta I b h * varpi ∧ psiX2 (P1 b β h) = theta I b h * β * etaRho := by
  have hθ : theta I b h ∈ Kspan I b := Submodule.subset_span ⟨h, rfl⟩
  obtain ⟨a1, a2⟩ := psi_liftI hb hI hθ (Submodule.zero_mem _)
  obtain ⟨c1, c2⟩ := psi_liftR hb hI hr3 (Submodule.zero_mem _) (hb.mul_mem _ hθ _ hβ)
  simp only [P1, map_add, a1, a2, c1, c2]
  constructor <;> ring

lemma psi_P2 (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {β : ℂ}
    (hβ : β ∈ Kspan I b) (h : Fin r × Fin 2) :
    psiX1 b (P2 b β h) = theta I b h * omegaRho ∧
      psiX2 (P2 b β h) = theta I b h * β * (2 * r3 / 3) * (Real.pi / varpi) := by
  have hθ : theta I b h ∈ Kspan I b := Submodule.subset_span ⟨h, rfl⟩
  have h3 : (3 : ℂ) ∈ Kspan I b := by
    have := Submodule.smul_mem _ (3 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hc : 2 * r3 / 3 ∈ Kspan I b := by
    rw [div_eq_mul_inv]; exact hb.mul_mem _ (hb.mul_mem _ (two_mem hb) _ hr3) _ (hb.inv_mem _ h3)
  obtain ⟨a1, a2⟩ := psi_liftR hb hI hr3 hθ (Submodule.zero_mem _)
  obtain ⟨c1, c2⟩ := psi_liftI hb hI (Submodule.zero_mem _) (hb.mul_mem _ (hb.mul_mem _ hθ _ hβ) _ hc)
  simp only [P2, map_add, a1, a2, c1, c2]
  constructor <;> ring

lemma psi_DX (zX wX zY wY a t : ℂ) (h : Fin r × Fin 2) :
    psiX1 b (DX b zX wX zY wY a t h) = theta I b h * (zX + zY + a) ∧
      psiX2 (DX b zX wX zY wY a t h) = theta I b h * (wX + wY + t) := by
  simp only [DX, map_add, psiX1_gXI, psiX1_gXR, psiX1_gXA, psiX2_gXI, psiX2_gXR, psiX2_gXA]
  constructor <;> ring

end Gens

/-! ## Memberships, `V''`, `W''` -/

section Mem

variable {b}

lemma liftI_mem_per (x y : ℂ) : liftI b x y ∈ perXG b :=
  add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))))

lemma liftR_mem_per (x y : ℂ) : liftR b x y ∈ perXG b :=
  add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩))))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))

lemma P1_mem_per (β : ℂ) (h : Fin r × Fin 2) : P1 b β h ∈ perXG b :=
  add_mem (liftI_mem_per _ _) (liftR_mem_per _ _)
lemma P2_mem_per (β : ℂ) (h : Fin r × Fin 2) : P2 b β h ∈ perXG b :=
  add_mem (liftR_mem_per _ _) (liftI_mem_per _ _)

lemma logXG_G1 : LogNat lemniscatic etaLem varpi (Real.pi / varpi) :=
  Or.inl ⟨1, 0, by simp [lemniscatic], isAlg_zero_of (by simp [etaLem])⟩
lemma logXG_G2 : LogNat lemniscatic etaLem (I * varpi) (-I * (Real.pi / varpi)) :=
  Or.inl ⟨0, 1, by simp [lemniscatic], isAlg_zero_of (by simp [etaLem])⟩
lemma logXG_H1 : LogNat equianharmonic etaR omegaRho etaRho :=
  Or.inl ⟨1, 0, by simp [equianharmonic], isAlg_zero_of (by simp [etaR])⟩
lemma logXG_H2 : LogNat equianharmonic etaR (rho * omegaRho) (rhoBar * etaRho) :=
  Or.inl ⟨0, 1, by simp [equianharmonic], isAlg_zero_of (by simp [etaR])⟩

lemma perXG_le_lam : perXG b ≤ Submodule.span ℚ (lamGenX b) := by
  rw [perXG, Submodule.span_le]
  rintro _ (((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨j, _, _, logXG_G1, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨j, _, _, logXG_G2, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨j, _, _, logXG_H1, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨j, _, _, logXG_H2, rfl⟩))

lemma genX_mem_lam (β zX wX zY wY a t : ℂ) (hX : LogNat lemniscatic etaLem zX wX)
    (hY : LogNat equianharmonic etaR zY wY) (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (p : Fin 3 × (Fin r × Fin 2)) : genX b β zX wX zY wY a t p ∈ (gmXG b).lam := by
  show genX b β zX wX zY wY a t p ∈ Submodule.span ℚ (lamGenX b)
  obtain ⟨k, h⟩ := p
  fin_cases k
  · exact perXG_le_lam (P1_mem_per β h)
  · exact perXG_le_lam (P2_mem_per β h)
  · exact add_mem (add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, zX, wX, hX, rfl⟩)))
      (Submodule.subset_span (Or.inl (Or.inr ⟨h, zY, wY, hY, rfl⟩))))
      (Submodule.subset_span (Or.inr ⟨h, a, t, ha, ht, rfl⟩))

variable (b) in
/-- `c Ψ''₁ − ϖ Ψ''₂`; with `c = β η_ρ` its kernel is `V'' = Ψ''⁻¹(ℂ(ϖ, β η_ρ))`. -/
noncomputable def phiXG (c : ℂ) : TXG r →ₗ[ℂ] ℂ := c • psiX1 b - (varpi : ℂ) • psiX2

lemma phiXG_apply (c : ℂ) (v : TXG r) : phiXG b c v = c * psiX1 b v - varpi * psiX2 v := rfl

lemma genX_mem_V (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {β : ℂ}
    (hβ : β ∈ Kspan I b) (zX wX zY wY a t : ℂ)
    (hrel : (zX + zY + a) * (β * etaRho) = (wX + wY + t) * varpi) (p : Fin 3 × (Fin r × Fin 2)) :
    genX b β zX wX zY wY a t p ∈ LinearMap.ker (phiXG b (β * etaRho)) := by
  rw [LinearMap.mem_ker, phiXG_apply]
  obtain ⟨k, h⟩ := p
  have hp : (varpi : ℂ) * (Real.pi / varpi) = Real.pi := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ varpi_ne_zero']
  fin_cases k
  · show β * etaRho * psiX1 b (P1 b β h) - varpi * psiX2 (P1 b β h) = 0
    rw [(psi_P1 hb hI hr3 hβ h).1, (psi_P1 hb hI hr3 hβ h).2]; ring
  · show β * etaRho * psiX1 b (P2 b β h) - varpi * psiX2 (P2 b β h) = 0
    rw [(psi_P2 hb hI hr3 hβ h).1, (psi_P2 hb hI hr3 hβ h).2]
    linear_combination (theta I b h * β) * etaRho_mul - (theta I b h * β * (2 * r3 / 3)) * hp
  · show β * etaRho * psiX1 b (DX b zX wX zY wY a t h) - varpi * psiX2 (DX b zX wX zY wY a t h) = 0
    rw [(psi_DX zX wX zY wY a t h).1, (psi_DX zX wX zY wY a t h).2]
    linear_combination theta I b h * hrel

lemma finrank_TXG : finrank ℂ (TXG r) = 2 * Fintype.card (Fin r × Fin 2) + 2 := by
  simp [TXG, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring

lemma finrank_ker_phiXG (c : ℂ) : finrank ℂ (LinearMap.ker (phiXG b c)) + 1 = finrank ℂ (TXG r) := by
  have hsurj : Function.Surjective (phiXG b c) := fun w =>
    ⟨(0, 0, 0, -w / varpi), by
      have hv := varpi_ne_zero'
      simp [phiXG_apply, psiX1_apply, psiX2_apply]; field_simp⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiXG b c)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
  omega

variable (b) in
/-- `(−θ_j, e_j, 0, 0)` and `(−θ_j, 0, e_j, 0)` span `W'' = ker Ψ''`. -/
noncomputable def wXG : (Fin r × Fin 2) ⊕ (Fin r × Fin 2) → TXG r
  | .inl j => (-theta I b j, Pi.single j 1, 0, 0)
  | .inr j => (-theta I b j, 0, Pi.single j 1, 0)

lemma wXG_linearIndependent : LinearIndependent ℂ (wXG b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rintro (j | j)
  · have := congrArg (fun v : TXG r => v.2.1 j) hg
    simpa [Fintype.sum_sum_type, wXG, Finset.sum_apply, Pi.single_apply, Prod.snd_sum,
      Prod.fst_sum] using this
  · have := congrArg (fun v : TXG r => v.2.2.1 j) hg
    simpa [Fintype.sum_sum_type, wXG, Finset.sum_apply, Pi.single_apply, Prod.snd_sum,
      Prod.fst_sum] using this

lemma wXG_le_V (c : ℂ) : Submodule.span ℂ (Set.range (wXG b)) ≤ LinearMap.ker (phiXG b c) := by
  rw [Submodule.span_le]
  rintro _ ⟨j | j, rfl⟩ <;> simp [wXG, phiXG_apply, psiX1_apply, psiX2_apply, dotL_single]

end Mem

/-! ## The theorem -/

/-- **Theorem MX, `K`-form, for every `β ∈ ℚ̄ˣ`** (Proposition D for `v ∈ Ψ(Λ(G))`): if `X = (zX, wX) ∈ Λ(E_i^♮)`,
`Y = (zY, wY) ∈ Λ(E_ρ^♮)`, `a, t ∈ ℚ̄` and `(zX + zY + a) β η(Ω_ρ) = (wX + wY + t) ϖ`, then
`zX + zY + a ∈ ℚ̄ϖ + ℚ̄Ω_ρ`. Hypotheses: W88 §5d for `G_a × G_ℓ` (`hW`), `g₂, g₃` algebraic for both lattices,
`ϖΩ_ρ/π ∉ ℚ̄` (`hΓ`) and `Ω_ρ/ϖ ∉ ℚ̄` (`hM`) (Wüstholz). -/
theorem mx_K (hW : Thm11KappaMXG) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi))
    (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : LogNat lemniscatic etaLem zX wX) (hY : LogNat equianharmonic etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (β * etaRho) = (wX + wY + t) * varpi) :
    ∃ x x' : ℂ, IsAlgebraic ℚ x ∧ IsAlgebraic ℚ x' ∧ zX + zY + a = x * varpi + x' * omegaRho := by
  by_contra hcon
  have hnot : ∀ x x' : ℂ, IsAlgebraic ℚ x → IsAlgebraic ℚ x' → zX + zY + a ≠ x * varpi + x' * omegaRho :=
    fun x x' hx hx' h => hcon ⟨x, x', hx, hx', h⟩
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  obtain ⟨r, hr, b, hb, hS⟩ := exists_adapted_basis I hI (by simp) ⟨-1, 0, by push_cast; simp⟩
    {β, r3} (by intro s hs; simp at hs; rcases hs with rfl | rfl; exacts [hβ, isAlgebraic_r3])
  have hβK : β ∈ Kspan I b := hS β (by simp)
  have hr3K : r3 ∈ Kspan I b := hS r3 (by simp)
  have hIK : I ∈ Kspan I b := CMLattice.α_mem Gen.latI hb
  have hθalg := theta_isAlgebraic hI hb.alg
  have hθ := hb.indep
  set n := Fintype.card (Fin r × Fin 2)
  have hn : n = 2 * r := by simp [n, Fintype.card_prod, mul_comm]
  -- generators, indexed by `Fin m`
  set y0 := genX b β zX wX zY wY a t
  have hli : LinearIndependent ℚ y0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e := congrArg (psiX1 b) hg
    rw [map_sum, map_zero] at e
    simp only [psiX_rsmul, Fintype.sum_prod_type, Fin.sum_univ_three] at e
    have e1 : ∀ h, psiX1 b (y0 (0, h)) = theta I b h * varpi := fun h => (psi_P1 hb hIK hr3K hβK h).1
    have e2 : ∀ h, psiX1 b (y0 (1, h)) = theta I b h * omegaRho := fun h => (psi_P2 hb hIK hr3K hβK h).1
    have e3 : ∀ h, psiX1 b (y0 (2, h)) = theta I b h * (zX + zY + a) := fun h => (psi_DX zX wX zY wY a t h).1
    simp only [e1, e2, e3] at e
    set A := dotL (theta I b) (fun h => ((g (0, h) : ℚ) : ℂ))
    set B := dotL (theta I b) (fun h => ((g (1, h) : ℚ) : ℂ))
    set C := dotL (theta I b) (fun h => ((g (2, h) : ℚ) : ℂ))
    have hABC : A * varpi + B * omegaRho + C * (zX + zY + a) = 0 := by
      simp only [A, B, C, dotL_apply, Finset.sum_mul, Fintype.sum_prod_type]
      rw [← e]
      congr 1
      · congr 1 <;> exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
      · exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have hq : ∀ l : Fin r × Fin 2 → ℚ, dotL (theta I b) (fun h => ((l h : ℚ) : ℂ)) ∈ algebraicClosure ℚ ℂ :=
      dot_rat_mem_alg hθalg
    by_cases hC0 : C = 0
    · have g2 : ∀ h, g (2, h) = 0 := fun h => congrFun (dot_rat_eq_zero hθ _ hC0) h
      rw [hC0, zero_mul, add_zero] at hABC
      by_cases hB0 : B = 0
      · have g1 : ∀ h, g (1, h) = 0 := fun h => congrFun (dot_rat_eq_zero hθ _ hB0) h
        rw [hB0, zero_mul, add_zero] at hABC
        have hA0 : A = 0 := (mul_eq_zero.mp hABC).resolve_right varpi_ne_zero'
        have g0 : ∀ h, g (0, h) = 0 := fun h => congrFun (dot_rat_eq_zero hθ _ hA0) h
        rintro ⟨k, h⟩
        fin_cases k
        exacts [g0 h, g1 h, g2 h]
      · exfalso
        apply hM
        rw [← mem_algebraicClosure_iff]
        have : (omegaRho : ℂ) / varpi = -A / B := by
          rw [div_eq_div_iff varpi_ne_zero' hB0]; linear_combination hABC
        rw [this]
        exact div_mem (neg_mem (hq _)) (hq _)
    · exfalso
      refine hnot (-A / C) (-B / C) (mem_algebraicClosure_iff.mp (div_mem (neg_mem (hq _)) (hq _)))
        (mem_algebraicClosure_iff.mp (div_mem (neg_mem (hq _)) (hq _))) ?_
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hC0]
      linear_combination hABC
  set e := Fintype.equivFin (Fin 3 × (Fin r × Fin 2))
  set y : Fin (Fintype.card (Fin 3 × (Fin r × Fin 2))) → TXG r := y0 ∘ e.symm with hy
  have hli' : LinearIndependent ℚ y := hli.comp _ e.symm.injective
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y)) = 3 * n := by
    rw [finrank_span_eq_card hli']; simp [n, Fintype.card_prod]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hmem : ∀ p, y0 p ∈ Submodule.span ℚ (Set.range y) := fun p =>
    Submodule.subset_span ⟨e p, by simp [hy]⟩
  -- `κ ≥ 2n`
  have hk : 2 * n ≤ finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXG b).per) := by
    let f : Fin 2 × (Fin r × Fin 2) → ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXG b).per) := fun p =>
      ⟨y0 (Fin.castSucc p.1, p.2), hmem _, by
        obtain ⟨k, h⟩ := p
        fin_cases k
        · exact P1_mem_per β h
        · exact P2_mem_per β h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp (Submodule.span ℚ (Set.range y) ⊓ (gmXG b).per).subtype
      exact hli.comp (fun p : Fin 2 × (Fin r × Fin 2) => (Fin.castSucc p.1, p.2))
        (fun p q hpq => by
          obtain ⟨k, h⟩ := p; obtain ⟨k', h'⟩ := q
          simp only [Prod.mk.injEq] at hpq
          obtain ⟨hk, rfl⟩ := hpq
          rw [Fin.castSucc_inj] at hk; rw [hk])
    have := hf.fintype_card_le_finrank
    simpa [n, Fintype.card_prod, mul_comm] using this
  -- `V''`, `W''`
  have hTX := finrank_TXG (r := r)
  have hV := finrank_ker_phiXG (b := b) (β * etaRho)
  have hWfin : finrank ℂ (Submodule.span ℂ (Set.range (wXG b))) = 2 * n := by
    rw [finrank_span_eq_card wXG_linearIndependent]; simp [n]; ring
  have hWrat : (gmXG b).Rational (Submodule.span ℂ (Set.range (wXG b))) := by
    refine ⟨Set.range (wXG b), ?_, rfl⟩
    rintro _ ⟨j | j, rfl⟩
    · refine ⟨(hθalg j).neg, fun k => ?_, fun _ => isAlgebraic_zero, isAlgebraic_zero⟩
      simp only [wXG, Pi.single_apply]
      exact isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero
    · refine ⟨(hθalg j).neg, fun _ => isAlgebraic_zero, fun k => ?_, isAlgebraic_zero⟩
      simp only [wXG, Pi.single_apply]
      exact isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero
  have hk_le : finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXG b).per) ≤ 3 * n := by
    have := Submodule.finrank_mono
      (show Submodule.span ℚ (Set.range y) ⊓ (gmXG b).per ≤ Submodule.span ℚ (Set.range y) from
        inf_le_left)
    omega
  obtain ⟨S, hsub, hne, hle⟩ := hW hg₂ hg₃ hg₂' hg₃' r b hb
    (LinearMap.ker (phiXG b (β * etaRho))) (Submodule.span ℂ (Set.range (wXG b))) _ y
    (by omega) (wXG_le_V _) hWrat
    (fun i => ⟨genX_mem_V hb hIK hr3K hβK zX wX zY wY a t hrel _,
      genX_mem_lam β zX wX zY wY a t hX hY ha ht _⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
        ((0 : ℤ) + 2 * ((2 * n + 1 : ℕ) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXG b).per)) *
          ((finrank ℂ (TXG r) : ℤ) - 1 - finrank ℂ (Submodule.span ℂ (Set.range (wXG b)))))
      rw [hfinY, hWfin, hTX]; push_cast; omega)
  rcases hsub with rfl | ⟨x, hxS, ⟨hx1, hx2, hx3, hx4⟩, hx⟩
  · exact hne rfl
  · have hxV := hle hxS
    rw [LinearMap.mem_ker, phiXG_apply] at hxV
    have hp1 : psiX1 b x ∈ algebraicClosure ℚ ℂ := by
      rw [psiX1_apply, dotL_apply, dotL_apply]
      refine add_mem (add_mem (mem_algebraicClosure_iff.mpr hx1) ?_) ?_ <;>
        exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
          (mem_algebraicClosure_iff.mpr (by tauto))
    have hp2 : psiX2 x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr hx4
    have hc : β * etaRho ≠ 0 := mul_ne_zero hβ0 etaRho_ne_zero
    have hpsi2 : psiX2 x ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at hxV
      have h1 : psiX1 b x = 0 := (mul_eq_zero.mp hxV).resolve_left hc
      rcases hx with h | h
      · exact h h1
      · exact h h0
    apply hΓ
    rw [← mem_algebraicClosure_iff]
    have hvar : (varpi : ℂ) = β * etaRho * psiX1 b x / psiX2 x := by
      rw [eq_div_iff hpsi2]; linear_combination (-1 : ℂ) * hxV
    have hval : (varpi : ℂ) * omegaRho / Real.pi = 2 * β * psiX1 b x / (r3 * psiX2 x) := by
      have hO := omegaRho_ne_zero
      have hr0 := r3_ne_zero
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      rw [hvar, etaRho]
      field_simp
    rw [hval]
    have h2 : (2 : ℂ) ∈ algebraicClosure ℚ ℂ := by simp
    exact div_mem (mul_mem (mul_mem h2 (mem_algebraicClosure_iff.mpr hβ)) hp1)
      (mul_mem (mem_algebraicClosure_iff.mpr isAlgebraic_r3) hp2)

/-! ## Theorem MX and Corollary MX1 -/

/-- **Named input (Wüstholz 1989, analytic subgroup theorem).** A `ℚ̄`-linear relation between `1`, an elliptic logarithm
on `E_i`, one on `E_ρ`, `ϖ` and `Ω_ρ` splits: apply the theorem to `E_i² × E_ρ² × G_a` at `(z_X, ϖ, z_Y, Ω_ρ, a)`; the
smallest algebraic subgroup is a product (the curves are non-isogenous, and there are no homomorphisms between `G_a`
and an abelian variety), so the linear form vanishes on each factor. -/
def WuestholzMX : Prop :=
  ∀ zX wX zY wY a x x' : ℂ, LogNat lemniscatic etaLem zX wX → LogNat equianharmonic etaR zY wY →
    IsAlgebraic ℚ a → IsAlgebraic ℚ x → IsAlgebraic ℚ x' →
    zX + zY + a = x * varpi + x' * omegaRho → a = 0 ∧ zX = x * varpi ∧ zY = x' * omegaRho

/-- **Named input (Masser 1975; also Wüstholz on `E²`).** An elliptic logarithm that is an algebraic multiple of the period
is a `k`-multiple of it (`k` = the CM field), i.e. the point is torsion. -/
def MasserCM : Prop :=
  (∀ z w x : ℂ, LogNat lemniscatic etaLem z w → IsAlgebraic ℚ x → z = x * varpi →
      ∃ p q : ℚ, x = p + q * I) ∧
    (∀ z w x : ℂ, LogNat equianharmonic etaR z w → IsAlgebraic ℚ x → z = x * omegaRho →
      ∃ p q : ℚ, x = p + q * rho)

/-- **Named input (Laurent 1980).** For non-torsion `u` on `E_i` with `℘(u), ℘'(u)` algebraic, `ζ(u)` is transcendental
(`1, u, ζ(u)` are `ℚ̄`-linearly independent). -/
def LaurentZeta : Prop :=
  ∀ u : ℂ, u ∉ lemniscatic.lattice → IsAlgebraic ℚ (lemniscatic.weierstrassP u) →
    IsAlgebraic ℚ (lemniscatic.derivWeierstrassP u) → (¬ ∃ p q : ℚ, u = (p + q * I) * varpi) →
    Transcendental ℚ (LSG.Weierstrass.zeta lemniscatic u)

lemma transcendental_omegaRho_div_varpi (hWu : WuestholzMX) : Transcendental ℚ ((omegaRho : ℂ) / varpi) := by
  intro halg
  have hv := varpi_ne_zero'
  have hO := omegaRho_ne_zero
  have hY : LogNat equianharmonic etaR omegaRho etaRho :=
    Or.inl ⟨1, 0, by simp [equianharmonic], isAlg_zero_of (by simp [etaR])⟩
  have hX : LogNat lemniscatic etaLem 0 0 :=
    Or.inl ⟨0, 0, by simp, isAlg_zero_of (by simp [etaLem])⟩
  obtain ⟨-, h1, -⟩ := hWu 0 0 omegaRho etaRho 0 ((omegaRho : ℂ) / varpi) 0 hX hY isAlgebraic_zero halg
    isAlgebraic_zero (by rw [div_mul_cancel₀ _ hv]; ring)
  have : (omegaRho : ℂ) / varpi = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hv
  exact hO (by rwa [div_eq_zero_iff, or_iff_left hv] at this)

/-- **Theorem MX** (paper, Theorem MX) for every `β ∈ ℚ̄ˣ`: if `X ∈ Λ(E_i^♮)`, `Y ∈ Λ(E_ρ^♮)`, `a, t ∈ ℚ̄` and
`(z(X) + z(Y) + a) β η(Ω_ρ) = (w(X) + w(Y) + t) ϖ`, then `a = 0`, `z(X) ∈ ℚ(i)ϖ` and `z(Y) ∈ ℚ(ρ)Ω_ρ`. Hypotheses:
W88 §5d (`hW`), `g₂, g₃` algebraic, and the named classical inputs `hΓ`, `WuestholzMX`, `MasserCM`. -/
theorem mx_full (hW : Thm11KappaMXG) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (hWu : WuestholzMX) (hMa : MasserCM)
    (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : LogNat lemniscatic etaLem zX wX) (hY : LogNat equianharmonic etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (β * etaRho) = (wX + wY + t) * varpi) :
    a = 0 ∧ (∃ p q : ℚ, zX = (p + q * I) * varpi) ∧ (∃ p q : ℚ, zY = (p + q * rho) * omegaRho) := by
  obtain ⟨x, x', hx, hx', hxx⟩ := mx_K hW hg₂ hg₃ hg₂' hg₃' hΓ (transcendental_omegaRho_div_varpi hWu)
    β hβ hβ0 zX wX zY wY a t hX hY ha ht hrel
  obtain ⟨ha0, hzX, hzY⟩ := hWu zX wX zY wY a x x' hX hY ha hx hx' hxx
  obtain ⟨p, q, hpq⟩ := hMa.1 zX wX x hX hx hzX
  obtain ⟨p', q', hpq'⟩ := hMa.2 zY wY x' hY hx' hzY
  exact ⟨ha0, ⟨p, q, by rw [hzX, hpq]⟩, ⟨p', q', by rw [hzY, hpq']⟩⟩

/-- **Corollary MX1**: for `u` with `℘(u), ℘'(u) ∈ ℚ̄` and `u ∉ ℚ(i)ϖ`, and `a, t ∈ ℚ̄`, the number
`ϖ Ω_ρ (ζ(u) + t) / (π (u + a))` is transcendental. (`u + a ≠ 0` by Schneider's theorem on `℘` at algebraic points.) -/
theorem mx1 (hW : Thm11KappaMXG) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (hWu : WuestholzMX) (hMa : MasserCM)
    (hLa : LaurentZeta) (u : ℂ)
    (hwp : IsAlgebraic ℚ (lemniscatic.weierstrassP u)) (hwp' : IsAlgebraic ℚ (lemniscatic.derivWeierstrassP u))
    (hu' : ¬ ∃ p q : ℚ, u = (p + q * I) * varpi) (a t : ℂ) (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t) :
    Transcendental ℚ ((varpi : ℂ) * omegaRho * (LSG.Weierstrass.zeta lemniscatic u + t) /
      (Real.pi * (u + a))) := by
  intro halg
  have hu : u ∉ lemniscatic.lattice := by
    intro hl
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hl
    exact hu' ⟨m, n, by rw [← hmn]; simp [lemniscatic]; ring⟩
  set ζu := LSG.Weierstrass.zeta lemniscatic u
  have hv := varpi_ne_zero'
  have hO := omegaRho_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hua : u + a ≠ 0 := by
    intro h0
    have hu_eq : u = -a := by linear_combination h0
    exact LSG.Schneider.wp_transcendental hg₂ hg₃ (hu_eq ▸ ha.neg) hu hwp
  obtain ⟨q, hqdef⟩ : ∃ q : ℂ, q = (varpi : ℂ) * omegaRho * (ζu + t) / (Real.pi * (u + a)) := ⟨_, rfl⟩
  rw [← hqdef] at halg
  by_cases hq0 : q = 0
  · have hz : ζu + t = 0 := by
      rw [hqdef] at hq0
      rcases div_eq_zero_iff.mp hq0 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (mul_ne_zero hv hO)
        · exact h'
      · exact absurd h (mul_ne_zero hpi hua)
    apply hLa u hu hwp hwp' hu'
    have : LSG.Weierstrass.zeta lemniscatic u = -t := by linear_combination hz
    rw [this]; exact ht.neg
  · have hβ : IsAlgebraic ℚ (q * r3 / 2) := by
      rw [← mem_algebraicClosure_iff]
      exact div_mem (mul_mem (mem_algebraicClosure_iff.mpr halg)
        (mem_algebraicClosure_iff.mpr isAlgebraic_r3)) (by simp)
    have hβ0 : q * r3 / 2 ≠ 0 := div_ne_zero (mul_ne_zero hq0 r3_ne_zero) two_ne_zero
    have hX : LogNat lemniscatic etaLem u ζu :=
      Or.inr ⟨hu, hwp, hwp', isAlg_zero_of (by simp [ζu])⟩
    have hY : LogNat equianharmonic etaR 0 0 :=
      Or.inl ⟨0, 0, by simp, isAlg_zero_of (by simp [etaR])⟩
    have hrel : (u + 0 + a) * (q * r3 / 2 * etaRho) = (ζu + 0 + t) * varpi := by
      have hr := r3_ne_zero
      have hdef : q * (Real.pi * (u + a)) = varpi * omegaRho * (ζu + t) := by
        rw [hqdef, div_mul_cancel₀ _ (mul_ne_zero hpi hua)]
      have e1 : (u + 0 + a) * (q * r3 / 2 * etaRho) = q * (Real.pi * (u + a)) / omegaRho := by
        rw [etaRho]; field_simp; ring
      rw [e1, hdef]; field_simp; ring
    obtain ⟨-, ⟨p, q', hpq⟩, -⟩ := mx_full hW hg₂ hg₃ hg₂' hg₃' hΓ hWu hMa (q * r3 / 2) hβ hβ0 u ζu 0 0 a t
      hX hY ha ht hrel
    exact hu' ⟨p, q', hpq⟩

end CM4E.Gen
