/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MXGen

/-!
# Proposition D′ (Theorem MX′, `K`-form)

Twisted variant of Theorem MX (paper [I], §`sec:MXP`): `G = E_i^♮ × E_ρ^♮ × G_a²`,
`Ψ'(X_i, X_ρ, a₁, a₂) = (z(X_i) + w(X_ρ) + a₁, w(X_i) + z(X_ρ) + a₂)`, `V' = ℂ(ϖ, βΩ_ρ)`. With an adapted basis `θ` of a
number field `K ∋ i` (`n = [K : ℚ]`), the quotient `G'' = G^n / U'`, `U' = {θᵀ(w_ρ + a₁) = θᵀ(w_i + a₂) = 0}`, is the
push-out of `(E_i^n × E_ρ^n)^♮` along `(w_i, w_ρ) ↦ (θᵀw_i, θᵀw_ρ)`, an extension of `E_i^n × E_ρ^n` by `G_a²`.
Tangent coordinates `(z_i, z_ρ, s₁, s₂)`, `s₁ = θᵀ(w_ρ + a₁)`, `s₂ = θᵀ(w_i + a₂)`, and `Ψ'' = (θᵀz_i + s₁, θᵀz_ρ + s₂)`;
`d₀ = d₁ = 0`, `d₂ = 2n + 2`. W88 §5d with `m = 3n`, `κ ≥ 2n`, `t = 2n` needs `3n > 2n + 4`, i.e. `n ≥ 6`.

Soundness facts (not checked by Lean): as for `gmXG` (`CM4E/Gen/MXGen.lean`) for the logarithms and periods; `G''` is a
quotient of an anti-affine group, so `d₀ = d₁ = 0`; and no nonzero connected subgroup has tangent space in `ker Ψ''`
(a canonical lift `B^♮` of `B_{S_i} × B_{S_ρ}` has tangent space in `ker Φ'` only if `ψ(S) = φ(S) = 0`, i.e. `B = 0`, by
Lemma K; so `U'` is the largest connected subgroup with tangent space in `ker Φ'`).

Corollary deg2 (i) (`π, ϖ, Ω_ρ, ϖΩ_ρ` linearly independent over `ℚ̄`) is derived from it in `CM4E/Gen/Deg2.lean`.
-/

open Complex Module CM4E.Waldschmidt CM4E.MX

namespace CM4E.Gen

variable {r : ℕ}

/-- The tangent space `ℂ^n × ℂ^n × ℂ × ℂ`, coordinates `(z_i, z_ρ, s₁, s₂)`. -/
abbrev TXP (r : ℕ) := (Fin r × Fin 2 → ℂ) × (Fin r × Fin 2 → ℂ) × ℂ × ℂ

variable (b : Fin r → ℂ)

/-- `Ψ''₁ = θᵀz_i + s₁`. -/
noncomputable def psiP1 : TXP r →ₗ[ℂ] ℂ :=
  dotL (theta I b) ∘ₗ LinearMap.fst ℂ _ _ +
    LinearMap.fst ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _
/-- `Ψ''₂ = θᵀz_ρ + s₂`. -/
noncomputable def psiP2 : TXP r →ₗ[ℂ] ℂ :=
  dotL (theta I b) ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _ +
    LinearMap.snd ℂ ℂ ℂ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _

lemma psiP1_apply (v : TXP r) : psiP1 b v = dotL (theta I b) v.1 + v.2.2.1 := by simp [psiP1]
lemma psiP2_apply (v : TXP r) : psiP2 b v = dotL (theta I b) v.2.1 + v.2.2.2 := by simp [psiP2]

/-- `(z, w) ∈ T(E_i^♮)` in copy `h` (its fibre value goes to `s₂`). -/
noncomputable def gPI (h : Fin r × Fin 2) (z w : ℂ) : TXP r := (Pi.single h z, 0, 0, theta I b h * w)
/-- `(z, w) ∈ T(E_ρ^♮)` in copy `h` (its fibre value goes to `s₁`). -/
noncomputable def gPR (h : Fin r × Fin 2) (z w : ℂ) : TXP r := (0, Pi.single h z, theta I b h * w, 0)
/-- `(a₁, a₂) ∈ T(G_a²)` in copy `h`. -/
noncomputable def gPA (h : Fin r × Fin 2) (a c : ℂ) : TXP r := (0, 0, theta I b h * a, theta I b h * c)

/-- Generators of `lam`. -/
def lamGenP : Set (TXP r) :=
  {v | ∃ h z w, LogNat lemniscatic etaLem z w ∧ v = gPI b h z w} ∪
    {v | ∃ h z w, LogNat equianharmonic etaR z w ∧ v = gPR b h z w} ∪
    {v | ∃ h a c, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ c ∧ v = gPA b h a c}

/-- Period generators in copy `j`. -/
noncomputable def GP1 (j : Fin r × Fin 2) : TXP r := gPI b j varpi (Real.pi / varpi)
noncomputable def GP2 (j : Fin r × Fin 2) : TXP r := gPI b j (I * varpi) (-I * (Real.pi / varpi))
noncomputable def HP1 (j : Fin r × Fin 2) : TXP r := gPR b j omegaRho etaRho
noncomputable def HP2 (j : Fin r × Fin 2) : TXP r := gPR b j (rho * omegaRho) (rhoBar * etaRho)

/-- The `ℚ`-span of the periods. -/
noncomputable def perXP : Submodule ℚ (TXP r) :=
  Submodule.span ℚ (Set.range (GP1 b) ∪ Set.range (GP2 b) ∪ Set.range (HP1 b) ∪ Set.range (HP2 b))

/-- Algebraic coordinates. -/
def algXP (v : TXP r) : Prop :=
  (∀ j, IsAlgebraic ℚ (v.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.2.1 j)) ∧ IsAlgebraic ℚ v.2.2.1 ∧
    IsAlgebraic ℚ v.2.2.2

/-- The model of `G''` (extension of `E_i^n × E_ρ^n` by `G_a²`). -/
noncomputable def gmXP : GroupModel (TXP r) where
  d₁ := 0
  d₂ := 2 * Fintype.card (Fin r × Fin 2) + 2
  alg := algXP
  lam := (Submodule.span ℚ (lamGenP b) : Set (TXP r))
  per := perXP b
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algXP x ∧ (psiP1 b x ≠ 0 ∨ psiP2 b x ≠ 0)

/-- **The hypothesis for Proposition D′**: W88 §5d for `G''`, every adapted basis of a number field containing `i`. -/
def Thm11KappaMXP : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ →
    IsAlgebraic ℚ equianharmonic.g₂ → IsAlgebraic ℚ equianharmonic.g₃ →
    ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedFieldBasis I b → HyperplaneKappa (gmXP b)

/-! ## `Ψ''` on generators and explicit lifts -/

section Lifts

variable {b}

lemma psiP1_gPI (h : Fin r × Fin 2) (z w : ℂ) : psiP1 b (gPI b h z w) = theta I b h * z := by
  simp [psiP1_apply, gPI, dotL_single]
lemma psiP2_gPI (h : Fin r × Fin 2) (z w : ℂ) : psiP2 b (gPI b h z w) = theta I b h * w := by
  simp [psiP2_apply, gPI]
lemma psiP1_gPR (h : Fin r × Fin 2) (z w : ℂ) : psiP1 b (gPR b h z w) = theta I b h * w := by
  simp [psiP1_apply, gPR]
lemma psiP2_gPR (h : Fin r × Fin 2) (z w : ℂ) : psiP2 b (gPR b h z w) = theta I b h * z := by
  simp [psiP2_apply, gPR, dotL_single]
lemma psiP1_gPA (h : Fin r × Fin 2) (a c : ℂ) : psiP1 b (gPA b h a c) = theta I b h * a := by
  simp [psiP1_apply, gPA]
lemma psiP2_gPA (h : Fin r × Fin 2) (a c : ℂ) : psiP2 b (gPA b h a c) = theta I b h * c := by
  simp [psiP2_apply, gPA]

lemma psiP_rsmul (f : TXP r →ₗ[ℂ] ℂ) (q : ℚ) (v : TXP r) : f (q • v) = (q : ℂ) * f v := by
  rw [map_rat_smul f q v, Rat.smul_def]

variable (b) in
/-- A lift on `E_i^♮` with `Ψ''`-contribution `(xϖ, yπ/ϖ)`. -/
noncomputable def liftPI (x y : ℂ) : TXP r :=
  ∑ j, (coordsA I b ((x + y) / 2) j) • GP1 b j + ∑ j, (coordsA I b ((x - y) / (2 * I)) j) • GP2 b j

variable (b) in
/-- A lift on `E_ρ^♮` with `Ψ''`-contribution `(yη_ρ, xΩ_ρ)`. -/
noncomputable def liftPR (x y : ℂ) : TXP r :=
  ∑ j, (coordsA I b (x - rho * ((x - y) / (rho - rhoBar))) j) • HP1 b j +
    ∑ j, (coordsA I b ((x - y) / (rho - rhoBar)) j) • HP2 b j

lemma psi_liftPI (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) {x y : ℂ} (hx : x ∈ Kspan I b)
    (hy : y ∈ Kspan I b) :
    psiP1 b (liftPI b x y) = x * varpi ∧ psiP2 b (liftPI b x y) = y * (Real.pi / varpi) := by
  have hU : (x + y) / 2 ∈ Kspan I b := by
    rw [div_eq_mul_inv]; exact hb.mul_mem _ (add_mem hx hy) _ (hb.inv_mem _ (two_mem hb))
  have hV : (x - y) / (2 * I) ∈ Kspan I b := by
    rw [div_eq_mul_inv]
    exact hb.mul_mem _ (sub_mem hx hy) _ (hb.inv_mem _ (hb.mul_mem _ (two_mem hb) _ hI))
  have hv := varpi_ne_zero'
  constructor
  · simp only [liftPI, GP1, GP2, map_add, map_sum, psiP_rsmul, psiP1_gPI]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    field_simp; ring_nf
  · simp only [liftPI, GP1, GP2, map_add, map_sum, psiP_rsmul, psiP2_gPI]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    field_simp; ring_nf

lemma psi_liftPR (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {x y : ℂ}
    (hx : x ∈ Kspan I b) (hy : y ∈ Kspan I b) :
    psiP1 b (liftPR b x y) = y * etaRho ∧ psiP2 b (liftPR b x y) = x * omegaRho := by
  have hd : rho - rhoBar ≠ 0 := by rw [rho_sub_rhoBar]; exact mul_ne_zero Complex.I_ne_zero r3_ne_zero
  have hV : (x - y) / (rho - rhoBar) ∈ Kspan I b := by
    rw [div_eq_mul_inv]
    exact hb.mul_mem _ (sub_mem hx hy) _
      (hb.inv_mem _ (sub_mem (rho_mem hb hI hr3) (rhoBar_mem hb hI hr3)))
  have hU : x - rho * ((x - y) / (rho - rhoBar)) ∈ Kspan I b :=
    sub_mem hx (hb.mul_mem _ (rho_mem hb hI hr3) _ hV)
  constructor
  · simp only [liftPR, HP1, HP2, map_add, map_sum, psiP_rsmul, psiP1_gPR]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    field_simp; ring
  · simp only [liftPR, HP1, HP2, map_add, map_sum, psiP_rsmul, psiP2_gPR]
    rw [sum_coef, sum_coef, coordsA_spec hU, coordsA_spec hV]
    ring

end Lifts

/-! ## Generators -/

section Gens

variable {b}

/-- Lift of `θ_h w₁' = θ_h (ϖ, βΩ_ρ)`. -/
noncomputable def P1' (b : Fin r → ℂ) (β : ℂ) (h : Fin r × Fin 2) : TXP r :=
  liftPI b (theta I b h) 0 + liftPR b (theta I b h * β) 0
/-- Lift of `θ_h w₂' = θ_h (η_ρ, β (2/√3) η_i)`. -/
noncomputable def P2' (b : Fin r → ℂ) (β : ℂ) (h : Fin r × Fin 2) : TXP r :=
  liftPR b 0 (theta I b h) + liftPI b 0 (theta I b h * β * (2 * r3 / 3))
/-- Lift of `θ_h v`, `v = Ψ'(X, Y, a, c)`. -/
noncomputable def DP (b : Fin r → ℂ) (zX wX zY wY a c : ℂ) (h : Fin r × Fin 2) : TXP r :=
  gPI b h zX wX + gPR b h zY wY + gPA b h a c

/-- The `3n` generators. -/
noncomputable def genP (b : Fin r → ℂ) (β zX wX zY wY a c : ℂ) : Fin 3 × (Fin r × Fin 2) → TXP r :=
  fun p => ![P1' b β p.2, P2' b β p.2, DP b zX wX zY wY a c p.2] p.1

lemma psi_P1' (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {β : ℂ}
    (hβ : β ∈ Kspan I b) (h : Fin r × Fin 2) :
    psiP1 b (P1' b β h) = theta I b h * varpi ∧ psiP2 b (P1' b β h) = theta I b h * β * omegaRho := by
  have hθ : theta I b h ∈ Kspan I b := Submodule.subset_span ⟨h, rfl⟩
  obtain ⟨a1, a2⟩ := psi_liftPI hb hI hθ (Submodule.zero_mem _)
  obtain ⟨c1, c2⟩ := psi_liftPR hb hI hr3 (hb.mul_mem _ hθ _ hβ) (Submodule.zero_mem _)
  simp only [P1', map_add, a1, a2, c1, c2]
  constructor <;> ring

lemma psi_P2' (hb : IsAdaptedFieldBasis I b) (hI : I ∈ Kspan I b) (hr3 : r3 ∈ Kspan I b) {β : ℂ}
    (hβ : β ∈ Kspan I b) (h : Fin r × Fin 2) :
    psiP1 b (P2' b β h) = theta I b h * etaRho ∧
      psiP2 b (P2' b β h) = theta I b h * β * (2 * r3 / 3) * (Real.pi / varpi) := by
  have hθ : theta I b h ∈ Kspan I b := Submodule.subset_span ⟨h, rfl⟩
  have h3 : (3 : ℂ) ∈ Kspan I b := by
    have := Submodule.smul_mem _ (3 : ℚ) hb.one_mem
    simpa [Rat.smul_def] using this
  have hc : 2 * r3 / 3 ∈ Kspan I b := by
    rw [div_eq_mul_inv]; exact hb.mul_mem _ (hb.mul_mem _ (two_mem hb) _ hr3) _ (hb.inv_mem _ h3)
  obtain ⟨a1, a2⟩ := psi_liftPR hb hI hr3 (Submodule.zero_mem _) hθ
  obtain ⟨c1, c2⟩ := psi_liftPI hb hI (Submodule.zero_mem _) (hb.mul_mem _ (hb.mul_mem _ hθ _ hβ) _ hc)
  simp only [P2', map_add, a1, a2, c1, c2]
  constructor <;> ring

lemma psi_DP (zX wX zY wY a c : ℂ) (h : Fin r × Fin 2) :
    psiP1 b (DP b zX wX zY wY a c h) = theta I b h * (zX + wY + a) ∧
      psiP2 b (DP b zX wX zY wY a c h) = theta I b h * (wX + zY + c) := by
  simp only [DP, map_add, psiP1_gPI, psiP1_gPR, psiP1_gPA, psiP2_gPI, psiP2_gPR, psiP2_gPA]
  constructor <;> ring

lemma liftPI_mem_per (x y : ℂ) : liftPI b x y ∈ perXP b :=
  add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))))

lemma liftPR_mem_per (x y : ℂ) : liftPR b x y ∈ perXP b :=
  add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩))))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩)))

lemma perXP_le_lam : perXP b ≤ Submodule.span ℚ (lamGenP b) := by
  rw [perXP, Submodule.span_le]
  rintro _ (((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨j, _, _, logXG_G1, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨j, _, _, logXG_G2, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨j, _, _, logXG_H1, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨j, _, _, logXG_H2, rfl⟩))

end Gens

/-! ## A field of degree at least `6` -/

lemma rat_sqrt23 (a c e : ℚ) (h : (a : ℝ) + c * Real.sqrt 3 + e * Real.sqrt 2 = 0) :
    a = 0 ∧ c = 0 ∧ e = 0 := by
  have h3 : Irrational (Real.sqrt 3) := by simpa using Nat.prime_three.irrational_sqrt
  have h2 := irrational_sqrt_two
  have h6 : Irrational (Real.sqrt 6) := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, irrational_sqrt_natCast_iff]
    rintro ⟨k, hk⟩
    have : k ≤ 3 := by nlinarith
    interval_cases k <;> omega
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s6 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  -- `(a + c√3)² = 2e²` gives `2ac√3 ∈ ℚ`
  have hsq : ((a : ℝ) + c * Real.sqrt 3) ^ 2 = 2 * e ^ 2 := by
    have : (a : ℝ) + c * Real.sqrt 3 = -(e * Real.sqrt 2) := by linarith
    rw [this]; ring_nf; rw [s2]
  have hac : a * c = 0 := by
    by_contra hne
    apply h3
    refine ⟨(2 * e ^ 2 - a ^ 2 - 3 * c ^ 2) / (2 * a * c), ?_⟩
    have hq : (2 * a * c : ℚ) ≠ 0 := by
      intro h0; apply hne
      have : (2 : ℚ) * (a * c) = 0 := by linear_combination h0
      exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    have hr : (2 * a * c : ℝ) ≠ 0 := by exact_mod_cast hq
    have key : (2 * a * c : ℝ) * Real.sqrt 3 = 2 * e ^ 2 - a ^ 2 - 3 * c ^ 2 := by
      linear_combination hsq - (c : ℝ) ^ 2 * s3
    push_cast
    rw [div_eq_iff hr]
    linear_combination -key
  rcases mul_eq_zero.mp hac with ha | hc
  · subst ha
    -- `c√3 = −e√2`, so `c√6 = −2e` after multiplying by `√2`
    by_cases hc : c = 0
    · subst hc
      have : (e : ℝ) * Real.sqrt 2 = 0 := by simpa using h
      rcases mul_eq_zero.mp this with he | he
      · exact ⟨rfl, rfl, by exact_mod_cast he⟩
      · exact absurd he (Real.sqrt_pos.mpr (by norm_num)).ne'
    · exfalso; apply h6
      refine ⟨-2 * e / c, ?_⟩
      have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      have : (c : ℝ) * Real.sqrt 6 = -2 * e := by
        have e1 := congrArg (· * Real.sqrt 2) h
        push_cast at e1
        rw [← s6]; linear_combination e1 - (e : ℝ) * s2
      push_cast
      rw [div_eq_iff hc']
      linear_combination -this
  · subst hc
    have : (a : ℝ) + e * Real.sqrt 2 = 0 := by simpa using h
    by_cases he : e = 0
    · subst he; simp at this; exact ⟨by exact_mod_cast this, rfl, rfl⟩
    · exfalso; apply h2
      refine ⟨-a / e, ?_⟩
      have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
      push_cast; field_simp; linarith

lemma linearIndependent_five :
    LinearIndependent ℚ ![(1 : ℂ), I, r3, I * r3, ((Real.sqrt 2 : ℝ) : ℂ)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Rat.smul_def] at hg
  have hre := congrArg Complex.re hg
  have him := congrArg Complex.im hg
  simp [r3] at hre him
  obtain ⟨g1, g3⟩ : g 1 = 0 ∧ g 3 = 0 := by
    have hq := quad_inj (s := Real.sqrt 3) (by simpa using Nat.prime_three.irrational_sqrt) 0 (g 1) 0 (g 3)
    have := hq (by
      apply Complex.ext <;> simp [r3] <;> linarith)
    exact ⟨this.2.1, this.2.2.2⟩
  obtain ⟨g0, g2, g4⟩ := rat_sqrt23 (g 0) (g 2) (g 4) (by linarith)
  intro k; fin_cases k <;> simp [g0, g1, g2, g3, g4]

/-- An adapted basis with `r ≥ 3` (so `[K : ℚ] ≥ 6`) whose span contains `i`, `√3` and the given finite set. -/
lemma exists_adapted_basis_three (S : Finset ℂ) (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ r : ℕ, 3 ≤ r ∧ ∃ b : Fin r → ℂ, IsAdaptedFieldBasis I b ∧ I ∈ Kspan I b ∧ r3 ∈ Kspan I b ∧
      ∀ s ∈ S, s ∈ Kspan I b := by
  classical
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  have hr2 : IsAlgebraic ℚ ((Real.sqrt 2 : ℝ) : ℂ) := by simpa using isAlgebraic_sqrt_nat 2
  obtain ⟨r, -, b, hb, hSb⟩ := exists_adapted_basis I hI (by simp) ⟨-1, 0, by push_cast; simp⟩
    (S ∪ {I, r3, ((Real.sqrt 2 : ℝ) : ℂ)}) (by
      intro s hs
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with hs | rfl | rfl | rfl
      exacts [hS s hs, hI, isAlgebraic_r3, hr2])
  have hIK : I ∈ Kspan I b := hSb I (by simp)
  have hr3K : r3 ∈ Kspan I b := hSb r3 (by simp)
  have hr2K : ((Real.sqrt 2 : ℝ) : ℂ) ∈ Kspan I b := hSb _ (by simp)
  refine ⟨r, ?_, b, hb, hIK, hr3K, fun s hs => hSb s (by simp [hs])⟩
  -- five `ℚ`-independent elements of `K` force `2r ≥ 5`
  have hmem : ∀ k, ![(1 : ℂ), I, r3, I * r3, ((Real.sqrt 2 : ℝ) : ℂ)] k ∈ Kspan I b := by
    intro k; fin_cases k
    exacts [hb.one_mem, hIK, hr3K, hb.mul_mem _ hIK _ hr3K, hr2K]
  let f : Fin 5 → Kspan I b := fun k => ⟨_, hmem k⟩
  have hf : LinearIndependent ℚ f := LinearIndependent.of_comp (Kspan I b).subtype linearIndependent_five
  haveI : FiniteDimensional ℚ (Kspan I b) := FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have h1 := hf.fintype_card_le_finrank
  have h2 : finrank ℚ (Kspan I b) = 2 * r := by
    rw [Kspan, finrank_span_eq_card hb.indep]; simp [Fintype.card_prod]; ring
  simp at h1
  omega

/-! ## Proposition D′ -/

section Main

variable {b}

lemma genP_mem_lam (β zX wX zY wY a c : ℂ) (hX : LogNat lemniscatic etaLem zX wX)
    (hY : LogNat equianharmonic etaR zY wY) (ha : IsAlgebraic ℚ a) (hc : IsAlgebraic ℚ c)
    (p : Fin 3 × (Fin r × Fin 2)) : genP b β zX wX zY wY a c p ∈ (gmXP b).lam := by
  show genP b β zX wX zY wY a c p ∈ Submodule.span ℚ (lamGenP b)
  obtain ⟨k, h⟩ := p
  fin_cases k
  · exact perXP_le_lam (add_mem (liftPI_mem_per _ _) (liftPR_mem_per _ _))
  · exact perXP_le_lam (add_mem (liftPR_mem_per _ _) (liftPI_mem_per _ _))
  · exact add_mem (add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, zX, wX, hX, rfl⟩)))
      (Submodule.subset_span (Or.inl (Or.inr ⟨h, zY, wY, hY, rfl⟩))))
      (Submodule.subset_span (Or.inr ⟨h, a, c, ha, hc, rfl⟩))

variable (b) in
/-- `c Ψ''₁ − ϖ Ψ''₂`; with `c = βΩ_ρ` its kernel is `V'' = Ψ''⁻¹(ℂ(ϖ, βΩ_ρ))`. -/
noncomputable def phiP (c : ℂ) : TXP r →ₗ[ℂ] ℂ := c • psiP1 b - (varpi : ℂ) • psiP2 b

lemma phiP_apply (c : ℂ) (v : TXP r) : phiP b c v = c * psiP1 b v - varpi * psiP2 b v := rfl

lemma finrank_TXP : finrank ℂ (TXP r) = 2 * Fintype.card (Fin r × Fin 2) + 2 := by
  simp [TXP, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring

lemma finrank_ker_phiP (c : ℂ) : finrank ℂ (LinearMap.ker (phiP b c)) + 1 = finrank ℂ (TXP r) := by
  have hsurj : Function.Surjective (phiP b c) := fun w =>
    ⟨(0, 0, 0, -w / varpi), by
      have hv := varpi_ne_zero'
      simp [phiP_apply, psiP1_apply, psiP2_apply]; field_simp⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiP b c)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
  omega

variable (b) in
/-- `(e_j, 0, −θ_j, 0)` and `(0, e_j, 0, −θ_j)` span `W'' = ker Ψ''`. -/
noncomputable def wXP : (Fin r × Fin 2) ⊕ (Fin r × Fin 2) → TXP r
  | .inl j => (Pi.single j 1, 0, -theta I b j, 0)
  | .inr j => (0, Pi.single j 1, 0, -theta I b j)

lemma wXP_linearIndependent : LinearIndependent ℂ (wXP b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rintro (j | j)
  · have := congrArg (fun v : TXP r => v.1 j) hg
    simpa [Fintype.sum_sum_type, wXP, Finset.sum_apply, Pi.single_apply, Prod.fst_sum] using this
  · have := congrArg (fun v : TXP r => v.2.1 j) hg
    simpa [Fintype.sum_sum_type, wXP, Finset.sum_apply, Pi.single_apply, Prod.snd_sum,
      Prod.fst_sum] using this

lemma wXP_le_V (c : ℂ) : Submodule.span ℂ (Set.range (wXP b)) ≤ LinearMap.ker (phiP b c) := by
  rw [Submodule.span_le]
  rintro _ ⟨j | j, rfl⟩ <;> simp [wXP, phiP_apply, psiP1_apply, psiP2_apply, dotL_single]

/-- **Proposition D′** (`K`-form of Theorem MX′, for `v ∈ Ψ'(Λ(G))`): if `X = (zX, wX) ∈ Λ(E_i^♮)`,
`Y = (zY, wY) ∈ Λ(E_ρ^♮)`, `a, c ∈ ℚ̄`, `β ∈ ℚ̄ˣ` and `(zX + wY + a) βΩ_ρ = (wX + zY + c) ϖ`, then
`zX + wY + a ∈ ℚ̄ϖ + ℚ̄η_ρ`. Hypotheses: W88 §5d for `G''` (`hW`), `g₂, g₃` algebraic, `ϖΩ_ρ/π ∉ ℚ̄` (`hΓ`) and
`Ω_ρ/ϖ ∉ ℚ̄` (`hM`) (Wüstholz). -/
theorem mxP_K (hW : Thm11KappaMXP) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi))
    (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a c : ℂ)
    (hX : LogNat lemniscatic etaLem zX wX) (hY : LogNat equianharmonic etaR zY wY)
    (ha : IsAlgebraic ℚ a) (hc : IsAlgebraic ℚ c)
    (hrel : (zX + wY + a) * (β * omegaRho) = (wX + zY + c) * varpi) :
    ∃ x x' : ℂ, IsAlgebraic ℚ x ∧ IsAlgebraic ℚ x' ∧ zX + wY + a = x * varpi + x' * etaRho := by
  by_contra hcon
  have hnot : ∀ x x' : ℂ, IsAlgebraic ℚ x → IsAlgebraic ℚ x' → zX + wY + a ≠ x * varpi + x' * etaRho :=
    fun x x' hx hx' h => hcon ⟨x, x', hx, hx', h⟩
  have hI : IsAlgebraic ℚ I := isAlgebraic_iff_isIntegral.mpr (Complex.isIntegral_I ℚ)
  obtain ⟨r, hr, b, hb, hIK, hr3K, hS⟩ := exists_adapted_basis_three {β} (by simpa using hβ)
  have hβK : β ∈ Kspan I b := hS β (by simp)
  have hθalg := theta_isAlgebraic hI hb.alg
  have hθ := hb.indep
  set n := Fintype.card (Fin r × Fin 2)
  have hn : n = 2 * r := by simp [n, Fintype.card_prod, mul_comm]
  have hv := varpi_ne_zero'
  -- `η_ρ / ϖ ∉ ℚ̄` (it is `(2/√3)·π/(ϖΩ_ρ)`)
  have hηv : Transcendental ℚ (etaRho / varpi) := by
    intro halg
    apply hΓ
    have hO := omegaRho_ne_zero
    have hr0 := r3_ne_zero
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hηne : etaRho / varpi ≠ 0 := div_ne_zero etaRho_ne_zero hv
    have : (varpi : ℂ) * omegaRho / Real.pi = 2 / (r3 * (etaRho / varpi)) := by
      rw [etaRho]; field_simp
    rw [this, ← mem_algebraicClosure_iff]
    exact div_mem (by simp) (mul_mem (mem_algebraicClosure_iff.mpr isAlgebraic_r3)
      (mem_algebraicClosure_iff.mpr halg))
  set y0 := genP b β zX wX zY wY a c
  have hli : LinearIndependent ℚ y0 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have e := congrArg (psiP1 b) hg
    rw [map_sum, map_zero] at e
    simp only [psiP_rsmul, Fintype.sum_prod_type, Fin.sum_univ_three] at e
    have e1 : ∀ h, psiP1 b (y0 (0, h)) = theta I b h * varpi := fun h => (psi_P1' hb hIK hr3K hβK h).1
    have e2 : ∀ h, psiP1 b (y0 (1, h)) = theta I b h * etaRho := fun h => (psi_P2' hb hIK hr3K hβK h).1
    have e3 : ∀ h, psiP1 b (y0 (2, h)) = theta I b h * (zX + wY + a) := fun h =>
      (psi_DP zX wX zY wY a c h).1
    simp only [e1, e2, e3] at e
    set A := dotL (theta I b) (fun h => ((g (0, h) : ℚ) : ℂ))
    set B := dotL (theta I b) (fun h => ((g (1, h) : ℚ) : ℂ))
    set C := dotL (theta I b) (fun h => ((g (2, h) : ℚ) : ℂ))
    have hABC : A * varpi + B * etaRho + C * (zX + wY + a) = 0 := by
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
        have hA0 : A = 0 := (mul_eq_zero.mp hABC).resolve_right hv
        have g0 : ∀ h, g (0, h) = 0 := fun h => congrFun (dot_rat_eq_zero hθ _ hA0) h
        rintro ⟨k, h⟩
        fin_cases k
        exacts [g0 h, g1 h, g2 h]
      · exfalso
        apply hηv
        rw [← mem_algebraicClosure_iff]
        have : etaRho / varpi = -A / B := by
          rw [div_eq_div_iff hv hB0]; linear_combination hABC
        rw [this]
        exact div_mem (neg_mem (hq _)) (hq _)
    · exfalso
      refine hnot (-A / C) (-B / C) (mem_algebraicClosure_iff.mp (div_mem (neg_mem (hq _)) (hq _)))
        (mem_algebraicClosure_iff.mp (div_mem (neg_mem (hq _)) (hq _))) ?_
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hC0]
      linear_combination hABC
  set e := Fintype.equivFin (Fin 3 × (Fin r × Fin 2))
  set y : Fin (Fintype.card (Fin 3 × (Fin r × Fin 2))) → TXP r := y0 ∘ e.symm with hy
  have hli' : LinearIndependent ℚ y := hli.comp _ e.symm.injective
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y)) = 3 * n := by
    rw [finrank_span_eq_card hli']; simp [n, Fintype.card_prod]
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hmem : ∀ p, y0 p ∈ Submodule.span ℚ (Set.range y) := fun p =>
    Submodule.subset_span ⟨e p, by simp [hy]⟩
  have hk : 2 * n ≤ finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXP b).per) := by
    let f : Fin 2 × (Fin r × Fin 2) → ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXP b).per) := fun p =>
      ⟨y0 (Fin.castSucc p.1, p.2), hmem _, by
        obtain ⟨k, h⟩ := p
        fin_cases k
        · exact add_mem (liftPI_mem_per _ _) (liftPR_mem_per _ _)
        · exact add_mem (liftPR_mem_per _ _) (liftPI_mem_per _ _)⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp (Submodule.span ℚ (Set.range y) ⊓ (gmXP b).per).subtype
      exact hli.comp (fun p : Fin 2 × (Fin r × Fin 2) => (Fin.castSucc p.1, p.2))
        (fun p q hpq => by
          obtain ⟨k, h⟩ := p; obtain ⟨k', h'⟩ := q
          simp only [Prod.mk.injEq] at hpq
          obtain ⟨hk, rfl⟩ := hpq
          rw [Fin.castSucc_inj] at hk; rw [hk])
    have := hf.fintype_card_le_finrank
    simpa [n, Fintype.card_prod, mul_comm] using this
  have hTX := finrank_TXP (r := r)
  have hV := finrank_ker_phiP (b := b) (β * omegaRho)
  have hWfin : finrank ℂ (Submodule.span ℂ (Set.range (wXP b))) = 2 * n := by
    rw [finrank_span_eq_card wXP_linearIndependent]; simp [n]; ring
  have hWrat : (gmXP b).Rational (Submodule.span ℂ (Set.range (wXP b))) := by
    refine ⟨Set.range (wXP b), ?_, rfl⟩
    rintro _ ⟨j | j, rfl⟩
    · refine ⟨fun k => ?_, fun _ => isAlgebraic_zero, (hθalg j).neg, isAlgebraic_zero⟩
      simp only [wXP, Pi.single_apply]
      exact isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero
    · refine ⟨fun _ => isAlgebraic_zero, fun k => ?_, isAlgebraic_zero, (hθalg j).neg⟩
      simp only [wXP, Pi.single_apply]
      exact isAlgebraic_ite _ isAlgebraic_one isAlgebraic_zero
  have hk_le : finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXP b).per) ≤ 3 * n := by
    have := Submodule.finrank_mono
      (show Submodule.span ℚ (Set.range y) ⊓ (gmXP b).per ≤ Submodule.span ℚ (Set.range y) from
        inf_le_left)
    omega
  have hVmem : ∀ p, y0 p ∈ LinearMap.ker (phiP b (β * omegaRho)) := by
    rintro ⟨k, h⟩
    rw [LinearMap.mem_ker, phiP_apply]
    have hp : (varpi : ℂ) * (Real.pi / varpi) = Real.pi := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hv]
    fin_cases k
    · show β * omegaRho * psiP1 b (P1' b β h) - varpi * psiP2 b (P1' b β h) = 0
      rw [(psi_P1' hb hIK hr3K hβK h).1, (psi_P1' hb hIK hr3K hβK h).2]; ring
    · show β * omegaRho * psiP1 b (P2' b β h) - varpi * psiP2 b (P2' b β h) = 0
      rw [(psi_P2' hb hIK hr3K hβK h).1, (psi_P2' hb hIK hr3K hβK h).2]
      linear_combination (theta I b h * β) * etaRho_mul - (theta I b h * β * (2 * r3 / 3)) * hp
    · show β * omegaRho * psiP1 b (DP b zX wX zY wY a c h) - varpi * psiP2 b (DP b zX wX zY wY a c h) = 0
      rw [(psi_DP zX wX zY wY a c h).1, (psi_DP zX wX zY wY a c h).2]
      linear_combination theta I b h * hrel
  obtain ⟨S, hsub, hne, hle⟩ := hW hg₂ hg₃ hg₂' hg₃' r b hb
    (LinearMap.ker (phiP b (β * omegaRho))) (Submodule.span ℂ (Set.range (wXP b))) _ y
    (by omega) (wXP_le_V _) hWrat
    (fun i => ⟨hVmem _, genP_mem_lam β zX wX zY wY a c hX hY ha hc _⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
        ((0 : ℤ) + 2 * ((2 * n + 2 : ℕ) : ℤ) -
          finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ (gmXP b).per)) *
          ((finrank ℂ (TXP r) : ℤ) - 1 - finrank ℂ (Submodule.span ℂ (Set.range (wXP b)))))
      rw [hfinY, hWfin, hTX]; push_cast; omega)
  rcases hsub with rfl | ⟨x, hxS, ⟨hx1, hx2, hx3, hx4⟩, hx⟩
  · exact hne rfl
  · have hxV := hle hxS
    rw [LinearMap.mem_ker, phiP_apply] at hxV
    have hdot : ∀ z : Fin r × Fin 2 → ℂ, (∀ j, IsAlgebraic ℚ (z j)) →
        dotL (theta I b) z ∈ algebraicClosure ℚ ℂ := fun z hz => by
      rw [dotL_apply]
      exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hθalg j))
        (mem_algebraicClosure_iff.mpr (hz j))
    have hp1 : psiP1 b x ∈ algebraicClosure ℚ ℂ := by
      rw [psiP1_apply]; exact add_mem (hdot _ hx1) (mem_algebraicClosure_iff.mpr hx3)
    have hp2 : psiP2 b x ∈ algebraicClosure ℚ ℂ := by
      rw [psiP2_apply]; exact add_mem (hdot _ hx2) (mem_algebraicClosure_iff.mpr hx4)
    have hc0 : β * omegaRho ≠ 0 := mul_ne_zero hβ0 omegaRho_ne_zero
    have hpsi2 : psiP2 b x ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at hxV
      have h1 : psiP1 b x = 0 := (mul_eq_zero.mp hxV).resolve_left hc0
      rcases hx with h | h
      · exact h h1
      · exact h h0
    have hp1ne : psiP1 b x ≠ 0 := by
      intro h0; rw [h0, mul_zero, zero_sub, neg_eq_zero] at hxV
      exact hpsi2 ((mul_eq_zero.mp hxV).resolve_left hv)
    apply hM
    have hOv : (omegaRho : ℂ) / varpi = psiP2 b x / (β * psiP1 b x) := by
      rw [div_eq_div_iff hv (mul_ne_zero hβ0 hp1ne)]; linear_combination hxV
    rw [hOv, ← mem_algebraicClosure_iff]
    exact div_mem hp2 (mul_mem (mem_algebraicClosure_iff.mpr hβ) hp1)

end Main

end CM4E.Gen
