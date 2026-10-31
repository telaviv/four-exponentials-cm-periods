/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs
import CM4E.Waldschmidt
import CM4E.Lattice
import CM4E.Common
import CM4E.Ext.Weierstrass.ZetaDef

/-!
# Theorem MX, conditional, `K`-form: two CM curves, no `G_m`

Let `E_i : y² = 4x³ − 4x` (lattice `ϖℤ[i]`) and `E_ρ : y² = 4x³ − 4` (lattice `Ω_ρℤ[ρ]`). Write `Λ(E^♮)` for the
logarithms of algebraic points of the universal vector extension, in coordinates `(z, w)` with
`exp(z, w) = (℘(z), ℘'(z), w − ζ(z))` (`LogNat`). Theorem MX of the paper (§MX) says: if `X ∈ Λ(E_i^♮)`,
`Y ∈ Λ(E_ρ^♮)`, `a, t ∈ ℚ̄`, `β ∈ ℚ̄ˣ` and

  `(z(X) + z(Y) + a) · β η(Ω_ρ) = (w(X) + w(Y) + t) · ϖ`,

then `z(X) + z(Y) + a ∈ Kϖ + KΩ_ρ` (Proposition D), and then `a = 0` etc. by Bertrand–Masser/Wüstholz.

This file proves the `K`-form (`CM4E.MX.main`) for `K = ℚ(i, √3)` (`n = 4`) and `β ∈ Kˣ`. It uses the paper's second
derivation (Remark "The count"): W88 §5d, (5.4), for `G'' = G_a × G_ℓ`, with `m = 3n = 12 > (2(2n+1) − κ)·1`, `κ ≥ 2n`.

## The group model `gmX`

`G'' = (E_i^♮ × E_ρ^♮ × G_a²)⁴ / U`, `U = {z_i = z_ρ = 0, θᵀa₁ = 0, θᵀ(w_i + w_ρ + a₂) = 0}`, `θ = (1, i, √3, i√3)`.
So `G'' = G_a × G_ℓ`, where `G_ℓ` is the push-out of the universal vector extension of `A = E_i⁴ × E_ρ⁴` along
`(w_i, w_ρ) ↦ θᵀw_i + θᵀw_ρ`. Tangent coordinates `(s₁, z_i, z_ρ, s₂) ∈ ℂ × ℂ⁴ × ℂ⁴ × ℂ`, with
`s₁ = θᵀa₁`, `s₂ = θᵀ(w_i + w_ρ + a₂)`, and `Ψ''(s₁, z_i, z_ρ, s₂) = (θᵀz_i + θᵀz_ρ + s₁, s₂)`.

Soundness facts used to justify the model (not checked by Lean):
1. `LogNat` describes `Λ(E^♮)` in the coordinates above (the cocycle `ζ(u+v) − ζ(u) − ζ(v)` is a rational function
   over `ℚ̄` of the points), and the quasi-periods are `η((m + ni)ϖ) = (m − ni)π/ϖ`,
   `η((m + nρ)Ω_ρ) = (m + nρ̄)·2π/(√3 Ω_ρ)` (Legendre, `ζ(iz) = −iζ(z)`, `ζ(ρz) = ρ̄ζ(z)`).
2. `lam` is the `ℚ`-span of images of elements of `Λ(G⁴)` (one copy at a time). `Λ(G'')` is a `ℚ`-vector space
   (division points of algebraic points are algebraic), and the quotient map sends `Λ(G⁴)` into `Λ(G'')`.
3. `per` is the `ℚ`-span of the images of the periods of `G⁴` (`U` is a vector group, so these are all periods).
4. Every nonzero connected algebraic subgroup `H` of `G''` has `T_H ⊄ ker Ψ''`. Proof: if `H` meets the kernel
   `G_a × G_a` of `G'' → A` nontrivially, `T_H` contains `(c, 0, 0, d) ≠ 0`, with `Ψ''`-image `(c, d)`. Otherwise `H`
   is a splitting over an abelian subvariety `B = B_i × B_ρ ≠ 0`, `T_{B_i} = ℂ S_i` for a `ℚ(i)`-subspace
   `S_i ⊂ ℚ(i)⁴` (likewise `B_ρ`). Its `G_a`-component is trivial (`Hom(B, G_a) = 0`), so `H ⊂ 0 × G_ℓ`. A splitting
   forces `φ(S) = 0`: otherwise the image in `G_ℓ` of the anti-affine group `B^♮` contains the fibre, and `H`, which
   would have to contain that image, meets the kernel. And `ker ψ ∩ ker φ = 0` (Lemma K) gives
   `ψ = θᵀ ≠ 0` on `T_B`, so `Ψ''₁ ≠ 0` on `T_H`. Since `T_H` is spanned by algebraic vectors, one of them has nonzero
   `Ψ''`-image: this is `sub`.
5. `d₀ = 1` and `d₁ = 0` are maximal (`G_ℓ` is a quotient of an anti-affine group), `d₂ = 9`.
6. `g₂, g₃` of both lattices are algebraic (premise of the hypothesis).

W88 (1.2)/(5.4) does not involve `d₀`, so the shared form `HyperplaneKappa` applies unchanged.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.MX

/-! ## The equianharmonic lattice `Ω_ρ ℤ[ρ]` -/

lemma omegaRho_pos : 0 < omegaRho := by
  unfold omegaRho
  have h1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < 2 ^ ((4 : ℝ) / 3) := by positivity
  have h3 := Real.pi_pos
  positivity

lemma omegaRho_ne_zero : (omegaRho : ℂ) ≠ 0 := by exact_mod_cast omegaRho_pos.ne'

/-- `√3` as a complex number. -/
noncomputable def r3 : ℂ := (Real.sqrt 3 : ℂ)

lemma r3_sq : r3 ^ 2 = 3 := by
  simp [r3, ← Complex.ofReal_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma r3_ne_zero : r3 ≠ 0 := by
  intro h; have := r3_sq; rw [h] at this; norm_num at this

/-- `ρ = (−1 + i√3)/2`. -/
noncomputable def rho : ℂ := (-1 + I * r3) / 2
/-- `ρ̄ = (−1 − i√3)/2`. -/
noncomputable def rhoBar : ℂ := (-1 - I * r3) / 2

lemma linearIndependent_rho : LinearIndependent ℝ ![(omegaRho : ℂ), rho * omegaRho] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hO := omegaRho_pos
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have e1 : (s • (omegaRho : ℂ) + t • (rho * omegaRho)).im = t * (Real.sqrt 3 / 2 * omegaRho) := by
    simp [rho, r3]
  have e2 : (s • (omegaRho : ℂ) + t • (rho * omegaRho)).re = s * omegaRho - t * (omegaRho / 2) := by
    simp [rho, r3]; ring
  rw [e1] at him; rw [e2] at hre
  simp only [Complex.zero_im, Complex.zero_re] at him hre
  have ht : t = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exfalso; have : 0 < Real.sqrt 3 / 2 * omegaRho := by positivity
      linarith
  subst ht
  refine ⟨?_, rfl⟩
  rcases mul_eq_zero.mp (by linarith : s * omegaRho = 0) with h1 | h1
  · exact h1
  · linarith

/-- The period pair `(Ω_ρ, ρΩ_ρ)` of `y² = 4x³ − 4`. -/
noncomputable def equianharmonic : PeriodPair where
  ω₁ := omegaRho
  ω₂ := rho * omegaRho
  indep := linearIndependent_rho

/-! ## Quasi-periods and `Λ(E^♮)` -/

/-- `η(Ω_ρ) = 2π/(√3 Ω_ρ)`. -/
noncomputable def etaRho : ℂ := 2 * Real.pi / (r3 * omegaRho)

/-- `η((m + nρ)Ω_ρ) = (m + nρ̄) η(Ω_ρ)`. -/
noncomputable def etaR (m n : ℤ) : ℂ := ((m : ℂ) + n * rhoBar) * etaRho

/-- `(z, w) ∈ Λ(E^♮)`, for the coordinates with `exp(z, w) = (℘(z), ℘'(z), w − ζ(z))`: either `z = mω₁ + nω₂` is a
period and `w − η(z) ∈ ℚ̄`, or `exp_E(z)` is an algebraic affine point and `w − ζ(z) ∈ ℚ̄`. Here `ζ` is
`CM4E.Ext.Weierstrass.zeta`, the standard series, with `ζ' = −℘` proved there (`hasDerivAt_zeta`). -/
def LogNat (L : PeriodPair) (eta : ℤ → ℤ → ℂ) (z w : ℂ) : Prop :=
  (∃ m n : ℤ, z = m * L.ω₁ + n * L.ω₂ ∧ IsAlgebraic ℚ (w - eta m n)) ∨
    (z ∉ L.lattice ∧ IsAlgebraic ℚ (L.weierstrassP z) ∧ IsAlgebraic ℚ (L.derivWeierstrassP z) ∧
      IsAlgebraic ℚ (w - CM4E.Ext.Weierstrass.zeta L z))

/-! ## The group model -/

/-- The tangent space `ℂ × ℂ⁴ × ℂ⁴ × ℂ` of `G'' = G_a × G_ℓ`, coordinates `(s₁, z_i, z_ρ, s₂)`. -/
abbrev TX := ℂ × (Fin 4 → ℂ) × (Fin 4 → ℂ) × ℂ

/-- The basis `θ = (1, i, √3, i√3)` of `K = ℚ(i, √3)`. -/
noncomputable def θ : Fin 4 → ℂ := ![1, I, r3, I * r3]

/-- `Ψ''₁ = s₁ + θᵀz_i + θᵀz_ρ`. -/
noncomputable def psi1 : TX →ₗ[ℂ] ℂ where
  toFun v := v.1 + (v.2.1 0 + I * v.2.1 1 + r3 * v.2.1 2 + I * r3 * v.2.1 3) +
    (v.2.2.1 0 + I * v.2.2.1 1 + r3 * v.2.2.1 2 + I * r3 * v.2.2.1 3)
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- `Ψ''₂ = s₂`. -/
noncomputable def psi2 : TX →ₗ[ℂ] ℂ where
  toFun v := v.2.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma psi1_apply (v : TX) : psi1 v = v.1 + (v.2.1 0 + I * v.2.1 1 + r3 * v.2.1 2 + I * r3 * v.2.1 3) +
    (v.2.2.1 0 + I * v.2.2.1 1 + r3 * v.2.2.1 2 + I * r3 * v.2.2.1 3) := rfl

lemma psi2_apply (v : TX) : psi2 v = v.2.2.2 := rfl

/-- The image of `(z, w) ∈ T(E_i^♮)` placed in copy `h`. -/
noncomputable def genI (h : Fin 4) (z w : ℂ) : TX := (0, Pi.single h z, 0, θ h * w)
/-- The image of `(z, w) ∈ T(E_ρ^♮)` placed in copy `h`. -/
noncomputable def genR (h : Fin 4) (z w : ℂ) : TX := (0, 0, Pi.single h z, θ h * w)
/-- The image of `(a₁, a₂) ∈ T(G_a²)` placed in copy `h`. -/
noncomputable def genA (h : Fin 4) (a t : ℂ) : TX := (θ h * a, 0, 0, θ h * t)

/-- Generators of `lam`: images of logarithms of algebraic points of one factor of one copy. -/
def lamGen : Set TX :=
  {v | ∃ h z w, LogNat lemniscatic etaLem z w ∧ v = genI h z w} ∪
    {v | ∃ h z w, LogNat equianharmonic etaR z w ∧ v = genR h z w} ∪
    {v | ∃ h a t, IsAlgebraic ℚ a ∧ IsAlgebraic ℚ t ∧ v = genA h a t}

/-- Period generators: `(ϖ, π/ϖ)`, `(iϖ, −iπ/ϖ)` on `E_i^♮`. -/
noncomputable def G1 (j : Fin 4) : TX := genI j varpi (Real.pi / varpi)
noncomputable def G2 (j : Fin 4) : TX := genI j (I * varpi) (-I * (Real.pi / varpi))
/-- Period generators: `(Ω_ρ, η_ρ)`, `(i√3 Ω_ρ, −i√3 η_ρ)` on `E_ρ^♮` (`i√3 = 1 + 2ρ`). -/
noncomputable def H1 (j : Fin 4) : TX := genR j omegaRho etaRho
noncomputable def H2 (j : Fin 4) : TX := genR j (I * r3 * omegaRho) (-(I * r3) * etaRho)

/-- The `ℚ`-span of the periods of `G''`. -/
noncomputable def perX : Submodule ℚ TX :=
  Submodule.span ℚ (Set.range G1 ∪ Set.range G2 ∪ Set.range H1 ∪ Set.range H2)

/-- Algebraic coordinates. -/
def algX (v : TX) : Prop :=
  IsAlgebraic ℚ v.1 ∧ (∀ j, IsAlgebraic ℚ (v.2.1 j)) ∧ (∀ j, IsAlgebraic ℚ (v.2.2.1 j)) ∧
    IsAlgebraic ℚ v.2.2.2

/-- The model of `G'' = G_a × G_ℓ`. -/
noncomputable def gmX : GroupModel TX where
  d₁ := 0
  d₂ := 9
  alg := algX
  lam := (Submodule.span ℚ lamGen : Set TX)
  per := perX
  sub := fun S => S = ⊥ ∨ ∃ x ∈ S, algX x ∧ (psi1 x ≠ 0 ∨ psi2 x ≠ 0)

/-- **The hypothesis for Theorem MX**: W88 §5d for `G_a × G_ℓ` (same form as `Thm11Kappa`). -/
def Thm11KappaMX : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ →
    IsAlgebraic ℚ equianharmonic.g₂ → IsAlgebraic ℚ equianharmonic.g₃ → HyperplaneKappa gmX

/-! ## `Ψ''` on the generators -/

lemma psi1_genI (h : Fin 4) (z w : ℂ) : psi1 (genI h z w) = θ h * z := by
  fin_cases h <;> simp [psi1_apply, genI, θ]
lemma psi2_genI (h : Fin 4) (z w : ℂ) : psi2 (genI h z w) = θ h * w := rfl
lemma psi1_genR (h : Fin 4) (z w : ℂ) : psi1 (genR h z w) = θ h * z := by
  fin_cases h <;> simp [psi1_apply, genR, θ]
lemma psi2_genR (h : Fin 4) (z w : ℂ) : psi2 (genR h z w) = θ h * w := rfl
lemma psi1_genA (h : Fin 4) (a t : ℂ) : psi1 (genA h a t) = θ h * a := by
  simp [psi1_apply, genA]
lemma psi2_genA (h : Fin 4) (a t : ℂ) : psi2 (genA h a t) = θ h * t := rfl

lemma psi_rsmul (f : TX →ₗ[ℂ] ℂ) (q : ℚ) (v : TX) : f (q • v) = (q : ℂ) * f v := by
  rw [map_rat_smul f q v, Rat.smul_def]

/-! ## Explicit period lifts (`E_i`: base `θ_k ϖ` / fibre `θ_k π/ϖ`; `E_ρ`: base `θ_k Ω_ρ` / fibre `θ_k η_ρ`) -/

/-- `Ψ''`-image `(θ_k ϖ, 0)`. -/
noncomputable def Ib : Fin 4 → TX :=
  ![(1/2 : ℚ) • G1 0 + (-1/2 : ℚ) • G2 1, (1/2 : ℚ) • G1 1 + (1/2 : ℚ) • G2 0,
    (1/2 : ℚ) • G1 2 + (-1/2 : ℚ) • G2 3, (1/2 : ℚ) • G1 3 + (1/2 : ℚ) • G2 2]
/-- `Ψ''`-image `(0, θ_k π/ϖ)`. -/
noncomputable def If : Fin 4 → TX :=
  ![(1/2 : ℚ) • G1 0 + (1/2 : ℚ) • G2 1, (1/2 : ℚ) • G1 1 + (-1/2 : ℚ) • G2 0,
    (1/2 : ℚ) • G1 2 + (1/2 : ℚ) • G2 3, (1/2 : ℚ) • G1 3 + (-1/2 : ℚ) • G2 2]
/-- `Ψ''`-image `(θ_k Ω_ρ, 0)`. -/
noncomputable def Rb : Fin 4 → TX :=
  ![(1/2 : ℚ) • H1 0 + (-1/6 : ℚ) • H2 3, (1/2 : ℚ) • H1 1 + (1/6 : ℚ) • H2 2,
    (-1/2 : ℚ) • H2 1 + (1/2 : ℚ) • H1 2, (1/2 : ℚ) • H2 0 + (1/2 : ℚ) • H1 3]
/-- `Ψ''`-image `(0, θ_k η_ρ)`. -/
noncomputable def Rf : Fin 4 → TX :=
  ![(1/2 : ℚ) • H1 0 + (1/6 : ℚ) • H2 3, (1/2 : ℚ) • H1 1 + (-1/6 : ℚ) • H2 2,
    (1/2 : ℚ) • H2 1 + (1/2 : ℚ) • H1 2, (-1/2 : ℚ) • H2 0 + (1/2 : ℚ) • H1 3]

lemma psi_Ib (k : Fin 4) : psi1 (Ib k) = θ k * varpi ∧ psi2 (Ib k) = 0 := by
  fin_cases k <;> refine ⟨?_, ?_⟩ <;>
    simp [Ib, G1, G2, psi1_genI, psi2_genI, θ, Rat.smul_def] <;>
    ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
lemma psi_If (k : Fin 4) : psi1 (If k) = 0 ∧ psi2 (If k) = θ k * (Real.pi / varpi) := by
  fin_cases k <;> refine ⟨?_, ?_⟩ <;>
    simp [If, G1, G2, psi1_genI, psi2_genI, θ, Rat.smul_def] <;>
    ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
lemma psi_Rb (k : Fin 4) : psi1 (Rb k) = θ k * omegaRho ∧ psi2 (Rb k) = 0 := by
  fin_cases k <;> refine ⟨?_, ?_⟩ <;>
    simp [Rb, H1, H2, psi1_genR, psi2_genR, θ, Rat.smul_def] <;>
    ring_nf <;> (try simp only [Complex.I_sq, r3_sq]) <;> ring_nf
lemma psi_Rf (k : Fin 4) : psi1 (Rf k) = 0 ∧ psi2 (Rf k) = θ k * etaRho := by
  fin_cases k <;> refine ⟨?_, ?_⟩ <;>
    simp [Rf, H1, H2, psi1_genR, psi2_genR, θ, Rat.smul_def] <;>
    ring_nf <;> (try simp only [Complex.I_sq, r3_sq]) <;> ring_nf

/-! ## `β ∈ K`, and the lifts of `θ_h w₁`, `θ_h w₂`, `θ_h v` -/

/-- The field `K = ℚ(i, √3)`. -/
noncomputable def K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({I, r3} : Set ℂ)

/-- `β = b₀ + b₁ i + b₂ √3 + b₃ i√3 ∈ K`. -/
noncomputable def beta (b : Fin 4 → ℚ) : ℂ := (b 0 : ℂ) + I * b 1 + r3 * b 2 + I * r3 * b 3

/-- Coefficients of `θ_h · β`. -/
def mulC (b : Fin 4 → ℚ) : Fin 4 → Fin 4 → ℚ :=
  ![b, ![-b 1, b 0, -b 3, b 2], ![3 * b 2, 3 * b 3, b 0, b 1], ![-3 * b 3, 3 * b 2, -b 1, b 0]]

/-- Coefficients of `β · 2√3/3 = β · 2/√3`. -/
def gam (b : Fin 4 → ℚ) : Fin 4 → ℚ := ![2 * b 2, 2 * b 3, 2 * b 0 / 3, 2 * b 1 / 3]

lemma beta_mulC (b : Fin 4 → ℚ) (h : Fin 4) : beta (mulC b h) = θ h * beta b := by
  fin_cases h <;> simp [beta, mulC, θ] <;> ring_nf <;> (try simp only [Complex.I_sq, r3_sq]) <;> ring_nf

lemma beta_gam (b : Fin 4 → ℚ) : beta (gam b) = beta b * (2 * r3 / 3) := by
  simp [beta, gam]; ring_nf; simp only [r3_sq]; ring_nf

/-- Fibre lift on `E_i` with `K`-coefficient `beta x`. -/
noncomputable def IfC (x : Fin 4 → ℚ) : TX := ∑ k, x k • If k
/-- Fibre lift on `E_ρ` with `K`-coefficient `beta x`. -/
noncomputable def RfC (x : Fin 4 → ℚ) : TX := ∑ k, x k • Rf k

lemma psi_IfC (x : Fin 4 → ℚ) :
    psi1 (IfC x) = 0 ∧ psi2 (IfC x) = beta x * (Real.pi / varpi) := by
  have e1 : ∀ k, psi1 (If k) = 0 := fun k => (psi_If k).1
  have e2 : ∀ k, psi2 (If k) = θ k * (Real.pi / varpi) := fun k => (psi_If k).2
  refine ⟨?_, ?_⟩ <;> simp only [IfC, map_sum, psi_rsmul, e1, e2]
  · simp
  · simp [Fin.sum_univ_four, beta, θ]; ring

lemma psi_RfC (x : Fin 4 → ℚ) : psi1 (RfC x) = 0 ∧ psi2 (RfC x) = beta x * etaRho := by
  have e1 : ∀ k, psi1 (Rf k) = 0 := fun k => (psi_Rf k).1
  have e2 : ∀ k, psi2 (Rf k) = θ k * etaRho := fun k => (psi_Rf k).2
  refine ⟨?_, ?_⟩ <;> simp only [RfC, map_sum, psi_rsmul, e1, e2]
  · simp
  · simp [Fin.sum_univ_four, beta, θ]; ring

/-- A lift in `per` of `θ_h w₁ = θ_h (ϖ, β η_ρ)`. -/
noncomputable def preW1 (b : Fin 4 → ℚ) (h : Fin 4) : TX := Ib h + RfC (mulC b h)
/-- A lift in `per` of `θ_h w₂ = θ_h (Ω_ρ, β (2/√3) π/ϖ)`. -/
noncomputable def preW2 (b : Fin 4 → ℚ) (h : Fin 4) : TX := Rb h + IfC (mulC (gam b) h)

lemma psi_preW1 (b : Fin 4 → ℚ) (h : Fin 4) :
    psi1 (preW1 b h) = θ h * varpi ∧ psi2 (preW1 b h) = θ h * beta b * etaRho := by
  obtain ⟨h1, h2⟩ := psi_Ib h
  obtain ⟨h3, h4⟩ := psi_RfC (mulC b h)
  simp only [preW1, map_add, h1, h2, h3, h4, beta_mulC]
  constructor <;> ring

lemma psi_preW2 (b : Fin 4 → ℚ) (h : Fin 4) :
    psi1 (preW2 b h) = θ h * omegaRho ∧
      psi2 (preW2 b h) = θ h * beta b * (2 * r3 / 3) * (Real.pi / varpi) := by
  obtain ⟨h1, h2⟩ := psi_Rb h
  obtain ⟨h3, h4⟩ := psi_IfC (mulC (gam b) h)
  simp only [preW2, map_add, h1, h2, h3, h4, beta_mulC, beta_gam]
  constructor <;> ring

/-- The lift of `θ_h v`, `v = Ψ(X, Y, a, t)`. -/
noncomputable def dataV (zX wX zY wY a t : ℂ) (h : Fin 4) : TX :=
  genI h zX wX + genR h zY wY + genA h a t

lemma psi_dataV (zX wX zY wY a t : ℂ) (h : Fin 4) :
    psi1 (dataV zX wX zY wY a t h) = θ h * (zX + zY + a) ∧
      psi2 (dataV zX wX zY wY a t h) = θ h * (wX + wY + t) := by
  simp only [dataV, map_add, psi1_genI, psi1_genR, psi1_genA, psi2_genI, psi2_genR, psi2_genA]
  constructor <;> ring

/-- The twelve generators of `Y''`. -/
noncomputable def yX (b : Fin 4 → ℚ) (zX wX zY wY a t : ℂ) : Fin 12 → TX :=
  ![preW1 b 0, preW1 b 1, preW1 b 2, preW1 b 3, preW2 b 0, preW2 b 1, preW2 b 2, preW2 b 3,
    dataV zX wX zY wY a t 0, dataV zX wX zY wY a t 1, dataV zX wX zY wY a t 2, dataV zX wX zY wY a t 3]

/-! ## Membership in `per` and `lam` -/

lemma G1_mem (j : Fin 4) : G1 j ∈ perX := Submodule.subset_span (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩)))
lemma G2_mem (j : Fin 4) : G2 j ∈ perX := Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))
lemma H1_mem (j : Fin 4) : H1 j ∈ perX := Submodule.subset_span (Or.inl (Or.inr ⟨j, rfl⟩))
lemma H2_mem (j : Fin 4) : H2 j ∈ perX := Submodule.subset_span (Or.inr ⟨j, rfl⟩)

lemma Ib_mem (k : Fin 4) : Ib k ∈ perX := by
  fin_cases k <;> exact add_mem (Submodule.smul_mem _ _ (G1_mem _)) (Submodule.smul_mem _ _ (G2_mem _))
lemma If_mem (k : Fin 4) : If k ∈ perX := by
  fin_cases k <;> exact add_mem (Submodule.smul_mem _ _ (G1_mem _)) (Submodule.smul_mem _ _ (G2_mem _))
lemma Rb_mem (k : Fin 4) : Rb k ∈ perX := by
  fin_cases k <;> first
    | exact add_mem (Submodule.smul_mem _ _ (H1_mem _)) (Submodule.smul_mem _ _ (H2_mem _))
    | exact add_mem (Submodule.smul_mem _ _ (H2_mem _)) (Submodule.smul_mem _ _ (H1_mem _))
lemma Rf_mem (k : Fin 4) : Rf k ∈ perX := by
  fin_cases k <;> first
    | exact add_mem (Submodule.smul_mem _ _ (H1_mem _)) (Submodule.smul_mem _ _ (H2_mem _))
    | exact add_mem (Submodule.smul_mem _ _ (H2_mem _)) (Submodule.smul_mem _ _ (H1_mem _))

lemma preW1_mem (b : Fin 4 → ℚ) (h : Fin 4) : preW1 b h ∈ perX :=
  add_mem (Ib_mem h) (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Rf_mem k))
lemma preW2_mem (b : Fin 4 → ℚ) (h : Fin 4) : preW2 b h ∈ perX :=
  add_mem (Rb_mem h) (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (If_mem k))

lemma isAlg_zero_of {x : ℂ} (h : x = 0) : IsAlgebraic ℚ x := h ▸ isAlgebraic_zero

lemma log_G1 : LogNat lemniscatic etaLem varpi (Real.pi / varpi) :=
  Or.inl ⟨1, 0, by simp [lemniscatic], isAlg_zero_of (by simp [etaLem])⟩
lemma log_G2 : LogNat lemniscatic etaLem (I * varpi) (-I * (Real.pi / varpi)) :=
  Or.inl ⟨0, 1, by simp [lemniscatic], isAlg_zero_of (by simp [etaLem])⟩
lemma log_H1 : LogNat equianharmonic etaR omegaRho etaRho :=
  Or.inl ⟨1, 0, by simp [equianharmonic], isAlg_zero_of (by simp [etaR])⟩
lemma log_H2 : LogNat equianharmonic etaR (I * r3 * omegaRho) (-(I * r3) * etaRho) :=
  Or.inl ⟨1, 2, by simp [equianharmonic, rho]; ring, isAlg_zero_of (by simp [etaR, rhoBar]; ring)⟩

lemma perX_le_lam : perX ≤ Submodule.span ℚ lamGen := by
  rw [perX, Submodule.span_le]
  rintro _ (((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨j, _, _, log_G1, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨j, _, _, log_G2, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨j, _, _, log_H1, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨j, _, _, log_H2, rfl⟩))

lemma yX_lam (b : Fin 4 → ℚ) (zX wX zY wY a t : ℂ) (hX : LogNat lemniscatic etaLem zX wX)
    (hY : LogNat equianharmonic etaR zY wY) (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (i : Fin 12) : yX b zX wX zY wY a t i ∈ gmX.lam := by
  show yX b zX wX zY wY a t i ∈ Submodule.span ℚ lamGen
  have hd : ∀ h, dataV zX wX zY wY a t h ∈ Submodule.span ℚ lamGen := fun h =>
    add_mem (add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨h, zX, wX, hX, rfl⟩)))
      (Submodule.subset_span (Or.inl (Or.inr ⟨h, zY, wY, hY, rfl⟩))))
      (Submodule.subset_span (Or.inr ⟨h, a, t, ha, ht, rfl⟩))
  have p1 := fun h => perX_le_lam (preW1_mem b h)
  have p2 := fun h => perX_le_lam (preW2_mem b h)
  fin_cases i
  exacts [p1 0, p1 1, p1 2, p1 3, p2 0, p2 1, p2 2, p2 3, hd 0, hd 1, hd 2, hd 3]

/-! ## `V''` and `W''` -/

/-- `c Ψ''₁ − ϖ Ψ''₂`; with `c = β η_ρ` its kernel is `V'' = Ψ''⁻¹(ℂ(ϖ, β η_ρ))`. -/
noncomputable def phiX (c : ℂ) : TX →ₗ[ℂ] ℂ := c • psi1 - (varpi : ℂ) • psi2

lemma phiX_apply (c : ℂ) (v : TX) : phiX c v = c * psi1 v - varpi * psi2 v := rfl

lemma finrank_TX : finrank ℂ TX = 10 := by simp [TX, Module.finrank_prod]

lemma finrank_ker_phiX (c : ℂ) : finrank ℂ (LinearMap.ker (phiX c)) = 9 := by
  have hsurj : Function.Surjective (phiX c) := fun w =>
    ⟨(0, 0, 0, -w / varpi), by have hv := varpi_ne_zero'; simp [phiX_apply, psi1_apply, psi2_apply]; field_simp⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiX c)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, finrank_TX] at h1
  omega

/-- `(−θ_j, e_j, 0, 0) ∈ ker Ψ''`. -/
noncomputable def wI (j : Fin 4) : TX := (-θ j, Pi.single j 1, 0, 0)
/-- `(−θ_j, 0, e_j, 0) ∈ ker Ψ''`. -/
noncomputable def wR (j : Fin 4) : TX := (-θ j, 0, Pi.single j 1, 0)

/-- Eight algebraic vectors spanning `W'' = ker Ψ''`. -/
noncomputable def wB : Fin 8 → TX := ![wI 0, wI 1, wI 2, wI 3, wR 0, wR 1, wR 2, wR 3]

lemma wB_linearIndependent : LinearIndependent ℂ wB := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ k : Fin 4, g ⟨k, by omega⟩ = 0 ∧ g ⟨k + 4, by omega⟩ = 0 := by
    intro k
    have e1 := congrArg (fun v : TX => v.2.1 k) hg
    have e2 := congrArg (fun v : TX => v.2.2.1 k) hg
    fin_cases k <;> simp [Fin.sum_univ_succ, wB, wI, wR] at e1 e2 <;>
      exact ⟨e1, e2⟩
  intro i
  fin_cases i
  exacts [(e 0).1, (e 1).1, (e 2).1, (e 3).1, (e 0).2, (e 1).2, (e 2).2, (e 3).2]

lemma finrank_WX : finrank ℂ (Submodule.span ℂ (Set.range wB)) = 8 := by
  rw [finrank_span_eq_card wB_linearIndependent]; simp

lemma WX_le_V (c : ℂ) : Submodule.span ℂ (Set.range wB) ≤ LinearMap.ker (phiX c) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [wB, wI, wR, phiX_apply, psi1_apply, psi2_apply, θ]

lemma isAlgebraic_r3 : IsAlgebraic ℚ r3 := by simpa [r3] using isAlgebraic_sqrt_nat 3

lemma isAlg_theta (j : Fin 4) : IsAlgebraic ℚ (θ j) := by
  have hI := isAlgebraic_I
  fin_cases j <;> simp [θ]
  exacts [isAlgebraic_one, hI, isAlgebraic_r3, hI.mul isAlgebraic_r3]

lemma isAlg_single (j k : Fin 4) : IsAlgebraic ℚ ((Pi.single j (1 : ℂ) : Fin 4 → ℂ) k) := by
  rw [Pi.single_apply]; split_ifs
  exacts [isAlgebraic_one, isAlgebraic_zero]

lemma WX_rational : gmX.Rational (Submodule.span ℂ (Set.range wB)) := by
  refine ⟨Set.range wB, ?_, rfl⟩
  have hI : ∀ j, algX (wI j) := fun j =>
    ⟨(isAlg_theta j).neg, isAlg_single j, fun _ => isAlgebraic_zero, isAlgebraic_zero⟩
  have hR : ∀ j, algX (wR j) := fun j =>
    ⟨(isAlg_theta j).neg, fun _ => isAlgebraic_zero, isAlg_single j, isAlgebraic_zero⟩
  rintro _ ⟨i, rfl⟩
  fin_cases i
  exacts [hI 0, hI 1, hI 2, hI 3, hR 0, hR 1, hR 2, hR 3]

lemma etaRho_mul : etaRho * omegaRho = 2 * r3 * Real.pi / 3 := by
  have h3 := r3_sq
  have hO := omegaRho_ne_zero
  have hr := r3_ne_zero
  rw [etaRho]
  field_simp
  linear_combination (-1 : ℂ) * h3

lemma yX_mem_V (b : Fin 4 → ℚ) (zX wX zY wY a t : ℂ)
    (hrel : (zX + zY + a) * (beta b * etaRho) = (wX + wY + t) * varpi) (i : Fin 12) :
    yX b zX wX zY wY a t i ∈ LinearMap.ker (phiX (beta b * etaRho)) := by
  rw [LinearMap.mem_ker, phiX_apply]
  have hp : (varpi : ℂ) * (Real.pi / varpi) = Real.pi := by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ varpi_ne_zero']
  have h1 : ∀ h, beta b * etaRho * psi1 (preW1 b h) - varpi * psi2 (preW1 b h) = 0 := fun h => by
    rw [(psi_preW1 b h).1, (psi_preW1 b h).2]; ring
  have h2 : ∀ h, beta b * etaRho * psi1 (preW2 b h) - varpi * psi2 (preW2 b h) = 0 := fun h => by
    rw [(psi_preW2 b h).1, (psi_preW2 b h).2]
    linear_combination (θ h * beta b) * etaRho_mul - (θ h * beta b * (2 * r3 / 3)) * hp
  have h3 : ∀ h, beta b * etaRho * psi1 (dataV zX wX zY wY a t h) -
      varpi * psi2 (dataV zX wX zY wY a t h) = 0 := fun h => by
    rw [(psi_dataV zX wX zY wY a t h).1, (psi_dataV zX wX zY wY a t h).2]
    linear_combination θ h * hrel
  fin_cases i
  exacts [h1 0, h1 1, h1 2, h1 3, h2 0, h2 1, h2 2, h2 3, h3 0, h3 1, h3 2, h3 3]

/-! ## Rank and the final contradiction -/

lemma irrational_sqrt_three : Irrational (Real.sqrt 3) := by
  simpa using Nat.prime_three.irrational_sqrt

lemma comb_K (x y u v : ℚ) : ((x : ℂ) + I * y + r3 * u + I * r3 * v) ∈ K := by
  have hI : I ∈ K := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hr : r3 ∈ K := IntermediateField.subset_adjoin ℚ _ (by simp)
  have hq : ∀ r : ℚ, (r : ℂ) ∈ K := fun r => by simp
  exact add_mem (add_mem (add_mem (hq _) (mul_mem hI (hq _))) (mul_mem hr (hq _)))
    (mul_mem (mul_mem hI hr) (hq _))

lemma yX_linearIndependent (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi)) (b : Fin 4 → ℚ)
    (zX wX zY wY a t : ℂ)
    (hnot : ∀ x ∈ K, ∀ x' ∈ K, zX + zY + a ≠ x * varpi + x' * omegaRho) :
    LinearIndependent ℚ (yX b zX wX zY wY a t) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e := congrArg psi1 hg
  rw [map_sum, map_zero] at e
  simp only [psi_rsmul] at e
  simp [Fin.sum_univ_succ, yX, (psi_preW1 b _).1, (psi_preW2 b _).1,
    (psi_dataV zX wX zY wY a t _).1, θ] at e
  set A : ℂ := (g 0 : ℂ) + I * (g 1 : ℂ) + r3 * (g 2 : ℂ) + I * r3 * (g 3 : ℂ) with hA
  set B : ℂ := (g 4 : ℂ) + I * (g 5 : ℂ) + r3 * (g 6 : ℂ) + I * r3 * (g 7 : ℂ) with hB
  set C : ℂ := (g 8 : ℂ) + I * (g 9 : ℂ) + r3 * (g 10 : ℂ) + I * r3 * (g 11 : ℂ) with hC
  have hABC : A * varpi + B * omegaRho + C * (zX + zY + a) = 0 := by
    rw [hA, hB, hC]; linear_combination e
  by_cases hC0 : C = 0
  · obtain ⟨g8, g9, g10, g11⟩ := quad_inj irrational_sqrt_three _ _ _ _ hC0
    rw [hC0, zero_mul, add_zero] at hABC
    by_cases hB0 : B = 0
    · obtain ⟨g4, g5, g6, g7⟩ := quad_inj irrational_sqrt_three _ _ _ _ hB0
      rw [hB0, zero_mul, add_zero] at hABC
      have hA0 : A = 0 := by
        rcases mul_eq_zero.mp hABC with h | h
        · exact h
        · exact absurd h varpi_ne_zero'
      obtain ⟨g0, g1, g2, g3⟩ := quad_inj irrational_sqrt_three _ _ _ _ hA0
      intro i
      fin_cases i <;> assumption
    · exfalso
      apply hM
      rw [← mem_algebraicClosure_iff]
      have : (omegaRho : ℂ) / varpi = -A / B := by
        rw [div_eq_div_iff varpi_ne_zero' hB0]; linear_combination hABC
      rw [this]
      exact div_mem (neg_mem (quad_mem_alg isAlgebraic_r3 _ _ _ _)) (quad_mem_alg isAlgebraic_r3 _ _ _ _)
  · exfalso
    refine hnot (-A / C) (div_mem (neg_mem (comb_K _ _ _ _)) (comb_K _ _ _ _))
      (-B / C) (div_mem (neg_mem (comb_K _ _ _ _)) (comb_K _ _ _ _)) ?_
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hC0]
    linear_combination hABC

lemma etaRho_ne_zero : etaRho ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [etaRho]
  exact div_ne_zero (mul_ne_zero two_ne_zero hpi) (mul_ne_zero r3_ne_zero omegaRho_ne_zero)

/-- **Conditional Theorem MX, `K`-form (Proposition D)** for `K = ℚ(i, √3)` and `β ∈ Kˣ`: if
`X = (zX, wX) ∈ Λ(E_i^♮)`, `Y = (zY, wY) ∈ Λ(E_ρ^♮)`, `a, t ∈ ℚ̄` and
`(zX + zY + a) β η(Ω_ρ) = (wX + wY + t) ϖ`, then `zX + zY + a ∈ Kϖ + KΩ_ρ`. This is Proposition D restricted to
`v ∈ Ψ(Λ(G))` (rather than `Ψ(Λ_K(G))`), which is the case Theorem MX uses.

Hypotheses: W88 §5d for `G_a × G_ℓ` (`hW`); `g₂, g₃ ∈ ℚ̄` for both lattices (`g₃(ϖℤ[i]) = 0` is proved);
`ϖΩ_ρ/π ∉ ℚ̄` (`hΓ`) and `Ω_ρ/ϖ ∉ ℚ̄` (`hM`), both consequences of Wüstholz's analytic subgroup theorem. -/
theorem main (hW : Thm11KappaMX) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₂' : IsAlgebraic ℚ equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi))
    (b : Fin 4 → ℚ) (hb : b ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : LogNat lemniscatic etaLem zX wX) (hY : LogNat equianharmonic etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (beta b * etaRho) = (wX + wY + t) * varpi) :
    ∃ x ∈ K, ∃ x' ∈ K, zX + zY + a = x * varpi + x' * omegaRho := by
  by_contra hcon
  have hnot : ∀ x ∈ K, ∀ x' ∈ K, zX + zY + a ≠ x * varpi + x' * omegaRho :=
    fun x hx x' hx' h => hcon ⟨x, hx, x', hx', h⟩
  have hliY := yX_linearIndependent hM b zX wX zY wY a t hnot
  set y := yX b zX wX zY wY a t with hy
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range y)) = 12 := by
    rw [finrank_span_eq_card hliY]; simp
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range y)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hk : 8 ≤ finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ gmX.per) := by
    have hyP : ∀ k : Fin 8, y ⟨k, by omega⟩ ∈ gmX.per := by
      intro k; fin_cases k
      exacts [preW1_mem b 0, preW1_mem b 1, preW1_mem b 2, preW1_mem b 3,
        preW2_mem b 0, preW2_mem b 1, preW2_mem b 2, preW2_mem b 3]
    let f : Fin 8 → ↥(Submodule.span ℚ (Set.range y) ⊓ gmX.per) := fun k =>
      ⟨y ⟨k, by omega⟩, Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩, hyP k⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp (Submodule.span ℚ (Set.range y) ⊓ gmX.per).subtype
      exact hliY.comp (fun k : Fin 8 => (⟨k, by omega⟩ : Fin 12))
        (fun k₁ k₂ e => by simpa [Fin.ext_iff] using e)
    simpa using hf.fintype_card_le_finrank
  obtain ⟨S, hsub, hne, hle⟩ := hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃'
    (LinearMap.ker (phiX (beta b * etaRho))) (Submodule.span ℂ (Set.range wB)) 12 y
    (by rw [finrank_ker_phiX, finrank_TX]) (WX_le_V _) WX_rational
    (fun i => ⟨yX_mem_V b zX wX zY wY a t hrel i, yX_lam b zX wX zY wY a t hX hY ha ht i⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
        ((0 : ℤ) + 2 * 9 - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ gmX.per)) *
          ((finrank ℂ TX : ℤ) - 1 - finrank ℂ (Submodule.span ℂ (Set.range wB))))
      rw [hfinY, finrank_WX, finrank_TX]; push_cast; omega)
  rcases hsub with rfl | ⟨x, hxS, ⟨hx1, hx2, hx3, hx4⟩, hx⟩
  · exact hne rfl
  · have hxV := hle hxS
    rw [LinearMap.mem_ker, phiX_apply] at hxV
    have hq : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ algebraicClosure ℚ ℂ := fun z h => mem_algebraicClosure_iff.mpr h
    have hr : r3 ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr isAlgebraic_r3
    have hI : I ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr isAlgebraic_I
    have hblk : ∀ v : Fin 4 → ℂ, (∀ j, IsAlgebraic ℚ (v j)) →
        v 0 + I * v 1 + r3 * v 2 + I * r3 * v 3 ∈ algebraicClosure ℚ ℂ := fun v hv =>
      add_mem (add_mem (add_mem (hq _ (hv 0)) (mul_mem hI (hq _ (hv 1))))
        (mul_mem hr (hq _ (hv 2)))) (mul_mem (mul_mem hI hr) (hq _ (hv 3)))
    have hp1 : psi1 x ∈ algebraicClosure ℚ ℂ := by
      rw [psi1_apply]
      exact add_mem (add_mem (hq _ hx1) (hblk _ hx2)) (hblk _ hx3)
    have hp2 : psi2 x ∈ algebraicClosure ℚ ℂ := hq _ hx4
    have hbeta : beta b ≠ 0 := by
      intro h0
      obtain ⟨b0, b1, b2, b3⟩ := quad_inj irrational_sqrt_three _ _ _ _ h0
      exact hb (by funext j; fin_cases j <;> simp [b0, b1, b2, b3])
    have hc : beta b * etaRho ≠ 0 := mul_ne_zero hbeta etaRho_ne_zero
    have hpsi2 : psi2 x ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at hxV
      have h1 : psi1 x = 0 := (mul_eq_zero.mp hxV).resolve_left hc
      rcases hx with h | h
      · exact h h1
      · exact h h0
    apply hΓ
    rw [← mem_algebraicClosure_iff]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hvar : (varpi : ℂ) = beta b * etaRho * psi1 x / psi2 x := by
      rw [eq_div_iff hpsi2]; linear_combination (-1 : ℂ) * hxV
    have hval : (varpi : ℂ) * omegaRho / Real.pi = 2 * beta b * psi1 x / (r3 * psi2 x) := by
      have hO := omegaRho_ne_zero
      have hr0 := r3_ne_zero
      have hv := varpi_ne_zero'
      rw [hvar, etaRho]
      field_simp
    rw [hval]
    have hb' : beta b ∈ algebraicClosure ℚ ℂ := quad_mem_alg isAlgebraic_r3 _ _ _ _
    have h2 : (2 : ℂ) ∈ algebraicClosure ℚ ℂ := by
      simp
    exact div_mem (mul_mem (mul_mem h2 hb') hp1) (mul_mem hr hp2)

end CM4E.MX
