/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Defs
import CM4E.Waldschmidt
import CM4E.Lattice
import CM4E.Common

/-!
# Theorem 1(a), conditional: four exponentials at `t = cϖ`, `c ∈ ℚ(i)ˣ` (e.g. `2^ϖ`, `3^ϖ`)

This is Theorem MG♮ of the paper with `K = ℚ(i, √2)` (`n = 4`; `n = 2` is too small for MG♮), via W88 §5d.

## The group model `gmQ` (soundness: see the list below and `TRUST.md`)

`G'' = G_m⁸ × Q''`, where `Q'' = (E_i^♮)⁴ / U` is the quotient used in the paper (§3, proof of Theorem MG♮):
* `E_i^♮` is the universal vector extension of `E_i : y² = 4x³ − 4x`, with `ℚ̄`-rational coordinates `(z, w)` dual to
  `(dx/y, −x dx/y)` (with `+x dx/y` the second period coordinate is `−η(λ)`, since `∫ x dx/y = −η`; flipping the sign
  of `w` changes nothing below).
* Its periods are `(λ, η(λ))` for `λ ∈ ϖℤ[i]`, with `η(mϖ + niϖ) = (m − ni)·π/ϖ`. This uses Legendre's relation
  `ϖ η(ϖ) = π` and `η(iλ) = −iη(λ)`, which follows from `ζ(iz) = −iζ(z)`.
* `θ = (1, i, √2, i√2)` is a `ℚ`-basis of `K = ℚ(i, √2)`, and `φ(m) = Σ θ_j m̄_j` on `ℚ(i)⁴`.
* `U = B^♮_{ker φ} + {θᵀw = 0}`, and `Q''` is an anti-affine extension of `A'' = E⁴/B_{ker φ}` (dimension 2) by `G_a`.
* The coordinates on `T(Q'')` are `(ℓ_{τ₁}(z), ℓ_{τ₂}(z), θᵀw)`, where `ℓ_τ(z) = Σ τ(θ_j) z_j` for the two embeddings
  `τ` of `K` with `τ(i) = −i`. These vanish on `T_U` and are independent modulo it.

Soundness facts used to justify the model (not checked by Lean; independently re-derived in `reviews/REFEREE_HYP_NAT.md`):
1. the coordinates and the period formula above;
2. the periods of `Q''` are the images of the periods of `(E^♮)⁴` (`U` is connected);
3. every connected algebraic subgroup of `G_m⁸ × Q''` is `T_L × H` with `H = 0`, the fibre `F`, or `π⁻¹(B')`, and every
   nonzero `H` contains `F` (paper §3, proof of Theorem MG♮; re-derived in `reviews/REFEREE_HYP_NAT.md` §3). Products only:
   there are no nonzero homomorphisms between a torus and `Q''`, so Goursat gives `T_L × H`. Every nonzero `H`
   contains `F`: otherwise `H` would split `π⁻¹(B')` for some `B' ≠ 0`, but the anti-affine image of `B^♮_{S'}` has
   tangent vector `(0, 0, φ(m)) ≠ 0`, so it contains `F`;
4. `d₀ = 0` is maximal (`Q''` is a quotient of an anti-affine group), `d₁ = 8`, and `d₂ = dim Q'' = 3`;
5. `g₂, g₃` of `ϖℤ[i]` are algebraic (premise of the hypothesis).

The model's `lam` only allows `Q''`-components that are periods. That is all the proof needs, and it keeps `lam`
inside `Λ(G'')` trivially.
-/

open Complex Module CM4E.Waldschmidt

namespace CM4E.MainNat

/-- The tangent space `ℂ⁸ × ℂ³` of `G_m⁸ × Q''`. -/
abbrev TN := (Fin 8 → ℂ) × (Fin 3 → ℂ)

/-- `√2` as a complex number. -/
noncomputable def r2 : ℂ := (Real.sqrt 2 : ℂ)

/-- The basis `θ = (1, i, √2, i√2)` of `ℚ(i, √2)`. -/
noncomputable def θ : Fin 4 → ℂ := ![1, I, r2, I * r2]
/-- `τ₁(θ)`, `τ₁ : i ↦ −i, √2 ↦ √2`. -/
noncomputable def θ₁ : Fin 4 → ℂ := ![1, -I, r2, -I * r2]
/-- `τ₂(θ)`, `τ₂ : i ↦ −i, √2 ↦ −√2`. -/
noncomputable def θ₂ : Fin 4 → ℂ := ![1, -I, -r2, I * r2]

/-- The image in `T(Q'')` of the period `((λ_j, η(λ_j)))_j` of `(E^♮)⁴`, `λ_j = (m_j + n_j i)ϖ`. -/
noncomputable def perImg (m n : Fin 4 → ℤ) : Fin 3 → ℂ :=
  ![∑ j, θ₁ j * (((m j : ℂ) + n j * I) * varpi), ∑ j, θ₂ j * (((m j : ℂ) + n j * I) * varpi),
    ∑ j, θ j * etaLem (m j) (n j)]

/-- The periods of `Q''`. -/
def perQ : Set (Fin 3 → ℂ) := Set.range (fun mn : (Fin 4 → ℤ) × (Fin 4 → ℤ) => perImg mn.1 mn.2)

/-- The model of `G_m⁸ × Q''`. -/
noncomputable def gmQ : GroupModel TN where
  d₁ := 8
  d₂ := 3
  alg := fun v => (∀ j, IsAlgebraic ℚ (v.1 j)) ∧ ∀ j, IsAlgebraic ℚ (v.2 j)
  lam := {y | (∀ j, IsAlgebraic ℚ (Complex.exp (y.1 j))) ∧ y.2 ∈ perQ}
  per := Submodule.span ℚ
    (Set.range (fun j : Fin 8 => ((Pi.single j (2 * Real.pi * I) : Fin 8 → ℂ), (0 : Fin 3 → ℂ))) ∪
      (fun q => ((0 : Fin 8 → ℂ), q)) '' perQ)
  sub := fun S => ∃ (L : Submodule ℚ (Fin 8 → ℚ)) (h : Submodule ℂ (Fin 3 → ℂ)),
    (h = ⊥ ∨ Pi.single 2 1 ∈ h) ∧
    S = (Submodule.span ℂ ((fun l : Fin 8 → ℚ => fun j => ((l j : ℚ) : ℂ)) '' (L : Set _))).prod h

/-- **The hypothesis for Theorem 1(a)**: W88 §5d for `G_m⁸ × Q''` (same form as `Thm11Kappa`). -/
def Thm11KappaNat : Prop :=
  IsAlgebraic ℚ lemniscatic.g₂ → IsAlgebraic ℚ lemniscatic.g₃ → HyperplaneKappa gmQ

/-! ## The linear form, `V`, and `W` -/

/-- `θᵀ(block 2) + q₂ − s·θᵀ(block 1)`; its kernel is `V = Ψ''⁻¹(ℂ(1, s))`. -/
noncomputable def phiN (s : ℂ) : TN →ₗ[ℂ] ℂ where
  toFun v := (v.1 4 + I * v.1 5 + r2 * v.1 6 + I * r2 * v.1 7) + v.2 2 -
    s * (v.1 0 + I * v.1 1 + r2 * v.1 2 + I * r2 * v.1 3)
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]; ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma phiN_apply (s : ℂ) (v : TN) : phiN s v = (v.1 4 + I * v.1 5 + r2 * v.1 6 + I * r2 * v.1 7) +
    v.2 2 - s * (v.1 0 + I * v.1 1 + r2 * v.1 2 + I * r2 * v.1 3) := rfl

lemma finrank_TN : finrank ℂ TN = 11 := by simp [TN, Module.finrank_prod]

lemma finrank_ker_phiN (s : ℂ) : finrank ℂ (LinearMap.ker (phiN s)) = 10 := by
  have hsurj : Function.Surjective (phiN s) := fun w => ⟨(0, Pi.single 2 w), by simp [phiN_apply]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (phiN s)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, finrank_TN] at h1
  omega

/-- Nine algebraic vectors in `ker Ψ''`. -/
noncomputable def wN : Fin 9 → TN :=
  ![(![-I, 1, 0, 0, 0, 0, 0, 0], 0), (![-r2, 0, 1, 0, 0, 0, 0, 0], 0),
    (![-I * r2, 0, 0, 1, 0, 0, 0, 0], 0), (![0, 0, 0, 0, -I, 1, 0, 0], 0),
    (![0, 0, 0, 0, -r2, 0, 1, 0], 0), (![0, 0, 0, 0, -I * r2, 0, 0, 1], 0),
    (![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, -1]), (0, ![1, 0, 0]), (0, ![0, 1, 0])]

lemma wN_linearIndependent : LinearIndependent ℂ wN := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e1 := congrArg (fun v : TN => v.1 1) hg
  have e2 := congrArg (fun v : TN => v.1 2) hg
  have e3 := congrArg (fun v : TN => v.1 3) hg
  have e5 := congrArg (fun v : TN => v.1 5) hg
  have e6 := congrArg (fun v : TN => v.1 6) hg
  have e7 := congrArg (fun v : TN => v.1 7) hg
  have f0 := congrArg (fun v : TN => v.2 0) hg
  have f1 := congrArg (fun v : TN => v.2 1) hg
  have f2 := congrArg (fun v : TN => v.2 2) hg
  simp [Fin.sum_univ_succ, wN] at e1 e2 e3 e5 e6 e7 f0 f1 f2
  intro i
  fin_cases i <;> simp_all

lemma finrank_WN : finrank ℂ (Submodule.span ℂ (Set.range wN)) = 9 := by
  rw [finrank_span_eq_card wN_linearIndependent]; simp

lemma WN_le_V (s : ℂ) : Submodule.span ℂ (Set.range wN) ≤ LinearMap.ker (phiN s) := by
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [wN, phiN_apply]

lemma isAlgebraic_r2 : IsAlgebraic ℚ r2 := by simpa [r2] using isAlgebraic_sqrt_nat 2

lemma WN_rational : gmQ.Rational (Submodule.span ℂ (Set.range wN)) := by
  refine ⟨Set.range wN, ?_, rfl⟩
  rintro _ ⟨i, rfl⟩
  have hr := isAlgebraic_r2
  have hI := isAlgebraic_I
  have hIr : IsAlgebraic ℚ (I * r2) := hI.mul hr
  fin_cases i <;> refine ⟨fun j => ?_, fun j => ?_⟩ <;> fin_cases j <;>
    simp [wN, isAlgebraic_zero, isAlgebraic_one, isAlgebraic_one.neg, hI.neg, hr.neg, hIr.neg]

/-! ## The twelve data vectors -/

/-- The exponent `t = cϖ` with `c = D/(p + qi)`. -/
noncomputable def tN (p q : ℤ) (D : ℕ) : ℂ := D * varpi / ((p : ℂ) + q * I)

/-- `λ₀ = (−2q − 2pi)ϖ`, the lattice point whose quasi-period matches `s·2πiD`. -/
noncomputable def lam0 (p q : ℤ) : ℂ := (((-2 * q : ℤ) : ℂ) + ((-2 * p : ℤ) : ℂ) * I) * varpi

/-- `η(λ₀)`. -/
noncomputable def eta0 (p q : ℤ) : ℂ := etaLem (-2 * q) (-2 * p)

/-- Index of slot `h` in the first `G_m`-block. -/
def idx1 (h : Fin 4) : Fin 8 := ⟨h, by omega⟩
/-- Index of slot `h` in the second `G_m`-block. -/
def idx2 (h : Fin 4) : Fin 8 := ⟨h + 4, by omega⟩

/-- The period lift of `θ_h·(2πiD, s·2πiD)`. -/
noncomputable def perV (p q : ℤ) (D : ℕ) (h : Fin 4) : TN :=
  (Pi.single (idx1 h) (2 * Real.pi * I * D), ![θ₁ h * lam0 p q, θ₂ h * lam0 p q, θ h * eta0 p q])

/-- The data lift of `θ_h·(t x, x)`. -/
noncomputable def dataV (t x : ℂ) (h : Fin 4) : TN :=
  (Pi.single (idx1 h) (t * x) + Pi.single (idx2 h) x, 0)

/-- The twelve generators. -/
noncomputable def yN (p q : ℤ) (D : ℕ) (a b : ℂ) : Fin 12 → TN :=
  ![perV p q D 0, perV p q D 1, perV p q D 2, perV p q D 3,
    dataV (tN p q D) a 0, dataV (tN p q D) a 1, dataV (tN p q D) a 2, dataV (tN p q D) a 3,
    dataV (tN p q D) b 0, dataV (tN p q D) b 1, dataV (tN p q D) b 2, dataV (tN p q D) b 3]

lemma phiN_perV (s : ℂ) (p q : ℤ) (D : ℕ) (h : Fin 4) :
    phiN s (perV p q D h) = θ h * eta0 p q - s * (θ h * (2 * Real.pi * I * D)) := by
  fin_cases h <;> simp [phiN_apply, perV, idx1, θ]

lemma phiN_dataV (s t x : ℂ) (h : Fin 4) :
    phiN s (dataV t x h) = θ h * x - s * (θ h * (t * x)) := by
  fin_cases h <;> simp [phiN_apply, dataV, idx1, idx2, θ]

lemma hpq_ne (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) : ((p : ℂ) + q * I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  rcases hpq with hp | hq
  · exact hp (by exact_mod_cast hre)
  · exact hq (by exact_mod_cast him)

lemma eta0_eq (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) :
    eta0 p q = (tN p q D)⁻¹ * (2 * Real.pi * I * D) := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hv := varpi_ne_zero'
  have hc := hpq_ne p q hpq
  simp only [eta0, etaLem, tN]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma tN_ne (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : tN p q D ≠ 0 := by
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hv := varpi_ne_zero'
  simp only [tN]
  exact div_ne_zero (mul_ne_zero hD' hv) (hpq_ne p q hpq)

lemma yN_mem_V (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) (a b : ℂ) (i : Fin 12) :
    yN p q D a b i ∈ LinearMap.ker (phiN (tN p q D)⁻¹) := by
  rw [LinearMap.mem_ker]
  have ht := tN_ne p q D hD hpq
  have he := eta0_eq p q D hD hpq
  fin_cases i <;> simp [yN, phiN_perV, phiN_dataV] <;>
    first
    | (rw [he]; ring)
    | (field_simp; ring)

lemma perImg_single (p q : ℤ) (h : Fin 4) :
    perImg (Pi.single h (-2 * q)) (Pi.single h (-2 * p)) =
      ![θ₁ h * lam0 p q, θ₂ h * lam0 p q, θ h * eta0 p q] := by
  funext k
  fin_cases k <;> fin_cases h <;>
    simp [perImg, lam0, eta0, etaLem, Fin.sum_univ_four, Pi.single_apply]

lemma zero_mem_perQ : (0 : Fin 3 → ℂ) ∈ perQ :=
  ⟨(0, 0), by funext k; fin_cases k <;> simp [perImg, etaLem]⟩

lemma yN_lam (p q : ℤ) (D : ℕ) (a b : ℂ) (ha : a ∈ logAlg) (hb : b ∈ logAlg)
    (hta : IsAlgebraic ℚ (Complex.exp (tN p q D * a)))
    (htb : IsAlgebraic ℚ (Complex.exp (tN p q D * b))) (i : Fin 12) :
    yN p q D a b i ∈ gmQ.lam := by
  have h1 : IsAlgebraic ℚ (1 : ℂ) := isAlgebraic_one
  have hper : ∀ h : Fin 4, ![θ₁ h * lam0 p q, θ₂ h * lam0 p q, θ h * eta0 p q] ∈ perQ :=
    fun h => ⟨(Pi.single h (-2 * q), Pi.single h (-2 * p)), perImg_single p q h⟩
  have hexp : Complex.exp (2 * Real.pi * I * D) = 1 := by
    rw [show (2 * (Real.pi : ℂ) * I * D) = D * (2 * Real.pi * I) by ring]
    exact Complex.exp_nat_mul_two_pi_mul_I D
  fin_cases i <;> refine ⟨fun j => ?_, ?_⟩ <;>
    simp [yN, perV, dataV] <;>
    first
    | exact hper _
    | exact zero_mem_perQ
    | (fin_cases j <;> simp [idx1, idx2, hexp, h1] <;>
        first | exact ha | exact hb | exact hta | exact htb)

/-! ## Rank, period rank, and the final contradiction -/

lemma yN_linearIndependent (p q : ℤ) (D : ℕ) (hD : 0 < D) (a b : ℂ)
    (hind : LinearIndependent ℚ ![a, b]) : LinearIndependent ℚ (yN p q D a b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hli := Fintype.linearIndependent_iff.mp hind
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hpi := pi_ne_zero'
  have e4 := congrArg (fun v : TN => v.1 4) hg
  have e5 := congrArg (fun v : TN => v.1 5) hg
  have e6 := congrArg (fun v : TN => v.1 6) hg
  have e7 := congrArg (fun v : TN => v.1 7) hg
  simp [Fin.sum_univ_succ, yN, perV, dataV, idx1, idx2, Rat.smul_def]
    at e4 e5 e6 e7
  have c4 := hli ![g 4, g 8] (by simp [Fin.sum_univ_succ, Rat.smul_def]; linear_combination e4)
  have c5 := hli ![g 5, g 9] (by simp [Fin.sum_univ_succ, Rat.smul_def]; linear_combination e5)
  have c6 := hli ![g 6, g 10] (by simp [Fin.sum_univ_succ, Rat.smul_def]; linear_combination e6)
  have c7 := hli ![g 7, g 11] (by simp [Fin.sum_univ_succ, Rat.smul_def]; linear_combination e7)
  have g4 : g 4 = 0 := by simpa using c4 0
  have g8 : g 8 = 0 := by simpa using c4 1
  have g5 : g 5 = 0 := by simpa using c5 0
  have g9 : g 9 = 0 := by simpa using c5 1
  have g6 : g 6 = 0 := by simpa using c6 0
  have g10 : g 10 = 0 := by simpa using c6 1
  have g7 : g 7 = 0 := by simpa using c7 0
  have g11 : g 11 = 0 := by simpa using c7 1
  have e0 := congrArg (fun v : TN => v.1 0) hg
  have e1 := congrArg (fun v : TN => v.1 1) hg
  have e2 := congrArg (fun v : TN => v.1 2) hg
  have e3 := congrArg (fun v : TN => v.1 3) hg
  simp [Fin.sum_univ_succ, yN, perV, dataV, idx1, idx2, Rat.smul_def,
    g4, g5, g6, g7, g8, g9, g10, g11, hD', hpi, Complex.I_ne_zero] at e0 e1 e2 e3
  intro i
  fin_cases i <;> simp_all

lemma perV_mem_per (p q : ℤ) (D : ℕ) (h : Fin 4) : perV p q D h ∈ gmQ.per := by
  have hdec : perV p q D h =
      (D : ℚ) • ((Pi.single (idx1 h) (2 * Real.pi * I) : Fin 8 → ℂ), (0 : Fin 3 → ℂ)) +
        ((0 : Fin 8 → ℂ), ![θ₁ h * lam0 p q, θ₂ h * lam0 p q, θ h * eta0 p q]) := by
    refine Prod.ext ?_ ?_
    · funext j
      by_cases hj : j = idx1 h
      · subst hj; simp [perV, Rat.smul_def]; ring
      · simp [perV, hj]
    · simp [perV]
  rw [hdec]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨idx1 h, rfl⟩)))
    (Submodule.subset_span (Or.inr ⟨_, ⟨(Pi.single h (-2 * q), Pi.single h (-2 * p)),
      perImg_single p q h⟩, rfl⟩))

lemma key_contraN (hT : Transcendental ℚ (varpi : ℂ)) (p q : ℤ) (D : ℕ) (hD : 0 < D)
    (hpq : p ≠ 0 ∨ q ≠ 0) (l : Fin 8 → ℚ) (hl0 : l ≠ 0)
    (h : ((l 4 : ℂ) + I * (l 5 : ℂ) + r2 * (l 6 : ℂ) + I * r2 * (l 7 : ℂ)) -
      (tN p q D)⁻¹ * ((l 0 : ℂ) + I * (l 1 : ℂ) + r2 * (l 2 : ℂ) + I * r2 * (l 3 : ℂ)) = 0) :
    False := by
  set A : ℂ := (l 0 : ℂ) + I * (l 1 : ℂ) + r2 * (l 2 : ℂ) + I * r2 * (l 3 : ℂ) with hA
  set B : ℂ := (l 4 : ℂ) + I * (l 5 : ℂ) + r2 * (l 6 : ℂ) + I * r2 * (l 7 : ℂ) with hB
  have ht := tN_ne p q D hD hpq
  have hBA : B = (tN p q D)⁻¹ * A := by linear_combination h
  by_cases hA0 : A = 0
  · obtain ⟨h0, h1, h2, h3⟩ := quad_inj irrational_sqrt_two _ _ _ _ hA0
    rw [hA0, mul_zero] at hBA
    obtain ⟨h4, h5, h6, h7⟩ := quad_inj irrational_sqrt_two _ _ _ _ hBA
    exact hl0 (by funext j; fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, h6, h7])
  · have hB0 : B ≠ 0 := by rw [hBA]; exact mul_ne_zero (inv_ne_zero ht) hA0
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hc := hpq_ne p q hpq
    have hv0 := varpi_ne_zero'
    have hv : (varpi : ℂ) = ((p : ℂ) + q * I) * A / (D * B) := by
      rw [hBA]; simp only [tN]; field_simp
    apply hT
    rw [← mem_algebraicClosure_iff, hv]
    have hI : I ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.mpr isAlgebraic_I
    have hq : ∀ r : ℚ, (r : ℂ) ∈ algebraicClosure ℚ ℂ := fun r =>
      mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap r)
    have hz : ∀ r : ℤ, (r : ℂ) ∈ algebraicClosure ℚ ℂ := fun r => by exact_mod_cast hq r
    have hn : (D : ℂ) ∈ algebraicClosure ℚ ℂ := by exact_mod_cast hq D
    have hAm : A ∈ algebraicClosure ℚ ℂ := quad_mem_alg isAlgebraic_r2 _ _ _ _
    have hBm : B ∈ algebraicClosure ℚ ℂ := quad_mem_alg isAlgebraic_r2 _ _ _ _
    exact div_mem (mul_mem (add_mem (hz p) (mul_mem (hz q) hI)) hAm) (mul_mem hn hBm)

/-- **Conditional Theorem 1(a) for `c ∈ ℚ(i)ˣ`**: four exponentials at `t = Dϖ/(p + qi)`. Hypotheses: W88 §5d
for `G_m⁸ × Q''` (`hW`), `g₂(ϖℤ[i]) ∈ ℚ̄` (`hg₂`), and the transcendence of `ϖ` (`hT`, Schneider 1937). -/
theorem main (hW : Thm11KappaNat) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hT : Transcendental ℚ (varpi : ℂ))
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (tN p q D) := by
  intro a b ha hb hind ⟨hta, htb⟩
  have hliY := yN_linearIndependent p q D hD a b hind
  have hfinY : finrank ℚ (Submodule.span ℚ (Set.range (yN p q D a b))) = 12 := by
    rw [finrank_span_eq_card hliY]; simp
  have hfd : FiniteDimensional ℚ (Submodule.span ℚ (Set.range (yN p q D a b))) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range _)
  have hk : 4 ≤ finrank ℚ ↥(Submodule.span ℚ (Set.range (yN p q D a b)) ⊓ gmQ.per) := by
    let f : Fin 4 → ↥(Submodule.span ℚ (Set.range (yN p q D a b)) ⊓ gmQ.per) := fun h =>
      ⟨perV p q D h, Submodule.subset_span ⟨⟨h, by omega⟩, by fin_cases h <;> rfl⟩, perV_mem_per p q D h⟩
    have hf : LinearIndependent ℚ f := by
      apply LinearIndependent.of_comp (Submodule.span ℚ (Set.range (yN p q D a b)) ⊓ gmQ.per).subtype
      have := hliY.comp (fun h : Fin 4 => (⟨h, by omega⟩ : Fin 12))
        (fun h₁ h₂ e => by simpa [Fin.ext_iff] using e)
      convert this using 1
      funext h; fin_cases h <;> rfl
    simpa using hf.fintype_card_le_finrank
  obtain ⟨S, ⟨L, hsub, hfib, rfl⟩, hne, hle⟩ := hW hg₂ g₃_lemniscatic_isAlgebraic
    (LinearMap.ker (phiN (tN p q D)⁻¹)) (Submodule.span ℂ (Set.range wN)) 12 (yN p q D a b)
    (by rw [finrank_ker_phiN, finrank_TN]) (WN_le_V _) WN_rational
    (fun i => ⟨yN_mem_V p q D hD hpq a b i, yN_lam p q D a b ha hb hta htb i⟩)
    (by
      show ((finrank ℚ (Submodule.span ℚ (Set.range (yN p q D a b))) : ℤ) >
        ((8 : ℤ) + 2 * 3 - finrank ℚ ↥(Submodule.span ℚ (Set.range (yN p q D a b)) ⊓ gmQ.per)) *
          ((finrank ℂ TN : ℤ) - 1 - finrank ℂ (Submodule.span ℂ (Set.range wN))))
      rw [hfinY, finrank_WN, finrank_TN]; push_cast; omega)
  rcases hfib with rfl | hfib
  · have hL : L ≠ ⊥ := by
      rintro rfl
      apply hne
      have h0 : (fun _ : Fin 8 => (0 : ℂ)) = 0 := rfl
      simp [h0, Submodule.prod_bot]
    obtain ⟨l, hl, hl0⟩ := Submodule.ne_bot_iff _ |>.mp hL
    have hmem : ((fun j => ((l j : ℚ) : ℂ)), (0 : Fin 3 → ℂ)) ∈
        (Submodule.span ℂ ((fun l : Fin 8 → ℚ => fun j => ((l j : ℚ) : ℂ)) '' (L : Set _))).prod ⊥ := by
      rw [Submodule.mem_prod]; exact ⟨Submodule.subset_span ⟨l, hl, rfl⟩, by simp⟩
    have hV := hle hmem
    rw [LinearMap.mem_ker, phiN_apply] at hV
    exact key_contraN hT p q D hD hpq l hl0 (by simpa using hV)
  · have hmem : ((0 : Fin 8 → ℂ), (Pi.single 2 1 : Fin 3 → ℂ)) ∈
        (Submodule.span ℂ ((fun l : Fin 8 → ℚ => fun j => ((l j : ℚ) : ℂ)) '' (L : Set _))).prod hsub := by
      rw [Submodule.mem_prod]; exact ⟨Submodule.zero_mem _, hfib⟩
    have hV := hle hmem
    rw [LinearMap.mem_ker, phiN_apply] at hV
    simp at hV

/-- **`2^ϖ` and `3^ϖ` are not both algebraic**, conditional on W88 §5d for `G_m⁸ × Q''`, on `g₂(ϖℤ[i]) ∈ ℚ̄`, and on
the transcendence of `ϖ`. -/
theorem two_three_varpi (hW : Thm11KappaNat) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hT : Transcendental ℚ (varpi : ℂ)) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 3))) := by
  have ht : tN 1 0 1 = (varpi : ℂ) := by simp [tN]
  rw [← ht]
  exact main hW hg₂ hT 1 0 1 one_pos (Or.inl one_ne_zero) (Complex.log 2) (Complex.log 3)
    (by simpa using log_mem_logAlg 2 two_ne_zero) (by simpa using log_mem_logAlg 3 three_ne_zero)
    linearIndependent_two_three

end CM4E.MainNat
