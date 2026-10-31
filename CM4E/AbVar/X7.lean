/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.Basis
import CM4E.AbVar.Fermat7
import CM4E.AbVar.FrameX
import CM4E.Gen.ThmM

/-!
# Theorem X at level seven (paper [II], §`sec:X7`)

`A = Jac(C)`, `C : y⁷ = x(1 − x)` (CM by `F = ℚ(ζ)`, `ζ = ζ₇`, type `{1, 2, 3}`; eigen-coordinates `z₁, z₂, z₃` dual to
`dx/y⁶, dx/y⁵, dx/y⁴`, with `z_s(γ) = perA s` for one cycle `γ`) and `E` with period lattice `Ω ℤ[α]`, `Ω = B(1/7, 2/7)`,
`α = (−1 + √−7)/2` (CM by `k = ℚ(√−7) ⊂ F`). The slots are `a = z₁`, `b = z₂`, `c = z₃`, `d = E`, with the first-kind
relation `P₁P₂ = μ'P₃Ω` (`relation_R`, proved).

**The group.** For an `F`-basis `b` of a number field `K` (`θ(j, e) = ζ^e b j`, `n = 6r`), the paper's
`G'' = G^n/U = A'' × G_a²` is written as `A^{3r} × E^{3r} × G_a²` in explicit eigen-coordinates: `A^{3r}` = three blocks
`t = 0, 1, 2` (one per slot of `A`) of `r` copies of `A`, coordinates `zA t s j` (`s` = eigen-coordinate); `E^{3r}`, coordinates
`zE (j, e)`, `e < 3`. The slot forms are
`μ₁ = Σ_j b_j zA 0 0 j + Σ_{j, e<3} ζ^e b_j zE (j, e)` and `μ₂ = Σ_j b_j zA 2 2 j + Σ_j b_j zA 1 1 j`, and
`Ψ'' = (μ₁ + q₁, μ₂ + q₂)` (frame `CM4E/AbVar/FrameX.lean`). The logarithms of `A` are a parameter `LA` (triples
`(z₁(v), z₂(v), z₃(v))`; Lean has no Jacobians), always together with the period triple `γ`; the copy `j` of block `t` carries
`[ζ^e]v` (coordinates `ζ^{(s+1)e} v_s`); the logarithms of `E` are `u, αu` with `u ∈ 𝓛_E` (`LogE`).

Soundness of `gmX7 LA b` (not checked by Lean; `reviews/`): `A^{3r} × E^{3r} × G_a²` is an algebraic group over `ℚ̄`
(`E` has algebraic invariants by Chowla–Selberg); `perA s = z_s(γ)` (Rohrlich); `[ζ^e]` acts on `z_s` by `ζ^{(s+1)e}`
(`σ_s(ζ) = ζ^s`); `LA` consists of eigen-coordinate triples of logarithms of algebraic points of `A`; connected subgroups
are products `B × B' × L` (`A` simple, not isogenous to `E`); a nonzero abelian subvariety of `A^{3r}` (an `F`-subspace
`S' ⊂ F^{3r}`) is killed by the three slot forms only if `S' = 0`, since `b` is `F`-independent and different `σ_s` carry
independent tangent directions; one of `E^{3r}` (`S'' ⊂ k^{3r}`) only if `S'' = 0`, since `{ζ^e b_j}_{e<3}` is a `k`-basis of `K`;
`G_a²` has `Ψ'' = id`.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

lemma omega7_ne : omega7 ≠ 0 := by
  rw [omega7, betaG]
  exact div_ne_zero (mul_ne_zero (Gamma_ne_zero_of_re_pos (by norm_num))
    (Gamma_ne_zero_of_re_pos (by norm_num))) (Gamma_ne_zero_of_re_pos (by norm_num))

lemma perA_ne {j : ℕ} (h0 : 0 < j) (h7 : j < 7) : perA j ≠ 0 := by
  rw [perA, betaG]
  have hre : 0 < ((j : ℂ) / 7).re := by simp; positivity
  exact mul_ne_zero (one_sub_zeta7_pow_ne h0 h7) (div_ne_zero (mul_ne_zero
    (Gamma_ne_zero_of_re_pos hre) (Gamma_ne_zero_of_re_pos hre))
    (Gamma_ne_zero_of_re_pos (by simp; positivity)))

/-- The period pair `(Ω, αΩ)` of `E`. -/
noncomputable def E7 : PeriodPair where
  ω₁ := omega7
  ω₂ := alpha7 * omega7
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h' : ((s : ℂ) + t * alpha7) * omega7 = 0 := by
      rw [← h]; simp [Complex.real_smul]; ring
    have h2 := (mul_eq_zero.mp h').resolve_right omega7_ne
    have him := congrArg Complex.im h2
    simp at him
    have ht : t = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h alpha7_im_ne
    subst ht
    simpa using h2

/-- The period triple `(perA 1, perA 2, perA 3)` of the cycle `γ`. -/
noncomputable def perT : Fin 3 → ℂ := fun s => perA ((s : ℕ) + 1)

variable {r : ℕ} (b : Fin r → ℂ)

/-- `T(A^{3r} × E^{3r})`. -/
abbrev QX7 (r : ℕ) := (Fin 3 → Fin 3 → Fin r → ℂ) × (Fin r × Fin 3 → ℂ)

/-- The slot form `μ₁ = θᵀz₁ + θᵀu` (slots `a`, `d`). -/
noncomputable def mu1 : QX7 r →ₗ[ℂ] ℂ where
  toFun q := ∑ j, b j * q.1 0 0 j + ∑ p : Fin r × Fin 3, zeta7 ^ (p.2 : ℕ) * b p.1 * q.2 p
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [mul_add, Finset.mul_sum, Finset.mul_sum]; congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-- The slot form `μ₂ = θᵀz₃ + θᵀz₂` (slots `c`, `b`). -/
noncomputable def mu2 : QX7 r →ₗ[ℂ] ℂ where
  toFun q := ∑ j, b j * q.1 2 2 j + ∑ j, b j * q.1 1 1 j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' c x := by simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; rw [mul_add, Finset.mul_sum, Finset.mul_sum]; congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-- `[ζ^e]v` in copy `j` of block `t`. -/
noncomputable def aGen (t : Fin 3) (j : Fin r) (e : ℕ) (v : Fin 3 → ℂ) : TX (QX7 r) :=
  ((fun t' s j' => if t' = t ∧ j' = j then zeta7 ^ (((s : ℕ) + 1) * e) * v s else 0, 0), 0, 0)

/-- `w` in coordinate `(j, e)` of `E^{3r}`. -/
noncomputable def eGen (p : Fin r × Fin 3) (w : ℂ) : TX (QX7 r) := ((0, Pi.single p w), 0, 0)

/-- Generators of the logarithms. -/
def lamX7 (LA : Set (Fin 3 → ℂ)) : Set (TX (QX7 r)) :=
  {x | ∃ t j e, ∃ v ∈ insert perT LA, x = aGen t j e v} ∪
    {x | ∃ p u, LogE E7 u ∧ (x = eGen p u ∨ x = eGen p (alpha7 * u))} ∪
    {x | ∃ c₁ c₂ : ℂ, IsAlgebraic ℚ c₁ ∧ IsAlgebraic ℚ c₂ ∧ x = ((0, 0), c₁, c₂)}

/-- Generators of the periods. -/
noncomputable def perX7 : Set (TX (QX7 r)) :=
  {x | ∃ t j e, x = aGen t j e perT} ∪ {x | ∃ p, x = eGen p omega7 ∨ x = eGen p (alpha7 * omega7)}

/-- The `ℚ̄`-structure of `T(A^{3r} × E^{3r})`. -/
def algQX7 (q : QX7 r) : Prop := (∀ t s j, IsAlgebraic ℚ (q.1 t s j)) ∧ ∀ p, IsAlgebraic ℚ (q.2 p)

/-- **The model of `A^{3r} × E^{3r} × G_a²`.** -/
noncomputable def gmX7 (LA : Set (Fin 3 → ℂ)) : GroupModel (TX (QX7 r)) :=
  gmFX (algQX7 (r := r)) (lamX7 LA) perX7 (mu1 b) (mu2 b)

/-- **The hypothesis for Theorem X7**: W88 §5d for `A^{3r} × E^{3r} × G_a²`, for every `F`-basis `b` of a number field. -/
def Thm11KappaX7 (LA : Set (Fin 3 → ℂ)) : Prop :=
  ∀ (r : ℕ) (b : Fin r → ℂ), IsAdaptedBasisD zeta7 6 b → HyperplaneKappa (gmX7 b LA)

/-! ## Arithmetic of `ζ` inside `K` -/

lemma natDegree_minpoly_zeta7 : (minpoly ℚ zeta7).natDegree = 6 := by
  rw [← Polynomial.cyclotomic_eq_minpoly_rat zeta7_prim (by norm_num), Polynomial.natDegree_cyclotomic]
  rfl

lemma exists_adapted_basis7 (S : Finset ℂ) (hS : ∀ s ∈ S, IsAlgebraic ℚ s) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ b : Fin r → ℂ, IsAdaptedBasisD zeta7 6 b ∧ ∀ s ∈ S, s ∈ KspanD zeta7 6 b := by
  have h := exists_adapted_basisD zeta7 isAlgebraic_zeta7 S hS
  rw [natDegree_minpoly_zeta7] at h
  exact h

variable {b}

lemma zeta7_mul_mem {x : ℂ} (hx : x ∈ KspanD zeta7 6 b) :
    zeta7 * x ∈ KspanD zeta7 6 b := by
  have hgen : ∀ p, zeta7 * thetaD zeta7 6 b p ∈ KspanD zeta7 6 b := by
    rintro ⟨j, e⟩
    by_cases he : (e : ℕ) < 5
    · refine Submodule.subset_span ⟨(j, ⟨e + 1, by omega⟩), ?_⟩
      simp [thetaD, pow_succ]; ring
    · have he5 : (e : ℕ) = 5 := by omega
      have : zeta7 * thetaD zeta7 6 b (j, e) = -∑ e' : Fin 6, (1 : ℚ) • thetaD zeta7 6 b (j, e') := by
        simp only [thetaD, he5, one_smul, Fin.sum_univ_six]
        simp
        linear_combination (b j) * zeta7_sum
      rw [this]
      exact neg_mem (Submodule.sum_mem _ fun e' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  refine Submodule.span_induction (fun y ⟨p, hp⟩ => hp ▸ hgen p) (by simp) (fun y z _ _ hy hz => ?_)
    (fun c y _ hy => ?_) hx
  · rw [mul_add]; exact add_mem hy hz
  · rw [Rat.smul_def, mul_left_comm, ← Rat.smul_def]; exact Submodule.smul_mem _ _ hy

lemma zeta7_mem (hb : IsAdaptedBasisD zeta7 6 b) : zeta7 ∈ KspanD zeta7 6 b := by
  simpa using zeta7_mul_mem hb.one_mem

lemma mu7'_mem (hb : IsAdaptedBasisD zeta7 6 b) : mu7' ∈ KspanD zeta7 6 b := by
  have hz := zeta7_mem hb
  have h1 := hb.one_mem
  have hp : ∀ k : ℕ, zeta7 ^ k ∈ KspanD zeta7 6 b := by
    intro k; induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ']; exact hb.mul_mem _ hz _ ih
  rw [mu7', mu7, div_eq_mul_inv]
  exact hb.mul_mem _ (hb.mul_mem _ (hb.mul_mem _ (sub_mem h1 hz) _ (sub_mem h1 (hp 2))) _
    (add_mem (add_mem h1 hz) (hp 6))) _ (hb.inv_mem _ (sub_mem h1 (hp 3)))

/-- `ζ^e` (`e < 6`) in the `k`-basis `1, ζ, ζ²`: rational parts. -/
def zp : Fin 6 → Fin 3 → ℚ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![0, -1, -1], ![-1, -1, -1]]

/-- `ζ^e` (`e < 6`) in the `k`-basis `1, ζ, ζ²`: `α`-parts. -/
def zq : Fin 6 → Fin 3 → ℚ :=
  ![![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, 1], ![1, 0, 0], ![0, 0, -1]]

lemma zeta_expand (e : Fin 6) :
    zeta7 ^ (e : ℕ) = ∑ e' : Fin 3, ((zp e e' : ℂ) + zq e e' * alpha7) * zeta7 ^ (e' : ℕ) := by
  have h3 := zeta_pow_three
  have h4 := zeta_pow_four
  have h5 := zeta_pow_five
  fin_cases e <;> simp [zp, zq, Fin.sum_univ_three] <;>
    first | linear_combination h3 | linear_combination h4 | linear_combination h5

/-! ## Lifts -/

lemma PsiX_qsmul {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q] (μ₁ μ₂ : Q →ₗ[ℂ] ℂ) (c : ℚ)
    (v : TX Q) : PsiX μ₁ μ₂ (c • v) = ((c : ℂ) * (PsiX μ₁ μ₂ v).1, (c : ℂ) * (PsiX μ₁ μ₂ v).2) := by
  rw [map_rat_smul]
  exact Prod.ext (by rw [Prod.smul_fst, Rat.smul_def]) (by rw [Prod.smul_snd, Rat.smul_def])

variable (b)

/-- A lift in block `t` with exponent multiplier `mt`: `Σ_p m_p [ζ^{mt·e_p}]v` in copy `j_p`. -/
noncomputable def aLift (t : Fin 3) (mt : ℕ) (m : Fin r × Fin 6 → ℚ) (v : Fin 3 → ℂ) : TX (QX7 r) :=
  ∑ p, m p • aGen t p.1 (mt * (p.2 : ℕ)) v

/-- A lift in `E^{3r}`: `ζ^e b_j u` rewritten in the `k`-basis `1, ζ, ζ²` (`zeta_expand`). -/
noncomputable def eLift (m : Fin r × Fin 6 → ℚ) (u : ℂ) : TX (QX7 r) :=
  ∑ p, ∑ e' : Fin 3, ((m p * zp p.2 e') • eGen (p.1, e') u + (m p * zq p.2 e') • eGen (p.1, e') (alpha7 * u))

variable {b}

lemma PsiX_aGen0 (j : Fin r) (e : ℕ) (v : Fin 3 → ℂ) :
    PsiX (mu1 b) (mu2 b) (aGen 0 j e v) = (b j * (zeta7 ^ e * v 0), 0) := by
  simp [PsiX_apply, aGen, mu1, mu2]

lemma PsiX_aGen1 (j : Fin r) (e : ℕ) (v : Fin 3 → ℂ) :
    PsiX (mu1 b) (mu2 b) (aGen 1 j e v) = (0, b j * (zeta7 ^ (2 * e) * v 1)) := by
  simp [PsiX_apply, aGen, mu1, mu2]

lemma PsiX_aGen2 (j : Fin r) (e : ℕ) (v : Fin 3 → ℂ) :
    PsiX (mu1 b) (mu2 b) (aGen 2 j e v) = (0, b j * (zeta7 ^ (3 * e) * v 2)) := by
  simp [PsiX_apply, aGen, mu1, mu2]

lemma PsiX_eGen (p : Fin r × Fin 3) (w : ℂ) :
    PsiX (mu1 b) (mu2 b) (eGen p w) = (zeta7 ^ (p.2 : ℕ) * b p.1 * w, 0) := by
  simp [PsiX_apply, eGen, mu1, mu2, Pi.single_apply]

lemma zeta7_pow_eight (e : ℕ) : zeta7 ^ (2 * (4 * e)) = zeta7 ^ e := by
  rw [show 2 * (4 * e) = 7 * e + e by ring, pow_add, pow_mul, zeta7_pow_seven, one_pow, one_mul]

lemma zeta7_pow_fifteen (e : ℕ) : zeta7 ^ (3 * (5 * e)) = zeta7 ^ e := by
  rw [show 3 * (5 * e) = 7 * (2 * e) + e by ring, pow_add, pow_mul, zeta7_pow_seven, one_pow, one_mul]

lemma PsiX_aLift0 (m : Fin r × Fin 6 → ℚ) (v : Fin 3 → ℂ) :
    PsiX (mu1 b) (mu2 b) (aLift (r := r) 0 1 m v) = ((∑ p, (m p : ℂ) * thetaD zeta7 6 b p) * v 0, 0) := by
  simp only [aLift, map_sum, PsiX_qsmul, PsiX_aGen0, one_mul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by simp [thetaD]; ring
  · simp [Prod.snd_sum]

lemma PsiX_aLift1 (m : Fin r × Fin 6 → ℚ) (v : Fin 3 → ℂ) :
    PsiX (mu1 b) (mu2 b) (aLift (r := r) 1 4 m v) = (0, (∑ p, (m p : ℂ) * thetaD zeta7 6 b p) * v 1) := by
  simp only [aLift, map_sum, PsiX_qsmul, PsiX_aGen1, zeta7_pow_eight]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp only [Prod.snd_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by simp [thetaD]; ring

lemma PsiX_aLift2 (m : Fin r × Fin 6 → ℚ) (v : Fin 3 → ℂ) :
    PsiX (mu1 b) (mu2 b) (aLift (r := r) 2 5 m v) = (0, (∑ p, (m p : ℂ) * thetaD zeta7 6 b p) * v 2) := by
  simp only [aLift, map_sum, PsiX_qsmul, PsiX_aGen2, zeta7_pow_fifteen]
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp only [Prod.snd_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by simp [thetaD]; ring

lemma PsiX_eLift (m : Fin r × Fin 6 → ℚ) (u : ℂ) :
    PsiX (mu1 b) (mu2 b) (eLift (r := r) m u) = ((∑ p, (m p : ℂ) * thetaD zeta7 6 b p) * u, 0) := by
  simp only [eLift, map_sum, map_add, PsiX_qsmul, PsiX_eGen]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sum, Prod.fst_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hz := zeta_expand p.2
    rw [thetaD, hz]
    simp only [Rat.cast_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e' _ => by ring
  · simp [Prod.snd_sum]

lemma aLift_mem (LA : Set (Fin 3 → ℂ)) (t : Fin 3) (mt : ℕ) (m : Fin r × Fin 6 → ℚ) {v : Fin 3 → ℂ}
    (hv : v ∈ insert perT LA) : aLift (r := r) t mt m v ∈ Submodule.span ℚ (lamX7 LA) :=
  Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Or.inl (Or.inl ⟨t, p.1, _, v, hv, rfl⟩)))

lemma aLift_per (t : Fin 3) (mt : ℕ) (m : Fin r × Fin 6 → ℚ) :
    aLift (r := r) t mt m perT ∈ Submodule.span ℚ (perX7 (r := r)) :=
  Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨t, p.1, _, rfl⟩))

lemma eLift_mem (LA : Set (Fin 3 → ℂ)) (m : Fin r × Fin 6 → ℚ) {u : ℂ} (hu : LogE E7 u) :
    eLift (r := r) m u ∈ Submodule.span ℚ (lamX7 LA) :=
  Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ => add_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨_, u, hu, Or.inl rfl⟩))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨_, u, hu, Or.inr rfl⟩))))

lemma eLift_per (m : Fin r × Fin 6 → ℚ) : eLift (r := r) m omega7 ∈ Submodule.span ℚ (perX7 (r := r)) :=
  Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ => add_mem
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨_, Or.inl rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨_, Or.inr rfl⟩)))

/-! ## Proposition X at level seven -/

/-- **Named input (Wüstholz 1989; paper [II], (W)).** `1, P₁, P₂, P₃, Ω` are linearly independent over `ℚ̄`: periods of
pairwise distinct eigen-slots (three of `A`, one of `E`) and `1`. -/
def WuestholzBeta7 : Prop :=
  ∀ a₀ a₁ a₂ a₃ a₄ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → IsAlgebraic ℚ a₃ →
    IsAlgebraic ℚ a₄ → a₀ + a₁ * perA 1 + a₂ * perA 2 + a₃ * perA 3 + a₄ * omega7 = 0 →
      a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0

/-- The single-coordinate vector of `A^{3r}`. -/
def single3 (t s : Fin 3) (j : Fin r) : Fin 3 → Fin 3 → Fin r → ℂ :=
  fun t' s' j' => if t' = t ∧ s' = s ∧ j' = j then 1 else 0

lemma span_algQX7 : Submodule.span ℂ {q : QX7 r | algQX7 q} = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  have hdec : q = ∑ t, ∑ s, ∑ j, q.1 t s j • ((single3 t s j, 0) : QX7 r) +
      ∑ p, q.2 p • (((0 : Fin 3 → Fin 3 → Fin r → ℂ), Pi.single p 1) : QX7 r) := by
    refine Prod.ext ?_ ?_
    · funext t s j
      simp [Prod.fst_sum, Finset.sum_apply, single3, ite_and, Finset.sum_ite_eq]
    · funext p
      simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hdec]
  refine add_mem (Submodule.sum_mem _ fun t _ => Submodule.sum_mem _ fun s _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun t' s' j' => ?_, fun p => ?_⟩))
    (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun t' s' j' => ?_, fun p' => ?_⟩))
  · simp only [single3]; split_ifs
    exacts [isAlgebraic_one, isAlgebraic_zero]
  · exact isAlgebraic_zero
  · exact isAlgebraic_zero
  · simp only [Pi.single_apply]; split_ifs
    exacts [isAlgebraic_one, isAlgebraic_zero]

lemma mu1_alg (hb : IsAdaptedBasisD zeta7 6 b) {q : QX7 r} (hq : algQX7 q) : IsAlgebraic ℚ (mu1 b q) := by
  show IsAlgebraic ℚ (∑ j, b j * q.1 0 0 j + ∑ p : Fin r × Fin 3, zeta7 ^ (p.2 : ℕ) * b p.1 * q.2 p)
  rw [← mem_algebraicClosure_iff]
  have hz := mem_algebraicClosure_iff.mpr isAlgebraic_zeta7
  exact add_mem (sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hb.alg j))
    (mem_algebraicClosure_iff.mpr (hq.1 _ _ _))) (sum_mem fun p _ => mul_mem (mul_mem (pow_mem hz _)
    (mem_algebraicClosure_iff.mpr (hb.alg _))) (mem_algebraicClosure_iff.mpr (hq.2 _)))

lemma mu2_alg (hb : IsAdaptedBasisD zeta7 6 b) {q : QX7 r} (hq : algQX7 q) : IsAlgebraic ℚ (mu2 b q) := by
  show IsAlgebraic ℚ (∑ j, b j * q.1 2 2 j + ∑ j, b j * q.1 1 1 j)
  rw [← mem_algebraicClosure_iff]
  exact add_mem (sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hb.alg j))
    (mem_algebraicClosure_iff.mpr (hq.1 _ _ _))) (sum_mem fun j _ => mul_mem
    (mem_algebraicClosure_iff.mpr (hb.alg j)) (mem_algebraicClosure_iff.mpr (hq.1 _ _ _)))

lemma finrank_QX7 : finrank ℂ (QX7 r) = 12 * r := by
  simp [QX7, Module.finrank_prod, Module.finrank_pi_fintype]; ring

/-- **Proposition X at level seven** (`K`-form, one vector): with `K = span_ℚ θ ∋ β`, data `x = Σ c₁ₖ z₁(v₁ₖ) + Σ dₖ uₖ + q₁`
(slots `a`, `d`) and `y = Σ c₃ₖ z₃(v₃ₖ) + Σ c₂ₖ z₂(v₂ₖ) + q₂` (slots `c`, `b`), with coefficients in `K`, `vᵢₖ` logarithms of
`A` (or the period `γ`), `uₖ ∈ 𝓛_E`, `q₁, q₂ ∈ ℚ̄`, and `x·βP₃ = y·P₁`, one has `x ∈ K P₁ + K Ω`. -/
theorem propX7_K (LA : Set (Fin 3 → ℂ)) (hW : HyperplaneKappa (gmX7 b LA)) (hb : IsAdaptedBasisD zeta7 6 b)
    (hWB : WuestholzBeta7) (β : ℂ) (hβK : β ∈ KspanD zeta7 6 b) (hβ0 : β ≠ 0)
    {N₁ N₂ N₃ M : ℕ} (c₁ : Fin N₁ → ℂ) (v₁ : Fin N₁ → Fin 3 → ℂ) (c₂ : Fin N₂ → ℂ) (v₂ : Fin N₂ → Fin 3 → ℂ)
    (c₃ : Fin N₃ → ℂ) (v₃ : Fin N₃ → Fin 3 → ℂ) (d : Fin M → ℂ) (u : Fin M → ℂ) (q₁ q₂ : ℂ)
    (hc₁ : ∀ k, c₁ k ∈ KspanD zeta7 6 b) (hc₂ : ∀ k, c₂ k ∈ KspanD zeta7 6 b)
    (hc₃ : ∀ k, c₃ k ∈ KspanD zeta7 6 b) (hd : ∀ k, d k ∈ KspanD zeta7 6 b)
    (hv₁ : ∀ k, v₁ k ∈ insert perT LA) (hv₂ : ∀ k, v₂ k ∈ insert perT LA) (hv₃ : ∀ k, v₃ k ∈ insert perT LA)
    (hu : ∀ k, LogE E7 (u k)) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂)
    (hrel : (∑ k, c₁ k * v₁ k 0 + ∑ k, d k * u k + q₁) * (β * perA 3) =
      (∑ k, c₃ k * v₃ k 2 + ∑ k, c₂ k * v₂ k 1 + q₂) * perA 1) :
    ∃ c c' : ℂ, c ∈ KspanD zeta7 6 b ∧ c' ∈ KspanD zeta7 6 b ∧
      ∑ k, c₁ k * v₁ k 0 + ∑ k, d k * u k + q₁ = c * perA 1 + c' * omega7 := by
  set x := ∑ k, c₁ k * v₁ k 0 + ∑ k, d k * u k + q₁ with hxdef
  set y := ∑ k, c₃ k * v₃ k 2 + ∑ k, c₂ k * v₂ k 1 + q₂ with hydef
  by_contra hcon
  have hP1 := perA_ne (j := 1) (by norm_num) (by norm_num)
  have hP3 := perA_ne (j := 3) (by norm_num) (by norm_num)
  have hO := omega7_ne
  have hKalg : ∀ z ∈ KspanD zeta7 6 b, IsAlgebraic ℚ z := fun z hz => KspanD_isAlgebraic isAlgebraic_zeta7 hb.alg hz
  have hθK : ∀ h, thetaD zeta7 6 b h ∈ KspanD zeta7 6 b := fun h => Submodule.subset_span ⟨h, rfl⟩
  have hθalg : ∀ h, IsAlgebraic ℚ (thetaD zeta7 6 b h) := fun h => hKalg _ (hθK h)
  have hr : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    subst hr0
    have := hb.one_mem
    rw [KspanD, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
    exact one_ne_zero this
  set σ := β * perA 3 / perA 1 with hσdef
  have hσ : Transcendental ℚ σ := by
    intro halg
    obtain ⟨-, -, -, h3, -⟩ := hWB 0 σ 0 (-β) 0 isAlgebraic_zero halg isAlgebraic_zero (hKalg _ hβK).neg
      isAlgebraic_zero (by rw [hσdef]; field_simp; ring)
    exact hβ0 (neg_eq_zero.mp h3)
  have hx : ∀ c₀ c c' : ℂ, c₀ ∈ KspanD zeta7 6 b → c ∈ KspanD zeta7 6 b → c' ∈ KspanD zeta7 6 b →
      c₀ ≠ 0 → c₀ * x ≠ c * perA 1 + c' * omega7 := by
    intro c₀ c c' h₀ h h' hne heq
    apply hcon
    refine ⟨c * c₀⁻¹, c' * c₀⁻¹, hb.mul_mem _ h _ (hb.inv_mem _ h₀), hb.mul_mem _ h' _ (hb.inv_mem _ h₀), ?_⟩
    field_simp
    linear_combination heq
  have hAA' : ∀ c c' : ℂ, c ∈ KspanD zeta7 6 b → c' ∈ KspanD zeta7 6 b → c * perA 1 + c' * omega7 = 0 →
      c = 0 ∧ c' = 0 := by
    intro c c' h h' heq
    obtain ⟨-, h1, -, -, h4⟩ := hWB 0 c 0 0 c' isAlgebraic_zero (hKalg _ h) isAlgebraic_zero isAlgebraic_zero
      (hKalg _ h') (by linear_combination heq)
    exact ⟨h1, h4⟩
  have hωL : LogE E7 omega7 := Or.inl E7.ω₁_mem_lattice
  have hμ' := mu7'_ne
  have hμK := mu7'_mem hb
  have hR := relation_R
  -- the lifts
  refine frameX_false (mu1 b) (mu2 b) (thetaD zeta7 6 b) hb.indep (algQX7 (r := r)) (lamX7 LA) perX7 hW
    (by rw [finrank_QX7]; simp; omega) (fun q hq => mu1_alg hb hq) (fun q hq => mu2_alg hb hq)
    {q | algQX7 q} (fun q hq => hq) span_algQX7 σ hσ (perA 1) omega7 hAA'
    (fun h => aGen 0 h.1 h.2 perT + aLift (r := r) 2 5 (coordsD zeta7 6 b (thetaD zeta7 6 b h * β)) perT)
    (fun h => eLift (r := r) (coordsD zeta7 6 b (thetaD zeta7 6 b h)) omega7 +
      aLift (r := r) 1 4 (coordsD zeta7 6 b (thetaD zeta7 6 b h * (β / mu7'))) perT)
    ?_ ?_ ?_ ?_ ?_ ?_
    (fun h => ∑ k, aLift (r := r) 0 1 (coordsD zeta7 6 b (thetaD zeta7 6 b h * c₁ k)) (v₁ k) +
      ∑ k, eLift (r := r) (coordsD zeta7 6 b (thetaD zeta7 6 b h * d k)) (u k) +
      (((0 : Fin 3 → Fin 3 → Fin r → ℂ), (0 : Fin r × Fin 3 → ℂ)), thetaD zeta7 6 b h * q₁,
        thetaD zeta7 6 b h * q₂) +
      ∑ k, aLift (r := r) 2 5 (coordsD zeta7 6 b (thetaD zeta7 6 b h * c₃ k)) (v₃ k) +
      ∑ k, aLift (r := r) 1 4 (coordsD zeta7 6 b (thetaD zeta7 6 b h * c₂ k)) (v₂ k))
    x ?_ ?_ hx
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl (Or.inl ⟨0, h.1, h.2, perT, Set.mem_insert _ _, rfl⟩)))
      (aLift_mem LA 2 5 _ (Set.mem_insert _ _))
  · intro h
    exact add_mem (Submodule.subset_span (Or.inl ⟨0, h.1, h.2, rfl⟩)) (aLift_per 2 5 _)
  · intro h
    exact add_mem (eLift_mem LA _ hωL) (aLift_mem LA 1 4 _ (Set.mem_insert _ _))
  · intro h
    exact add_mem (eLift_per _) (aLift_per 1 4 _)
  · intro h
    rw [map_add, PsiX_aGen0, PsiX_aLift2, coordsD_spec (hb.mul_mem _ (hθK h) _ hβK)]
    refine Prod.ext ?_ ?_
    · simp [thetaD, perT]; ring
    · simp [perT, hσdef]; field_simp
  · intro h
    have hm : thetaD zeta7 6 b h * (β / mu7') ∈ KspanD zeta7 6 b := by
      rw [div_eq_mul_inv]; exact hb.mul_mem _ (hθK h) _ (hb.mul_mem _ hβK _ (hb.inv_mem _ hμK))
    rw [map_add, PsiX_eLift, PsiX_aLift1, coordsD_spec (hθK h), coordsD_spec hm]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, zero_add, perT, hσdef]
      norm_num
      field_simp
      linear_combination (thetaD zeta7 6 b h) * hR
  · intro h
    refine add_mem (add_mem (add_mem (add_mem
      (Submodule.sum_mem _ fun k _ => aLift_mem LA 0 1 _ (hv₁ k))
      (Submodule.sum_mem _ fun k _ => eLift_mem LA _ (hu k)))
      (Submodule.subset_span (Or.inr ⟨_, _, (hθalg h).mul hq₁, (hθalg h).mul hq₂, rfl⟩)))
      (Submodule.sum_mem _ fun k _ => aLift_mem LA 2 5 _ (hv₃ k)))
      (Submodule.sum_mem _ fun k _ => aLift_mem LA 1 4 _ (hv₂ k))
  · intro h
    have e1 : ∀ k, (∑ p, (coordsD zeta7 6 b (thetaD zeta7 6 b h * c₁ k) p : ℂ) * thetaD zeta7 6 b p) =
        thetaD zeta7 6 b h * c₁ k := fun k => coordsD_spec (hb.mul_mem _ (hθK h) _ (hc₁ k))
    have e2 : ∀ k, (∑ p, (coordsD zeta7 6 b (thetaD zeta7 6 b h * c₂ k) p : ℂ) * thetaD zeta7 6 b p) =
        thetaD zeta7 6 b h * c₂ k := fun k => coordsD_spec (hb.mul_mem _ (hθK h) _ (hc₂ k))
    have e3 : ∀ k, (∑ p, (coordsD zeta7 6 b (thetaD zeta7 6 b h * c₃ k) p : ℂ) * thetaD zeta7 6 b p) =
        thetaD zeta7 6 b h * c₃ k := fun k => coordsD_spec (hb.mul_mem _ (hθK h) _ (hc₃ k))
    have ed : ∀ k, (∑ p, (coordsD zeta7 6 b (thetaD zeta7 6 b h * d k) p : ℂ) * thetaD zeta7 6 b p) =
        thetaD zeta7 6 b h * d k := fun k => coordsD_spec (hb.mul_mem _ (hθK h) _ (hd k))
    have hga : PsiX (mu1 b) (mu2 b) ((((0 : Fin 3 → Fin 3 → Fin r → ℂ), (0 : Fin r × Fin 3 → ℂ)),
        thetaD zeta7 6 b h * q₁, thetaD zeta7 6 b h * q₂) : TX (QX7 r)) =
        (thetaD zeta7 6 b h * q₁, thetaD zeta7 6 b h * q₂) := by
      rw [PsiX_apply]
      simp only [show ((0 : Fin 3 → Fin 3 → Fin r → ℂ), (0 : Fin r × Fin 3 → ℂ)) = (0 : QX7 r) from rfl,
        map_zero, zero_add]
    simp only [map_add, map_sum, PsiX_aLift0, PsiX_aLift1, PsiX_aLift2, PsiX_eLift, hga, e1, e2, e3, ed]
    have hy : y = σ * x := by
      rw [hσdef]; field_simp; linear_combination -hrel
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Finset.sum_const_zero, add_zero]
      rw [hxdef]
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    · simp only [Prod.snd_add, Prod.snd_sum, Finset.sum_const_zero, zero_add]
      rw [show σ * (thetaD zeta7 6 b h * x) = thetaD zeta7 6 b h * y by rw [hy]; ring, hydef]
      simp only [mul_add, Finset.mul_sum, mul_assoc]
      ring

/-- **Proposition X at level seven**, with `ℚ̄` coefficients (the field `K` is chosen to contain them). -/
theorem propX7 (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (β : ℂ)
    (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0)
    {N₁ N₂ N₃ M : ℕ} (c₁ : Fin N₁ → ℂ) (v₁ : Fin N₁ → Fin 3 → ℂ) (c₂ : Fin N₂ → ℂ) (v₂ : Fin N₂ → Fin 3 → ℂ)
    (c₃ : Fin N₃ → ℂ) (v₃ : Fin N₃ → Fin 3 → ℂ) (d : Fin M → ℂ) (u : Fin M → ℂ) (q₁ q₂ : ℂ)
    (hc₁ : ∀ k, IsAlgebraic ℚ (c₁ k)) (hc₂ : ∀ k, IsAlgebraic ℚ (c₂ k))
    (hc₃ : ∀ k, IsAlgebraic ℚ (c₃ k)) (hd : ∀ k, IsAlgebraic ℚ (d k))
    (hv₁ : ∀ k, v₁ k ∈ insert perT LA) (hv₂ : ∀ k, v₂ k ∈ insert perT LA) (hv₃ : ∀ k, v₃ k ∈ insert perT LA)
    (hu : ∀ k, LogE E7 (u k)) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂)
    (hrel : (∑ k, c₁ k * v₁ k 0 + ∑ k, d k * u k + q₁) * (β * perA 3) =
      (∑ k, c₃ k * v₃ k 2 + ∑ k, c₂ k * v₂ k 1 + q₂) * perA 1) :
    ∃ c c' : ℂ, IsAlgebraic ℚ c ∧ IsAlgebraic ℚ c' ∧
      ∑ k, c₁ k * v₁ k 0 + ∑ k, d k * u k + q₁ = c * perA 1 + c' * omega7 := by
  classical
  obtain ⟨r, -, b, hb, hS⟩ := exists_adapted_basis7
    (insert β (Finset.univ.image c₁ ∪ Finset.univ.image c₂ ∪ Finset.univ.image c₃ ∪ Finset.univ.image d)) (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
      rcases hz with rfl | ((⟨k, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩) | ⟨k, rfl⟩
      exacts [hβ, hc₁ k, hc₂ k, hc₃ k, hd k])
  obtain ⟨c, c', hc, hc', heq⟩ := propX7_K (b := b) LA (hW r b hb) hb hWB β (hS β (by simp)) hβ0 c₁ v₁ c₂ v₂
    c₃ v₃ d u q₁ q₂ (fun k => hS _ (by simp)) (fun k => hS _ (by simp)) (fun k => hS _ (by simp))
    (fun k => hS _ (by simp)) hv₁ hv₂ hv₃ hu hq₁ hq₂ hrel
  exact ⟨c, c', KspanD_isAlgebraic isAlgebraic_zeta7 hb.alg hc, KspanD_isAlgebraic isAlgebraic_zeta7 hb.alg hc',
    heq⟩

/-- **Named input (Wüstholz 1989; slot splitting, paper [II] proof of Theorem X).** For logarithms of `A` (or the period
`γ`) and of `E`, a relation `z₁(v) + u + q = cP₁ + c'Ω`, resp. `z₃(v') + z₂(v) + q = cP₃ + c'P₂`, with algebraic `q, c, c'`
splits slot by slot. It is a statement about the parameter `LA` and holds when `LA` consists of eigen-coordinate triples
of logarithms of algebraic points of `A`. -/
def WuestholzX7 (LA : Set (Fin 3 → ℂ)) : Prop :=
  (∀ v ∈ insert perT LA, ∀ u : ℂ, LogE E7 u → ∀ q c c' : ℂ, IsAlgebraic ℚ q → IsAlgebraic ℚ c →
      IsAlgebraic ℚ c' → v 0 + u + q = c * perA 1 + c' * omega7 →
        q = 0 ∧ v 0 = c * perA 1 ∧ u = c' * omega7) ∧
    (∀ v ∈ insert perT LA, ∀ v' ∈ insert perT LA, ∀ q c c' : ℂ, IsAlgebraic ℚ q → IsAlgebraic ℚ c →
      IsAlgebraic ℚ c' → v' 2 + v 1 + q = c * perA 3 + c' * perA 2 →
        q = 0 ∧ v' 2 = c * perA 3 ∧ v 1 = c' * perA 2)

/-- **Theorem X7** (paper [II], `thm:X7`, first part): if `v₁, v₂, v₃` are logarithms of algebraic points of `A`
(eigen-coordinate triples in `LA`), `u ∈ 𝓛_E`, `q₁, q₂ ∈ ℚ̄`, `β ∈ ℚ̄ˣ` and
`(z₁(v₁) + u + q₁)·βP₃ = (z₃(v₃) + z₂(v₂) + q₂)·P₁`, then `q₁ = q₂ = 0`, `z_j(v_j) ∈ ℚ̄P_j` and `u ∈ ℚ̄Ω`. -/
theorem thmX7 (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (hWX : WuestholzX7 LA)
    (v₁ v₂ v₃ : Fin 3 → ℂ) (hv₁ : v₁ ∈ LA) (hv₂ : v₂ ∈ LA) (hv₃ : v₃ ∈ LA) (u : ℂ) (hu : LogE E7 u)
    (q₁ q₂ β : ℂ) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0)
    (hrel : (v₁ 0 + u + q₁) * (β * perA 3) = (v₃ 2 + v₂ 1 + q₂) * perA 1) :
    q₁ = 0 ∧ q₂ = 0 ∧ (∃ c, IsAlgebraic ℚ c ∧ v₁ 0 = c * perA 1) ∧ (∃ c, IsAlgebraic ℚ c ∧ v₂ 1 = c * perA 2) ∧
      (∃ c, IsAlgebraic ℚ c ∧ v₃ 2 = c * perA 3) ∧ (∃ c, IsAlgebraic ℚ c ∧ u = c * omega7) := by
  have hP1 := perA_ne (j := 1) (by norm_num) (by norm_num)
  have hμ' := mu7'_ne
  have hR := relation_R
  obtain ⟨c, c', hc, hc', heq⟩ := propX7 LA hW hWB β hβ hβ0 (fun _ : Fin 1 => (1 : ℂ)) (fun _ => v₁)
    (fun _ : Fin 1 => (1 : ℂ)) (fun _ => v₂) (fun _ : Fin 1 => (1 : ℂ)) (fun _ => v₃) (fun _ : Fin 1 => (1 : ℂ))
    (fun _ => u) q₁ q₂ (fun _ => isAlgebraic_one) (fun _ => isAlgebraic_one) (fun _ => isAlgebraic_one)
    (fun _ => isAlgebraic_one) (fun _ => Set.mem_insert_of_mem _ hv₁) (fun _ => Set.mem_insert_of_mem _ hv₂)
    (fun _ => Set.mem_insert_of_mem _ hv₃) (fun _ => hu) hq₁ hq₂ (by simpa using hrel)
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, one_mul] at heq
  obtain ⟨e1, e2, e3⟩ := hWX.1 v₁ (Set.mem_insert_of_mem _ hv₁) u hu q₁ c c' hq₁ hc hc' heq
  have h2 : v₃ 2 + v₂ 1 + q₂ = (c * β) * perA 3 + (c' * β / mu7') * perA 2 := by
    apply mul_right_cancel₀ hP1
    rw [← hrel, heq]
    field_simp
    linear_combination (-c') * hR
  have hcb : IsAlgebraic ℚ (c * β) := hc.mul hβ
  have hcb' : IsAlgebraic ℚ (c' * β / mu7') := by
    rw [← mem_algebraicClosure_iff]
    exact div_mem (mul_mem (mem_algebraicClosure_iff.mpr hc') (mem_algebraicClosure_iff.mpr hβ))
      (mem_algebraicClosure_iff.mpr isAlgebraic_mu7')
  obtain ⟨f1, f2, f3⟩ := hWX.2 v₂ (Set.mem_insert_of_mem _ hv₂) v₃ (Set.mem_insert_of_mem _ hv₃) q₂ _ _ hq₂ hcb
    hcb' h2
  exact ⟨e1, f1, ⟨c, hc, e2⟩, ⟨_, hcb', f3⟩, ⟨_, hcb, f2⟩, ⟨c', hc', e3⟩⟩

/-- **Corollary X7 (c)** (paper [II], `cor:X7`(c)): `1, B(2/7, 2/7), B(3/7, 3/7), B(3/7, 3/7)/B(1/7, 1/7)` are linearly
independent over `ℚ̄`. Uses only the periods (`LA = ∅`): W88 §5d for `A^{3r} × E^{3r} × G_a²` and the named input
`WuestholzBeta7`. -/
theorem x7c (hW : Thm11KappaX7 ∅) (hWB : WuestholzBeta7) (a₀ a₁ a₂ a₃ : ℂ) (h₀ : IsAlgebraic ℚ a₀)
    (h₁ : IsAlgebraic ℚ a₁) (h₂ : IsAlgebraic ℚ a₂) (h₃ : IsAlgebraic ℚ a₃)
    (hrel : a₀ + a₁ * betaIntegral (2 / 7) (2 / 7) + a₂ * betaIntegral (3 / 7) (3 / 7) +
      a₃ * (betaIntegral (3 / 7) (3 / 7) / betaIntegral (1 / 7) (1 / 7)) = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have hz1 := one_sub_zeta7_pow_ne (j := 1) (by norm_num) (by norm_num)
  have hz2 := one_sub_zeta7_pow_ne (j := 2) (by norm_num) (by norm_num)
  have hz3 := one_sub_zeta7_pow_ne (j := 3) (by norm_num) (by norm_num)
  rw [pow_one] at hz1
  have hP1 := perA_ne (j := 1) (by norm_num) (by norm_num)
  have hP3 := perA_ne (j := 3) (by norm_num) (by norm_num)
  have hμ' := mu7'_ne
  have hR := relation_R
  have hBj : ∀ j : ℕ, 0 < j → j < 7 → betaIntegral ((j : ℂ) / 7) ((j : ℂ) / 7) = perA j / (1 - zeta7 ^ j) := by
    intro j h0 h7
    have hre : 0 < ((j : ℂ) / 7).re := by simp; positivity
    rw [← betaG_eq_betaIntegral hre hre, perA, mul_comm, mul_div_assoc, div_self
      (one_sub_zeta7_pow_ne h0 h7), mul_one]
  have e1 := hBj 1 (by norm_num) (by norm_num)
  have e2 := hBj 2 (by norm_num) (by norm_num)
  have e3 := hBj 3 (by norm_num) (by norm_num)
  simp only [Nat.cast_one, Nat.cast_ofNat, pow_one] at e1 e2 e3
  rw [e1, e2, e3] at hrel
  -- the relation, multiplied by `P₁` and rewritten with `P₁P₂ = μ'P₃Ω`
  have hz := mem_algebraicClosure_iff.mpr isAlgebraic_zeta7
  have halg : ∀ z ∈ algebraicClosure ℚ ℂ, IsAlgebraic ℚ z := fun z hz => mem_algebraicClosure_iff.mp hz
  have hd1 : IsAlgebraic ℚ (a₂ / (1 - zeta7 ^ 3)) :=
    halg _ (div_mem (mem_algebraicClosure_iff.mpr h₂) (sub_mem (one_mem _) (pow_mem hz 3)))
  have hd2 : IsAlgebraic ℚ (a₁ * mu7' / (1 - zeta7 ^ 2)) :=
    halg _ (div_mem (mul_mem (mem_algebraicClosure_iff.mpr h₁) (mem_algebraicClosure_iff.mpr isAlgebraic_mu7'))
      (sub_mem (one_mem _) (pow_mem hz 2)))
  have hd3 : IsAlgebraic ℚ (a₃ * (1 - zeta7) / (1 - zeta7 ^ 3)) :=
    halg _ (div_mem (mul_mem (mem_algebraicClosure_iff.mpr h₃) (sub_mem (one_mem _) hz))
      (sub_mem (one_mem _) (pow_mem hz 3)))
  have hrel' : ((a₂ / (1 - zeta7 ^ 3)) * perT 0 + (a₁ * mu7' / (1 - zeta7 ^ 2)) * omega7 +
      a₃ * (1 - zeta7) / (1 - zeta7 ^ 3)) * (1 * perA 3) = (-a₀) * perA 1 := by
    have hrel2 := congrArg (· * perA 1) hrel
    simp only [zero_mul] at hrel2
    simp only [perT, Fin.isValue, Fin.val_zero, zero_add]
    field_simp at hrel2 ⊢
    linear_combination hrel2 - a₁ * (1 - zeta7 ^ 3) * hR
  obtain ⟨c, c', hc, hc', heq⟩ := propX7 ∅ hW hWB 1 isAlgebraic_one one_ne_zero
    (fun _ : Fin 1 => a₂ / (1 - zeta7 ^ 3)) (fun _ => perT) (fun k : Fin 0 => k.elim0) (fun k => k.elim0)
    (fun k : Fin 0 => k.elim0) (fun k => k.elim0) (fun _ : Fin 1 => a₁ * mu7' / (1 - zeta7 ^ 2))
    (fun _ => omega7) (a₃ * (1 - zeta7) / (1 - zeta7 ^ 3)) (-a₀) (fun _ => hd1) (fun k => k.elim0)
    (fun k => k.elim0) (fun _ => hd2) (fun _ => Set.mem_insert _ _) (fun k => k.elim0) (fun k => k.elim0)
    (fun _ => Or.inl E7.ω₁_mem_lattice) hd3 h₀.neg (by simpa using hrel')
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton] at heq
  simp only [perT, Fin.isValue, Fin.val_zero, zero_add] at heq
  obtain ⟨k0, k1, -, -, k4⟩ := hWB (a₃ * (1 - zeta7) / (1 - zeta7 ^ 3)) (a₂ / (1 - zeta7 ^ 3) - c) 0 0
    (a₁ * mu7' / (1 - zeta7 ^ 2) - c') hd3 (hd1.sub hc) isAlgebraic_zero isAlgebraic_zero (hd2.sub hc')
    (by linear_combination heq)
  -- the second coordinate: `−a₀μ' = cμ'P₃ + c'P₂`
  have hy : -(a₀ * mu7') + (-c') * perA 2 + (-(c * mu7')) * perA 3 = 0 := by
    apply mul_right_cancel₀ hP1
    have := hrel'
    rw [one_mul] at this
    simp only [perT, Fin.isValue, Fin.val_zero, zero_add] at this
    linear_combination mu7' * (-this + perA 3 * heq) - c' * hR
  obtain ⟨y0, -, y2, y3, -⟩ := hWB (-(a₀ * mu7')) 0 (-c') (-(c * mu7')) 0 (h₀.mul isAlgebraic_mu7').neg
    isAlgebraic_zero hc'.neg (hc.mul isAlgebraic_mu7').neg isAlgebraic_zero (by linear_combination hy)
  have hc0 : c = 0 := (mul_eq_zero.mp (neg_eq_zero.mp y3)).resolve_right hμ'
  have hc'0 : c' = 0 := neg_eq_zero.mp y2
  have ha0 : a₀ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp y0)).resolve_right hμ'
  subst hc0 hc'0
  rw [sub_zero] at k1 k4
  refine ⟨ha0, ?_, ?_, ?_⟩
  · rcases div_eq_zero_iff.mp k4 with h | h
    · exact (mul_eq_zero.mp h).resolve_right hμ'
    · exact absurd h hz2
  · rcases div_eq_zero_iff.mp k1 with h | h
    · exact h
    · exact absurd h hz3
  · rcases div_eq_zero_iff.mp k0 with h | h
    · exact (mul_eq_zero.mp h).resolve_right hz1
    · exact absurd h hz3

end CM4E.AbVar
