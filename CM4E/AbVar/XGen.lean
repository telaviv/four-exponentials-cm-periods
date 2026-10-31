/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.Basis
import CM4E.AbVar.FrameX

/-!
# Theorem X in generic form: the W88 step (paper [II], §`sec:X`, proof of Proposition `prop:X`)

**Data.** A simple CM abelian variety `A` (CM field `F = ℚ(α)`, `[F : ℚ] = 2g`, CM type `σ_0, …, σ_{g−1}`) is recorded by
`CMAV`: its eigen-coordinates `z_s` (`s < g`), the conjugates `κ_s = σ_s(α)` (so `z_s([α^e]v) = κ_s^e z_s(v)`), the
periods `P_s = z_s(γ)` of one cycle `γ`, and a parameter set `LA` of eigen-coordinate vectors of logarithms of algebraic
points (Lean has no abelian varieties). A first-kind slot (`FKSlot`) is such an `A` with one `s`; its slot period is
`P_s` and its slot field `σ_s(F) = ℚ(κ_s)`. Four slots `a, b, c, d` are indexed `0, 1, 2, 3`.

**The group.** For each slot `j` and a `ℚ(κ_{s_j})`-basis `b_j` of one number field `K` (`IsAdaptedX`: every
`θ_j(i, e) = κ_{s_j}^e b_j i` is a `ℚ`-basis of the same `K`), the paper's `G'' = G^n/U = A'' × G_a²` is replaced by the
group `∏_j A_j^{r_j} × G_a²`, one block of `r_j = n/[F_j : ℚ]` copies of `A_j` per slot (as for level seven,
`CM4E/AbVar/X7.lean`; it has the same dimension `2n + 2` as `G''`). The slot form of slot `j` is
`Σ_i b_j i · z_{s_j}(copy i of block j)`, and `Ψ'' = (μ₁ + q₁, μ₂ + q₂)` with `μ₁ = slot a + slot d`,
`μ₂ = slot c + slot b` (frame `CM4E/AbVar/FrameX.lean`). Logarithms: `[α^e]v` in each copy (`v ∈ LA ∪ {γ}`); periods:
`[α^e]γ`; and algebraic vectors of `G_a²`.

Soundness of `gmXA S b` (not checked by Lean; `reviews/REFEREE_HYP_XA.md`): the four slots are pairwise distinct
(slots on one `A` have distinct `s`, and slots on isogenous varieties are given on the same `A`); `∏_j A_j^{r_j} × G_a²`
is an algebraic group over `ℚ̄`; `[α^e]` acts on `z_s` by `κ_s^e`; connected subgroups are products (P); by (S1) a
nonzero abelian subvariety of `∏_j A_j^{r_j}` is `B_S`, `S ⊂ ∏_j F_j^{r_j}` (mixing only blocks of isogenous slots),
with independent tangent directions for distinct embeddings; its slot form in block `j` is `Σ_i b_j i σ_{s_j}(m_i)`,
which vanishes for all `m ∈ S` only if the block-`j` part of `S` is `0` (`b_j` is `σ_{s_j}(F_j)`-independent); so a
nonzero connected subgroup has an algebraic tangent vector with `Ψ'' ≠ 0` (the uniform condition), using that the
slots are distinct.

`propXA_K`: the `K`-form of Proposition X for this group (one vector; the data of slot `j` are `K`-combinations of
`z_{s_j}` of logarithms in `LA_j ∪ {γ_j}`).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

/-- A simple CM abelian variety in eigen-coordinates: dimension `g`, conjugates `κ_s = σ_s(α)` of a primitive element
`α` of its CM field, periods `P_s = z_s(γ)` of one cycle, and a parameter set `LA` of logarithms (eigen-coordinate
vectors of logarithms of algebraic points). -/
structure CMAV where
  g : ℕ
  κ : Fin g → ℂ
  P : Fin g → ℂ
  LA : Set (Fin g → ℂ)

/-- A first-kind slot `(A, σ_s)`. -/
structure FKSlot where
  A : CMAV
  s : Fin A.g

namespace FKSlot

/-- The generator `κ_s = σ_s(α)` of the slot field `σ_s(F)`. -/
def α (S : FKSlot) : ℂ := S.A.κ S.s

/-- The slot period `P_s = z_s(γ)`. -/
def per (S : FKSlot) : ℂ := S.A.P S.s

/-- `[F : ℚ]`, the degree of `κ_s`. -/
noncomputable def d (S : FKSlot) : ℕ := (minpoly ℚ S.α).natDegree

end FKSlot

variable (S : Fin 4 → FKSlot) {r : Fin 4 → ℕ} (b : (j : Fin 4) → Fin (r j) → ℂ)

/-- `T(∏_j A_j^{r_j})`: block `j`, copy `i`, eigen-coordinate `s`. -/
abbrev QA (S : Fin 4 → FKSlot) (r : Fin 4 → ℕ) := (j : Fin 4) → Fin (r j) → Fin (S j).A.g → ℂ

/-- The slot form of slot `j`: `Σ_i b_j i · z_{s_j}(copy i of block j)`. -/
noncomputable def slotForm (j : Fin 4) : QA S r →ₗ[ℂ] ℂ where
  toFun q := ∑ i, b j i * q j i (S j).s
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- `μ₁ = slot a + slot d`. -/
noncomputable def muA1 : QA S r →ₗ[ℂ] ℂ := slotForm S b 0 + slotForm S b 3

/-- `μ₂ = slot c + slot b`. -/
noncomputable def muA2 : QA S r →ₗ[ℂ] ℂ := slotForm S b 2 + slotForm S b 1

/-- `[α^e]v` in copy `i` of block `j`. -/
noncomputable def genA (j : Fin 4) (i : Fin (r j)) (e : ℕ) (v : Fin (S j).A.g → ℂ) : TX (QA S r) :=
  (Pi.single (M := fun j => Fin (r j) → Fin (S j).A.g → ℂ) j
    (fun i' s => if i' = i then (S j).A.κ s ^ e * v s else 0), 0, 0)

/-- Generators of the logarithms. -/
def lamXA : Set (TX (QA S r)) :=
  {x | ∃ j i e, ∃ v ∈ insert (S j).A.P (S j).A.LA, x = genA S j i e v} ∪
    {x | ∃ c₁ c₂ : ℂ, IsAlgebraic ℚ c₁ ∧ IsAlgebraic ℚ c₂ ∧ x = (0, c₁, c₂)}

/-- Generators of the periods. -/
noncomputable def perXA : Set (TX (QA S r)) := {x | ∃ j i e, x = genA S j i e (S j).A.P}

/-- The `ℚ̄`-structure. -/
def algQA (q : QA S r) : Prop := ∀ j i s, IsAlgebraic ℚ (q j i s)

/-- **The model of `∏_j A_j^{r_j} × G_a²`.** -/
noncomputable def gmXA : GroupModel (TX (QA S r)) :=
  gmFX (algQA S (r := r)) (lamXA S) (perXA S) (muA1 S b) (muA2 S b)

/-- The four slot bases are adapted to one number field `K = span_ℚ θ_a`. -/
structure IsAdaptedX : Prop where
  basis : ∀ j, IsAdaptedBasisD (S j).α (S j).d (b j)
  span : ∀ j, KspanD (S j).α (S j).d (b j) = KspanD (S 0).α (S 0).d (b 0)

/-- **The hypothesis for Theorem X (generic)**: W88 §5d for `∏_j A_j^{r_j} × G_a²`, for all adapted slot bases. Claimed
(sound, `reviews/REFEREE_HYP_XA.md`) when: each record is faithful (`A` a simple CM abelian variety over `ℚ̄` of primitive
type, `κ_s = σ_s(α)` for a primitive element `α` of its CM field, `P` the eigen-coordinate vector of one nonzero cycle,
`LA` eigen-coordinate vectors of logarithms of algebraic points, coherent in one `ℚ̄`-model); and the four slots are
pairwise distinct, where two slots are equal iff their varieties are isogenous and their embeddings correspond (so slots
given on one record need different `s`). For non-distinct slots the model is unsound, but then `WuestholzXA` is false. -/
def Thm11KappaXA : Prop :=
  ∀ (r : Fin 4 → ℕ) (b : (j : Fin 4) → Fin (r j) → ℂ), IsAdaptedX S b → HyperplaneKappa (gmXA S b)

/-- **Named input (Wüstholz 1989; paper [II], (W)).** `1, P_a, P_b, P_c, P_d` are `ℚ̄`-linearly independent, for
distinct first-kind slots of simple CM abelian varieties over `ℚ̄` (two slots are equal iff the varieties are isogenous
and the embeddings correspond); `reviews/REFEREE_INPUTS_XA.md`. -/
def WuestholzXA : Prop :=
  ∀ a₀ a₁ a₂ a₃ a₄ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → IsAlgebraic ℚ a₃ →
    IsAlgebraic ℚ a₄ → a₀ + a₁ * (S 0).per + a₂ * (S 1).per + a₃ * (S 2).per + a₄ * (S 3).per = 0 →
      a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0

/-! ## Values of `Ψ''` on generators and lifts -/

/-- Which target coordinate a slot feeds: `a, d ↦ (x, 0)`, `b, c ↦ (0, x)`. -/
noncomputable def tgt (j : Fin 4) : ℂ →ₗ[ℂ] ℂ × ℂ :=
  if j = 0 ∨ j = 3 then LinearMap.inl ℂ ℂ ℂ else LinearMap.inr ℂ ℂ ℂ

variable {S b}

lemma PsiX_genA (j : Fin 4) (i : Fin (r j)) (e : ℕ) (v : Fin (S j).A.g → ℂ) :
    PsiX (muA1 S b) (muA2 S b) (genA S j i e v) = tgt j (b j i * ((S j).α ^ e * v (S j).s)) := by
  rw [PsiX_apply]
  fin_cases j <;>
    simp [genA, muA1, muA2, slotForm, tgt, FKSlot.α, Finset.sum_ite_eq']

lemma PsiX_rsmul {Q : Type} [AddCommGroup Q] [Module ℂ Q] [Module ℚ Q] (μ₁ μ₂ : Q →ₗ[ℂ] ℂ) (c : ℚ)
    (v : TX Q) : PsiX μ₁ μ₂ (c • v) = c • PsiX μ₁ μ₂ v := map_rat_smul _ _ _

variable (S b)

/-- A lift in block `j`: `Σ_p m_p [α^{e_p}]v` in copy `i_p`. -/
noncomputable def liftA (j : Fin 4) (m : Fin (r j) × Fin (S j).d → ℚ) (v : Fin (S j).A.g → ℂ) : TX (QA S r) :=
  ∑ p, m p • genA S j p.1 (p.2 : ℕ) v

variable {S b}

lemma PsiX_liftA (j : Fin 4) (m : Fin (r j) × Fin (S j).d → ℚ) (v : Fin (S j).A.g → ℂ) :
    PsiX (muA1 S b) (muA2 S b) (liftA S j m v) =
      tgt j ((∑ p, (m p : ℂ) * thetaD (S j).α (S j).d (b j) p) * v (S j).s) := by
  simp only [liftA, map_sum, PsiX_rsmul, PsiX_genA, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← map_rat_smul, Rat.smul_def, thetaD]
  congr 1
  ring

lemma liftA_mem (j : Fin 4) (m : Fin (r j) × Fin (S j).d → ℚ) {v : Fin (S j).A.g → ℂ}
    (hv : v ∈ insert (S j).A.P (S j).A.LA) : liftA S j m v ∈ Submodule.span ℚ (lamXA S (r := r)) :=
  Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨j, p.1, _, v, hv, rfl⟩))

lemma liftA_per (j : Fin 4) (m : Fin (r j) × Fin (S j).d → ℚ) :
    liftA S j m (S j).A.P ∈ Submodule.span ℚ (perXA S (r := r)) :=
  Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, p.1, _, rfl⟩)

/-! ## The ingredients of the frame contradiction -/

lemma alpha_alg_of_adapted {α : ℂ} {r' : ℕ} {b' : Fin r' → ℂ}
    (hb : IsAdaptedBasisD α (minpoly ℚ α).natDegree b') : IsAlgebraic ℚ α := by
  by_contra h
  have h0 : (minpoly ℚ α).natDegree = 0 := by
    rw [minpoly.eq_zero (fun hi => h hi.isAlgebraic)]; simp
  have := hb.one_mem
  rw [KspanD] at this
  have hemp : Set.range (thetaD α (minpoly ℚ α).natDegree b') = ∅ := by
    rw [Set.range_eq_empty_iff]
    constructor
    rintro ⟨_, e⟩
    exact (Fin.cast h0 e).elim0
  rw [hemp, Submodule.span_empty, Submodule.mem_bot] at this
  exact one_ne_zero this

variable (S) in
/-- The elementary vector of `QA`. -/
noncomputable def eA (j : Fin 4) (i : Fin (r j)) (s : Fin (S j).A.g) : QA S r :=
  Pi.single (M := fun j => Fin (r j) → Fin (S j).A.g → ℂ) j (fun i' s' => if i' = i ∧ s' = s then (1 : ℂ) else 0)

lemma span_algQA : Submodule.span ℂ {q : QA S r | algQA S q} = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  have hq : q = ∑ j, ∑ i, ∑ s, q j i s • eA S j i s := by
    funext j' i' s'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j']
    · simp [eA, ite_and]
    · intro j _ hj
      simp [eA, Pi.single_eq_of_ne' hj]
    · simp
  rw [hq]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun s _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  intro j' i' s'
  by_cases h : j' = j
  · subst h
    simp only [eA, Pi.single_eq_same]
    split_ifs
    exacts [isAlgebraic_one, isAlgebraic_zero]
  · simp [eA, Pi.single_eq_of_ne h, isAlgebraic_zero]

lemma slotForm_alg (hb : IsAdaptedX S b) (j : Fin 4) {q : QA S r} (hq : algQA S q) :
    IsAlgebraic ℚ (slotForm S b j q) := by
  show IsAlgebraic ℚ (∑ i, b j i * q j i (S j).s)
  rw [← mem_algebraicClosure_iff]
  exact sum_mem fun i _ => mul_mem (mem_algebraicClosure_iff.mpr ((hb.basis j).alg i))
    (mem_algebraicClosure_iff.mpr (hq _ _ _))

lemma finrank_QA : finrank ℂ (QA S r) = ∑ j, r j * (S j).A.g := by
  simp [QA, Module.finrank_pi_fintype]

lemma card_eq_of_adapted (hb : IsAdaptedX S b) (j : Fin 4) : r j * (S j).d = r 0 * (S 0).d := by
  have h1 := finrank_span_eq_card (hb.basis j).indep
  have h0 := finrank_span_eq_card (hb.basis 0).indep
  rw [← KspanD, hb.span j] at h1
  rw [← KspanD] at h0
  simp only [Fintype.card_prod, Fintype.card_fin] at h0 h1
  omega

variable (S) in
/-- The data value of slot `j`: `Σ_k c_k z_{s_j}(v_k)`. -/
def slotVal {N : Fin 4 → ℕ} (c : (j : Fin 4) → Fin (N j) → ℂ)
    (v : (j : Fin 4) → Fin (N j) → Fin (S j).A.g → ℂ) (j : Fin 4) : ℂ :=
  ∑ k, c j k * v j k (S j).s

/-- **Proposition X, `K`-form, generic** (one vector): for slot bases adapted to `K`, `μ, β ∈ K`, the relation
`P_aP_b = μP_cP_d`, data `x = X_a + X_d + q₁`, `y = X_c + X_b + q₂` (`X_j` a `K`-combination of `z_{s_j}` of
logarithms of `A_j` or of `γ_j`, `q_i ∈ ℚ̄`) with `x·βP_c = y·P_a`, one has `x ∈ K P_a + K P_d`. -/
theorem propXA_K (hb : IsAdaptedX S b) (hW : HyperplaneKappa (gmXA S b))
    (hg : ∀ j, 2 * (S j).A.g ≤ (S j).d) (hn : 5 ≤ r 0 * (S 0).d) (hWB : WuestholzXA S)
    (μ : ℂ) (hμK : μ ∈ KspanD (S 0).α (S 0).d (b 0)) (hμ0 : μ ≠ 0)
    (hR : (S 0).per * (S 1).per = μ * (S 2).per * (S 3).per)
    (β : ℂ) (hβK : β ∈ KspanD (S 0).α (S 0).d (b 0)) (hβ0 : β ≠ 0)
    {N : Fin 4 → ℕ} (c : (j : Fin 4) → Fin (N j) → ℂ) (v : (j : Fin 4) → Fin (N j) → Fin (S j).A.g → ℂ)
    (hc : ∀ j k, c j k ∈ KspanD (S 0).α (S 0).d (b 0)) (hv : ∀ j k, v j k ∈ insert (S j).A.P (S j).A.LA)
    (q₁ q₂ : ℂ) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂)
    (hrel : (slotVal S c v 0 + slotVal S c v 3 + q₁) * (β * (S 2).per) =
      (slotVal S c v 2 + slotVal S c v 1 + q₂) * (S 0).per) :
    ∃ x y : ℂ, x ∈ KspanD (S 0).α (S 0).d (b 0) ∧ y ∈ KspanD (S 0).α (S 0).d (b 0) ∧
      slotVal S c v 0 + slotVal S c v 3 + q₁ = x * (S 0).per + y * (S 3).per := by
  set K := KspanD (S 0).α (S 0).d (b 0) with hKdef
  set θ := thetaD (S 0).α (S 0).d (b 0) with hθdef
  set X := slotVal S c v 0 + slotVal S c v 3 + q₁ with hXdef
  set Y := slotVal S c v 2 + slotVal S c v 1 + q₂ with hYdef
  by_contra hcon
  have hb0 := hb.basis 0
  have hKalg : ∀ z ∈ K, IsAlgebraic ℚ z := fun z hz =>
    KspanD_isAlgebraic (alpha_alg_of_adapted hb0) hb0.alg hz
  have hθK : ∀ h, θ h ∈ K := fun h => Submodule.subset_span ⟨h, rfl⟩
  have hθalg : ∀ h, IsAlgebraic ℚ (θ h) := fun h => hKalg _ (hθK h)
  have hKj : ∀ j, KspanD (S j).α (S j).d (b j) = K := hb.span
  have hco : ∀ j {z : ℂ}, z ∈ K →
      ∑ p, (coordsD (S j).α (S j).d (b j) z p : ℂ) * thetaD (S j).α (S j).d (b j) p = z := by
    intro j z hz
    exact coordsD_spec (by rw [hKj j]; exact hz)
  have hPa : (S 0).per ≠ 0 := by
    intro h0
    obtain ⟨-, h1, -⟩ := hWB 0 1 0 0 0 isAlgebraic_zero isAlgebraic_one isAlgebraic_zero isAlgebraic_zero
      isAlgebraic_zero (by rw [h0]; ring)
    exact one_ne_zero h1
  set σ := β * (S 2).per / (S 0).per with hσdef
  have hσ : Transcendental ℚ σ := by
    intro halg
    obtain ⟨-, -, -, h3, -⟩ := hWB 0 σ 0 (-β) 0 isAlgebraic_zero halg isAlgebraic_zero (hKalg _ hβK).neg
      isAlgebraic_zero (by rw [hσdef]; field_simp; ring)
    exact hβ0 (neg_eq_zero.mp h3)
  have hx : ∀ c₀ c' c'' : ℂ, c₀ ∈ Submodule.span ℚ (Set.range θ) → c' ∈ Submodule.span ℚ (Set.range θ) →
      c'' ∈ Submodule.span ℚ (Set.range θ) → c₀ ≠ 0 → c₀ * X ≠ c' * (S 0).per + c'' * (S 3).per := by
    intro c₀ c' c'' h₀ h h' hne heq
    apply hcon
    refine ⟨c' * c₀⁻¹, c'' * c₀⁻¹, hb0.mul_mem _ h _ (hb0.inv_mem _ h₀), hb0.mul_mem _ h' _ (hb0.inv_mem _ h₀), ?_⟩
    field_simp
    linear_combination heq
  have hAA' : ∀ c' c'' : ℂ, c' ∈ Submodule.span ℚ (Set.range θ) → c'' ∈ Submodule.span ℚ (Set.range θ) →
      c' * (S 0).per + c'' * (S 3).per = 0 → c' = 0 ∧ c'' = 0 := by
    intro c' c'' h h' heq
    obtain ⟨-, h1, -, -, h4⟩ := hWB 0 c' 0 0 c'' isAlgebraic_zero (hKalg _ h) isAlgebraic_zero isAlgebraic_zero
      (hKalg _ h') (by linear_combination heq)
    exact ⟨h1, h4⟩
  have hβμK : β / μ ∈ K := by
    rw [div_eq_mul_inv]; exact hb0.mul_mem _ hβK _ (hb0.inv_mem _ hμK)
  have hcount : 2 * finrank ℂ (QA S r) + 4 < 5 * Fintype.card (Fin (r 0) × Fin (S 0).d) := by
    rw [finrank_QA, Fin.sum_univ_four]
    simp only [Fintype.card_prod, Fintype.card_fin]
    have e1 := card_eq_of_adapted hb 1
    have e2 := card_eq_of_adapted hb 2
    have e3 := card_eq_of_adapted hb 3
    have g0 := Nat.mul_le_mul_left (r 0) (hg 0)
    have g1 := Nat.mul_le_mul_left (r 1) (hg 1)
    have g2 := Nat.mul_le_mul_left (r 2) (hg 2)
    have g3 := Nat.mul_le_mul_left (r 3) (hg 3)
    nlinarith
  refine frameX_false (muA1 S b) (muA2 S b) θ hb0.indep (algQA S) (lamXA S) (perXA S) hW hcount
    (fun q hq => (slotForm_alg hb 0 hq).add (slotForm_alg hb 3 hq))
    (fun q hq => (slotForm_alg hb 2 hq).add (slotForm_alg hb 1 hq))
    {q | algQA S q} (fun q hq => hq) span_algQA σ hσ (S 0).per (S 3).per hAA'
    (fun h => liftA S 0 (coordsD (S 0).α (S 0).d (b 0) (θ h)) (S 0).A.P +
      liftA S 2 (coordsD (S 2).α (S 2).d (b 2) (θ h * β)) (S 2).A.P)
    (fun h => liftA S 3 (coordsD (S 3).α (S 3).d (b 3) (θ h)) (S 3).A.P +
      liftA S 1 (coordsD (S 1).α (S 1).d (b 1) (θ h * (β / μ))) (S 1).A.P)
    ?_ ?_ ?_ ?_ ?_ ?_
    (fun h => ∑ j, ∑ k, liftA S j (coordsD (S j).α (S j).d (b j) (θ h * c j k)) (v j k) +
      ((0 : QA S r), θ h * q₁, θ h * q₂))
    X ?_ ?_ hx
  · intro h
    exact add_mem (liftA_mem 0 _ (Set.mem_insert _ _)) (liftA_mem 2 _ (Set.mem_insert _ _))
  · intro h
    exact add_mem (liftA_per 0 _) (liftA_per 2 _)
  · intro h
    exact add_mem (liftA_mem 3 _ (Set.mem_insert _ _)) (liftA_mem 1 _ (Set.mem_insert _ _))
  · intro h
    exact add_mem (liftA_per 3 _) (liftA_per 1 _)
  · intro h
    rw [map_add, PsiX_liftA, PsiX_liftA, hco 0 (hθK h), hco 2 (hb0.mul_mem _ (hθK h) _ hβK)]
    refine Prod.ext ?_ ?_
    · simp [tgt, FKSlot.per]
    · have hPa' : (S 0).A.P (S 0).s ≠ 0 := hPa
      simp [tgt, FKSlot.per, hσdef]
      field_simp
  · intro h
    rw [map_add, PsiX_liftA, PsiX_liftA, hco 3 (hθK h), hco 1 (hb0.mul_mem _ (hθK h) _ hβμK)]
    refine Prod.ext ?_ ?_
    · simp [tgt, FKSlot.per]
    · have hPa' : (S 0).A.P (S 0).s ≠ 0 := hPa
      simp only [FKSlot.per] at hR
      simp only [tgt, hσdef, FKSlot.per]
      simp
      field_simp
      linear_combination (θ h) * hR
  · intro h
    refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => liftA_mem j _ (hv j k))
      (Submodule.subset_span (Or.inr ⟨_, _, (hθalg h).mul hq₁, (hθalg h).mul hq₂, rfl⟩))
  · intro h
    have hy : Y = σ * X := by
      rw [hσdef]; field_simp; linear_combination -hrel
    have hga : PsiX (muA1 S b) (muA2 S b) (((0 : QA S r), θ h * q₁, θ h * q₂) : TX (QA S r)) =
        (θ h * q₁, θ h * q₂) := by
      rw [PsiX_apply]; simp
    simp only [map_add, map_sum, PsiX_liftA, hga]
    simp only [fun j k => hco j (hb0.mul_mem _ (hθK h) _ (hc j k))]
    simp only [Fin.sum_univ_four, tgt]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum]
      simp [hXdef, slotVal, Finset.mul_sum, mul_add, mul_assoc]
    · simp only [Prod.snd_add, Prod.snd_sum]
      rw [show σ * (θ h * X) = θ h * Y by rw [hy]; ring, hYdef]
      simp [slotVal, Finset.mul_sum, mul_add, mul_assoc]
      ring

end CM4E.AbVar
