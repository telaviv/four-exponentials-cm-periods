/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.XThm

/-!
# Theorem X7 as an instance of the generic Theorem X

The set-up of `CM4E/AbVar/X7.lean` as an `XSetup`: two isogeny classes, `A = Jac(y⁷ = x(1 − x))` (CM by `ℚ(ζ)`,
conjugates `κ_s = ζ^{s+1}`, periods `perT`, logarithms `LA`) and `E` (CM by `ℚ(α)`, `α = (−1 + √−7)/2`, period `Ω`,
logarithms `{u : LogE E7 u}`); slots `a, b, c = z₁, z₂, z₃` on `A`, `d` on `E`. The first-kind relation is
`relation_R` (`P₁P₂ = μ'P₃Ω`, proved). `thmX7_of_gen` derives the conclusion of `thmX7` from `thmXA`; this checks that
the generic statement specialises to the level-seven one. The record `E7AV` is faithful (a curve over `ℚ̄`) by
Chowla–Selberg at `−7` (`ChowlaSelberg7`), a soundness condition of `Thm11KappaXA (X7S LA).slot`.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen Polynomial

namespace CM4E.AbVar

/-- `A = Jac(y⁷ = x(1 − x))` with logarithms `LA`. -/
noncomputable def A7 (LA : Set (Fin 3 → ℂ)) : CMAV := ⟨3, fun s => zeta7 ^ ((s : ℕ) + 1), perT, LA⟩

/-- `E` with CM by `ℚ(√−7)`, period `Ω`, logarithms `𝓛_E`. -/
noncomputable def E7AV : CMAV := ⟨1, fun _ => alpha7, fun _ => omega7, {w | LogE E7 (w 0)}⟩

/-- The set-up of Theorem X7. -/
noncomputable def X7S (LA : Set (Fin 3 → ℂ)) : XSetup where
  m := 2
  AV := ![A7 LA, E7AV]
  cls := ![0, 0, 0, 1]
  sl := fun j => match j with
    | 0 => (0 : Fin 3)
    | 1 => (1 : Fin 3)
    | 2 => (2 : Fin 3)
    | 3 => (0 : Fin 1)

lemma minpoly_zeta7_pow {k : ℕ} (hk0 : 0 < k) (hk : k < 7) : minpoly ℚ (zeta7 ^ k) = cyclotomic 7 ℚ := by
  have hp : IsPrimitiveRoot (zeta7 ^ k) 7 := zeta7_prim.pow_of_coprime k
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (Nat.not_dvd_of_pos_of_lt hk0 hk)))
  exact (cyclotomic_eq_minpoly_rat hp (by norm_num)).symm

lemma A7_good (LA : Set (Fin 3 → ℂ)) : (A7 LA).Good where
  alg s := isAlgebraic_zeta7.pow _
  inj s s' h := by
    have hs : (s : ℕ) < 3 := s.2
    have hs' : (s' : ℕ) < 3 := s'.2
    have := zeta7_prim.pow_inj (by omega : (s : ℕ) + 1 < 7) (by omega : (s' : ℕ) + 1 < 7) h
    exact Fin.ext (by omega)
  conj s s' := by
    have hs : (s : ℕ) < 3 := s.2
    have hs' : (s' : ℕ) < 3 := s'.2
    show aeval (zeta7 ^ ((s : ℕ) + 1)) (minpoly ℚ (zeta7 ^ ((s' : ℕ) + 1))) = 0
    rw [minpoly_zeta7_pow (by omega) (by omega), ← minpoly_zeta7_pow (k := (s : ℕ) + 1) (by omega) (by omega)]
    exact minpoly.aeval _ _
  cm s := by
    have hs : (s : ℕ) < 3 := s.2
    show 2 * 3 ≤ (minpoly ℚ (zeta7 ^ ((s : ℕ) + 1))).natDegree
    rw [minpoly_zeta7_pow (by omega) (by omega), natDegree_cyclotomic]
    decide

lemma natDegree_minpoly_alpha7 : 2 ≤ (minpoly ℚ alpha7).natDegree := by
  have hi := isAlgebraic_alpha7.isIntegral
  have h1 := minpoly.natDegree_pos hi
  by_contra h
  have h1' : (minpoly ℚ alpha7).natDegree = 1 := by omega
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1'
  have := congrArg Complex.im hq
  simp at this
  exact alpha7_im_ne this.symm

lemma E7AV_good : E7AV.Good where
  alg _ := isAlgebraic_alpha7
  inj s s' _ := by
    have hs : (s : ℕ) < 1 := s.2
    have hs' : (s' : ℕ) < 1 := s'.2
    exact Fin.ext (by omega)
  conj _ _ := minpoly.aeval _ _
  cm _ := by
    show 2 * 1 ≤ (minpoly ℚ alpha7).natDegree
    have := natDegree_minpoly_alpha7
    omega

lemma X7S_good (LA : Set (Fin 3 → ℂ)) : ∀ i, ((X7S LA).AV i).Good := by
  intro i
  fin_cases i
  exacts [A7_good LA, E7AV_good]

lemma wuestholzXA_X7 (LA : Set (Fin 3 → ℂ)) (hWB : WuestholzBeta7) : WuestholzXA (X7S LA).slot := by
  intro a₀ a₁ a₂ a₃ a₄ h₀ h₁ h₂ h₃ h₄ hrel
  exact hWB a₀ a₁ a₂ a₃ a₄ h₀ h₁ h₂ h₃ h₄ hrel

/-- A point of `T(A × E)`. -/
noncomputable def mk7 (LA : Set (Fin 3 → ℂ)) (w : Fin 3 → ℂ) (u : ℂ) : (X7S LA).LieG :=
  fun i => Fin.cases (motive := fun i => Fin ((X7S LA).AV i).g → ℂ) w (fun _ _ => u) i

/-- **Theorem X7 from the generic Theorem X** (same conclusion as `thmX7`): with W88 for the generic block groups of
the level-seven slots, the named inputs `WuestholzBeta7` and `WuestholzSplitXA`, and `relation_R` for (R). -/
theorem thmX7_of_gen (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaXA (X7S LA).slot) (hWB : WuestholzBeta7)
    (hSp : WuestholzSplitXA (X7S LA).slot)
    (v₁ v₂ v₃ : Fin 3 → ℂ) (hv₁ : v₁ ∈ LA) (hv₂ : v₂ ∈ LA) (hv₃ : v₃ ∈ LA) (u : ℂ) (hu : LogE E7 u)
    (q₁ q₂ β : ℂ) (hq₁ : IsAlgebraic ℚ q₁) (hq₂ : IsAlgebraic ℚ q₂) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0)
    (hrel : (v₁ 0 + u + q₁) * (β * perA 3) = (v₃ 2 + v₂ 1 + q₂) * perA 1) :
    q₁ = 0 ∧ q₂ = 0 ∧ (∃ c, IsAlgebraic ℚ c ∧ v₁ 0 = c * perA 1) ∧ (∃ c, IsAlgebraic ℚ c ∧ v₂ 1 = c * perA 2) ∧
      (∃ c, IsAlgebraic ℚ c ∧ v₃ 2 = c * perA 3) ∧ (∃ c, IsAlgebraic ℚ c ∧ u = c * omega7) := by
  set X := X7S LA
  set v : (j : Fin 4) → Fin 1 → X.LieG := fun j _ => mk7 LA (![v₁, v₂, v₃, 0] j) u with hvdef
  have hd : ∀ j, X.dataVal (fun _ _ => 1) v j = ![v₁ 0, v₂ 1, v₃ 2, u] j := by
    intro j
    fin_cases j <;> simp only [XSetup.dataVal, Fin.sum_univ_one, one_mul] <;> rfl
  obtain ⟨f1, f2, hj⟩ := X.thmXA (X7S_good LA) hW (wuestholzXA_X7 LA hWB) hSp mu7'
    isAlgebraic_mu7' mu7'_ne relation_R β hβ hβ0 (fun _ _ => 1) v (fun _ _ => isAlgebraic_one)
    (fun j _ => by
      fin_cases j
      · exact Set.mem_insert_of_mem _ hv₁
      · exact Set.mem_insert_of_mem _ hv₂
      · exact Set.mem_insert_of_mem _ hv₃
      · exact Set.mem_insert_of_mem _ (show LogE E7 u from hu))
    q₁ q₂ hq₁ hq₂ (by simp only [hd]; exact hrel)
  obtain ⟨a0, ha0, e0⟩ := hj 0
  obtain ⟨a1, ha1, e1⟩ := hj 1
  obtain ⟨a2, ha2, e2⟩ := hj 2
  obtain ⟨a3, ha3, e3⟩ := hj 3
  rw [hd] at e0 e1 e2 e3
  exact ⟨f1, f2, ⟨a0, ha0, e0⟩, ⟨a1, ha1, e1⟩, ⟨a2, ha2, e2⟩, ⟨a3, ha3, e3⟩⟩

end CM4E.AbVar
