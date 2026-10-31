/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.AbVar.MGAK
import CM4E.Gen.MG13
import CM4E.Gen.ThmMCor

/-!
# Corollary A2 (paper [II], `cor:A2`)

For a first-kind eigen-period `P` of a simple CM abelian variety and `a, b, c ∈ ℚ̄ˣ`, at least one of `e^{aπ²}`,
`e^{bπP}`, `e^{cπ²/P}` is transcendental (`corA2`). The paper's proof: Theorem MG-A (`K`-form, `mgA_K` with `LA = ∅` and
constant `1`) at `s = P/π` with data `x₁ = π²`, `x₂ = π²/P` (`sx₁ = πP`, `sx₂ = π`); the `K`-independence of
`2πi, π², π²/P` comes from the transcendence of `π` (proved, `Gen.transcendental_pi`) and
`P ∉ 𝓛̃ = ℚ̄ + ℚ̄𝓛` (which also gives `P/π ∉ ℚ̄`) (a named input, `NotLtildeA`, the abelian analogue of `Gen.NotLtilde`; Wüstholz 1989 on
`G_a × G_m^m × A`). This is the argument that removes Chudnovsky's theorem (paper [II], Remark `rem:noChud`).

Instance: `P = (1 − ζ₅)B(1/5, 1/5)` (`corA2_beta5`, stated for `B(1/5, 1/5)` itself).
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen

namespace CM4E.AbVar

/-- **Named input (Wüstholz 1989).** `P ∉ 𝓛̃ = ℚ̄ + ℚ̄𝓛`. -/
def NotLtildeA (P : ℂ) : Prop := P ∉ Ltilde

lemma log_mem_KLog {K : Submodule ℚ ℂ} {a z : ℂ} (ha : a⁻¹ ∈ K) (hz : IsAlgebraic ℚ (Complex.exp (a * z)))
    (ha0 : a ≠ 0) : z ∈ KLog K :=
  ⟨1, fun _ => a⁻¹, fun _ => a * z, fun _ => ha, fun _ => hz, by simp; field_simp⟩

/-- **Corollary A2** (generic first-kind slot): at least one of `e^{aπ²}`, `e^{bπP}`, `e^{cπ²/P}` is transcendental. -/
theorem corA2 (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) (s₀ : Fin g) (hN : N ≠ 0)
    (hW : Thm11KappaAK N g κ P s₀ ∅) (hg : 2 * g ≤ N.totient) (hκ : κ s₀ = 1) (hκN : ∀ s, (κ s).Coprime N)
    (hNot : NotLtildeA (P s₀)) (a b c : ℂ) (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (b * (Real.pi * P s₀))) ∧
      IsAlgebraic ℚ (Complex.exp (c * (Real.pi ^ 2 / P s₀)))) := by
  rintro ⟨h1, h2, h3⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP0 : P s₀ ≠ 0 := fun h => hNot (h ▸ alg_mem_Ltilde isAlgebraic_zero)
  have hT : Transcendental ℚ (P s₀ / Real.pi) := fun halg => hNot (by
    rw [show P s₀ = P s₀ / Real.pi * Real.pi by field_simp]; exact Ltilde_smul halg pi_mem_Ltilde)
  obtain ⟨r, hr, β, hβ, hS⟩ := exists_adapted_basisN N hN {a⁻¹, b⁻¹, c⁻¹, I} (by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    exacts [ha.inv, hb.inv, hc.inv, isAlgebraic_I])
  have hIK : I ∈ KspanD (zetaN N) N.totient β := hS I (by simp)
  have hKalg : ∀ z ∈ KspanD (zetaN N) N.totient β, IsAlgebraic ℚ z :=
    fun z hz => KspanD_isAlgebraic (isAlgebraic_zetaN N hN) hβ.alg hz
  have hexpIπ : IsAlgebraic ℚ (Complex.exp ((-I)⁻¹ * Real.pi)) := by
    rw [show (-I)⁻¹ * (Real.pi : ℂ) = Real.pi * I by rw [inv_neg, Complex.inv_I]; ring, Complex.exp_pi_mul_I]
    exact isAlgebraic_one.neg
  have hnegI : ((-I)⁻¹)⁻¹ ∈ KspanD (zetaN N) N.totient β := by
    rw [inv_inv]; exact neg_mem hIK
  -- the `K`-independence of `2πi, π², π²/P`
  have hπL := pi_mem_Ltilde
  have hπPL : (Real.pi : ℂ) * P s₀ ∈ Ltilde := mem_Ltilde_of_log hb hb0 h2
  have hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ KspanD (zetaN N) N.totient β → a₁ ∈ KspanD (zetaN N) N.totient β →
      a₂ ∈ KspanD (zetaN N) N.totient β →
      a₀ * (2 * Real.pi * I) + a₁ * (Real.pi : ℂ) ^ 2 + a₂ * ((Real.pi : ℂ) ^ 2 / P s₀) = 0 →
        a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 := by
    intro a₀ a₁ a₂ k₀ k₁ k₂ hrel
    have g₀ := hKalg _ k₀
    have g₁ := hKalg _ k₁
    have g₂ := hKalg _ k₂
    have hrel' : 2 * I * a₀ * P s₀ + a₁ * (Real.pi * P s₀) + a₂ * Real.pi = 0 := by
      have := congrArg (· * (P s₀ / Real.pi)) hrel
      simp only [zero_mul] at this
      field_simp at this
      linear_combination this
    by_cases hz2 : a₂ = 0
    · subst hz2
      have hrel2 : (Real.pi : ℂ) * (2 * I * a₀ + a₁ * Real.pi) = 0 := by linear_combination hrel
      have h0 := (mul_eq_zero.mp hrel2).resolve_left hpi
      by_cases hz1 : a₁ = 0
      · subst hz1
        refine ⟨?_, rfl, rfl⟩
        have : 2 * I * a₀ = 0 := by linear_combination h0
        simpa [Complex.I_ne_zero] using this
      · exfalso
        apply transcendental_pi
        have : (Real.pi : ℂ) = -(2 * I * a₀) / a₁ := by field_simp; linear_combination h0
        rw [this, ← mem_algebraicClosure_iff]
        exact div_mem (neg_mem (mul_mem (mul_mem (by simp) (mem_algebraicClosure_iff.mpr isAlgebraic_I))
          (mem_algebraicClosure_iff.mpr g₀))) (mem_algebraicClosure_iff.mpr g₁)
    · exfalso
      by_cases hz1 : a₁ = 0
      · subst hz1
        by_cases hz0 : a₀ = 0
        · subst hz0
          have : a₂ * Real.pi = 0 := by linear_combination hrel'
          exact mul_ne_zero hz2 hpi this
        · apply hT
          have : P s₀ / Real.pi = -a₂ / (2 * I * a₀) := by
            field_simp; linear_combination hrel'
          rw [this, ← mem_algebraicClosure_iff]
          exact div_mem (neg_mem (mem_algebraicClosure_iff.mpr g₂)) (mul_mem (mul_mem (by simp)
            (mem_algebraicClosure_iff.mpr isAlgebraic_I)) (mem_algebraicClosure_iff.mpr g₀))
      · apply hNot
        by_cases hz0 : a₀ = 0
        · subst hz0
          have h' : a₁ * P s₀ + a₂ = 0 := mul_left_cancel₀ hpi (by linear_combination hrel')
          have : P s₀ = -a₂ / a₁ := by field_simp; linear_combination h'
          rw [this]
          exact alg_mem_Ltilde (by
            rw [← mem_algebraicClosure_iff]
            exact div_mem (neg_mem (mem_algebraicClosure_iff.mpr g₂)) (mem_algebraicClosure_iff.mpr g₁))
        · have h2ia : 2 * I * a₀ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hz0
          have : P s₀ = (-(a₁ / (2 * I * a₀))) * (Real.pi * P s₀) + (-(a₂ / (2 * I * a₀))) * Real.pi := by
            field_simp; linear_combination hrel'
          rw [this]
          have hq : ∀ z : ℂ, IsAlgebraic ℚ z → IsAlgebraic ℚ (-(z / (2 * I * a₀))) := fun z hz => by
            rw [← mem_algebraicClosure_iff]
            exact neg_mem (div_mem (mem_algebraicClosure_iff.mpr hz) (mul_mem (mul_mem (by simp)
              (mem_algebraicClosure_iff.mpr isAlgebraic_I)) (mem_algebraicClosure_iff.mpr g₀)))
          exact Ltilde_add (Ltilde_smul (hq _ g₁) hπPL) (Ltilde_smul (hq _ g₂) hπL)
  -- apply Theorem MG-A (`K`-form) with `c = 1`
  refine mgA_K (b := β) ∅ hN hW hg hκ hκN hT hβ 1 hβ.one_mem one_ne_zero hIK
    ![(Real.pi : ℂ) ^ 2, (Real.pi : ℂ) ^ 2 / P s₀] ?_ ?_ (by simpa using hind)
  · intro k
    fin_cases k
    · exact log_mem_KLog (hS _ (by simp)) h1 ha0
    · exact log_mem_KLog (hS _ (by simp)) h3 hc0
  · intro k
    have hzero : (0 : ℂ) ∈ KSlotA g P s₀ ∅ (KspanD (zetaN N) N.totient β) :=
      ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, by simp⟩
    fin_cases k
    · refine ⟨Real.pi * P s₀, log_mem_KLog (hS _ (by simp)) h2 hb0, 0, hzero, ?_⟩
      simp; field_simp
    · refine ⟨Real.pi, log_mem_KLog hnegI hexpIπ (inv_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)), 0, hzero, ?_⟩
      simp; field_simp

/-- **Corollary A2 for `B(1/5, 1/5)`**: at least one of `e^{aπ²}`, `e^{bπB(1/5,1/5)}`, `e^{cπ²/B(1/5,1/5)}` is
transcendental (`a, b, c ∈ ℚ̄ˣ`). -/
theorem corA2_beta5 (hW : Thm11KappaAK 5 2 (fun s => (s : ℕ) + 1) perA5 0 ∅)
    (hNot : NotLtildeA (perA5 0)) (a b c : ℂ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧
      IsAlgebraic ℚ (Complex.exp (b * (Real.pi * betaIntegral (1 / 5) (1 / 5)))) ∧
      IsAlgebraic ℚ (Complex.exp (c * (Real.pi ^ 2 / betaIntegral (1 / 5) (1 / 5))))) := by
  have hz := one_sub_zetaN_ne 5 (by norm_num)
  have hB : betaIntegral (1 / 5) (1 / 5) = perA5 0 / (1 - zetaN 5) := by
    rw [← betaG_eq_betaIntegral (by norm_num) (by norm_num), eq_div_iff hz, perA5]
    norm_num
    ring
  have hzalg : IsAlgebraic ℚ (1 - zetaN 5) := isAlgebraic_one.sub (isAlgebraic_zetaN 5 (by norm_num))
  have hP0 : perA5 0 ≠ 0 := fun h => hNot (h ▸ alg_mem_Ltilde isAlgebraic_zero)
  rintro ⟨h1, h2, h3⟩
  refine corA2 5 2 (fun s => (s : ℕ) + 1) perA5 0 (by norm_num) hW (by decide) rfl (by decide) hNot a (b / (1 - zetaN 5))
    (c * (1 - zetaN 5)) ha (by
      rw [← mem_algebraicClosure_iff]
      exact div_mem (mem_algebraicClosure_iff.mpr hb) (mem_algebraicClosure_iff.mpr hzalg)) (hc.mul hzalg) ha0
    (div_ne_zero hb0 hz) (mul_ne_zero hc0 hz) ⟨h1, ?_, ?_⟩
  · convert h2 using 2; rw [hB]; field_simp
  · convert h3 using 2; rw [hB]; field_simp

end CM4E.AbVar
