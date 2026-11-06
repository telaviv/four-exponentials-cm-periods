/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.ThmM
import CM4E.Gen.MXGen
import CM4E.Gen.MG13

/-!
# Theorem M: the clause `s ∈ k`, and Corollary M (paper, `cor:M`)

* `thmM_I_k`: on `E_i`, if `u ∈ 𝓛_E` then `s ∈ ℚ(i)` (from Masser's theorem, the named input `MasserCM`).
* (M1) `m1`: `℘(cω/π) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`, on every CM lattice `ω ℤ[α]` with algebraic `g₂, g₃`.
* (M3) `m3`: if `e^{π²} ∈ ℚ̄` then `℘(cπω) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`.
* (M3′) `m3'`: for `e^z ∈ ℚ̄ \ {1}`, one of `e^{iπz}`, `℘(ωz)` is transcendental (with Hermite–Lindemann, a named input).
* (Mη) `meta_I`: `η(ϖ)u ∉ 𝓛̃` for `u ∈ 𝓛_{E_i} \ ℚ(i)ϖ`, where `η(ϖ) = π/ϖ`.

(M2) (`℘(ϖ log α/π) ∉ ℚ̄` for `α` not a root of unity) needs Gel'fond–Schneider and is not formalised.
-/

open Complex Module CM4E.Waldschmidt CM4E.MX

namespace CM4E.Gen

/-- **Named input (Hermite–Lindemann).** `e^z` is transcendental for algebraic `z ≠ 0`. -/
def HermiteLindemann : Prop :=
  ∀ z : ℂ, IsAlgebraic ℚ z → z ≠ 0 → Transcendental ℚ (Complex.exp z)

lemma qbar_of_logE {P : PeriodPair} {u : ℂ} (hu : LogE P u) : u ∈ QbarLogE P :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩

/-- If `℘(u) ∈ ℚ̄` (or `u` is a period) then `u ∈ 𝓛_E`, since `℘'² = 4℘³ − g₂℘ − g₃`. -/
lemma logE_of_wp (P : PeriodPair) (hg₂ : IsAlgebraic ℚ P.g₂) (hg₃ : IsAlgebraic ℚ P.g₃) {u : ℂ}
    (hwp : IsAlgebraic ℚ (P.weierstrassP u)) : LogE P u := by
  by_cases hu : u ∈ P.lattice
  · exact Or.inl hu
  · refine Or.inr ⟨hwp, IsAlgebraic.of_pow two_pos ?_⟩
    rw [P.derivWeierstrassP_sq u hu, ← mem_algebraicClosure_iff]
    have h := mem_algebraicClosure_iff.mpr hwp
    have h4 : (4 : ℂ) ∈ algebraicClosure ℚ ℂ := by
      simp
    exact sub_mem (sub_mem (mul_mem h4 (pow_mem h 3)) (mul_mem (mem_algebraicClosure_iff.mpr hg₂) h))
      (mem_algebraicClosure_iff.mpr hg₃)

lemma logNat_of_logE (P : PeriodPair) (eta : ℤ → ℤ → ℂ) {u : ℂ} (hu : LogE P u) :
    ∃ w, LogNat P eta u w := by
  by_cases hl : u ∈ P.lattice
  · obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hl
    exact ⟨eta m n, Or.inl ⟨m, n, hmn.symm, by rw [sub_self]; exact isAlgebraic_zero⟩⟩
  · rcases hu with h | ⟨h1, h2⟩
    · exact absurd h hl
    · exact ⟨LSG.Weierstrass.zeta P u, Or.inr ⟨hl, h1, h2, by rw [sub_self]; exact isAlgebraic_zero⟩⟩

/-- `x = sω`, `x = cω·y` with `ω ≠ 0`: `s = c·y`. -/
private lemma coeff_eq {ω x s y : ℂ} (hω : ω ≠ 0) (h1 : x = s * (1 * ω)) (h2 : x = y * ω) : s = y := by
  apply mul_right_cancel₀ hω
  rw [← h2]; linear_combination -h1

/-- `c = sπ` is impossible for algebraic `c ≠ 0, s`. -/
private lemma pi_ne_div {c s : ℂ} (hc : IsAlgebraic ℚ c) (hs : IsAlgebraic ℚ s) (hc0 : c ≠ 0)
    (h : c = s * Real.pi) : False := by
  have hs0 : s ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact hc0 h
  apply transcendental_pi
  have : (Real.pi : ℂ) = c / s := by rw [h]; field_simp
  rw [this, ← mem_algebraicClosure_iff]
  exact div_mem (mem_algebraicClosure_iff.mpr hc) (mem_algebraicClosure_iff.mpr hs)

lemma alg_mem_Ltilde {z : ℂ} (hz : IsAlgebraic ℚ z) : z ∈ Ltilde :=
  ⟨0, z, Fin.elim0, Fin.elim0, hz, fun k => k.elim0, fun k => k.elim0, by simp⟩

/-- **Theorem M on `E_i`, with `s ∈ k`**: if `u ∈ 𝓛_{E_i}`, `ℓ ∈ 𝓛̃` and `iπu = ϖℓ`, then `u = sϖ`, `ℓ = s·iπ` with
`s ∈ ℚ(i)`. -/
theorem thmM_I_k (hW : Thm11KappaM latI) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃) (hT : Transcendental ℚ ((varpi : ℂ) / Real.pi)) (hMa : MasserCM)
    (u ℓ : ℂ) (hu : LogE lemniscatic u) (hℓ : ℓ ∈ Ltilde) (hrel : I * Real.pi * u = varpi * ℓ) :
    ∃ p q : ℚ, u = (p + q * I) * varpi ∧ ℓ = (p + q * I) * (I * Real.pi) := by
  obtain ⟨s, hs, hus, hℓs⟩ := thmM latI hW hg₂ hg₃ hT 1 isAlgebraic_one one_ne_zero u ℓ (qbar_of_logE hu) hℓ
    (by rw [one_mul]; exact hrel)
  have hus' : u = s * varpi := by rw [hus]; simp [latI]
  obtain ⟨w, hw⟩ := logNat_of_logE lemniscatic etaLem hu
  obtain ⟨p, q, hpq⟩ := hMa.1 u w s hw hs hus'
  exact ⟨p, q, by rw [← hpq]; exact hus', by rw [← hpq]; exact hℓs⟩

/-- **(M1)** `℘(cω/π) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`. -/
theorem m1 (L : CMLattice) (hW : Thm11KappaM L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ (L.ω / Real.pi)) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    Transcendental ℚ (L.pp.weierstrassP (c * L.ω / Real.pi)) := by
  intro hwp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  obtain ⟨s, hs, hus, -⟩ := thmM L hW hg₂ hg₃ hT 1 isAlgebraic_one one_ne_zero _ (I * c)
    (qbar_of_logE (logE_of_wp L.pp hg₂ hg₃ hwp)) (alg_mem_Ltilde (isAlgebraic_I.mul hc))
    (by field_simp)
  have e := coeff_eq L.ω_ne_zero hus (show c * L.ω / Real.pi = (c / Real.pi) * L.ω by ring)
  exact pi_ne_div hc hs hc0 (by rw [e]; field_simp)

/-- **(M3)** If `e^{π²} ∈ ℚ̄` then `℘(cπω) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`. -/
theorem m3 (L : CMLattice) (hW : Thm11KappaM L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ (L.ω / Real.pi)) (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    Transcendental ℚ (L.pp.weierstrassP (c * Real.pi * L.ω)) := by
  intro hwp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hℓ : I * c * (Real.pi : ℂ) ^ 2 ∈ Ltilde :=
    Ltilde_smul (isAlgebraic_I.mul hc) (mem_Ltilde_of_log isAlgebraic_one one_ne_zero (by rwa [one_mul]))
  obtain ⟨s, hs, hus, -⟩ := thmM L hW hg₂ hg₃ hT 1 isAlgebraic_one one_ne_zero _ _
    (qbar_of_logE (logE_of_wp L.pp hg₂ hg₃ hwp)) hℓ (by ring)
  have e := coeff_eq L.ω_ne_zero hus (show c * Real.pi * L.ω = (c * Real.pi) * L.ω by ring)
  exact pi_ne_div hs hc (by rw [e]; exact mul_ne_zero hc0 hpi) e

/-- **(M3′)** If `e^z ∈ ℚ̄`, `e^z ≠ 1` (`z` any logarithm of `α ∈ ℚ̄ \ {0, 1}`), then `e^{iπz}` and `℘(ωz)` are not both
algebraic. Uses Hermite–Lindemann. -/
theorem m3' (L : CMLattice) (hW : Thm11KappaM L) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hT : Transcendental ℚ (L.ω / Real.pi)) (hHL : HermiteLindemann) (z : ℂ)
    (hz : IsAlgebraic ℚ (Complex.exp z)) (hz1 : Complex.exp z ≠ 1) :
    ¬ (IsAlgebraic ℚ (Complex.exp (I * Real.pi * z)) ∧ IsAlgebraic ℚ (L.pp.weierstrassP (L.ω * z))) := by
  rintro ⟨he, hwp⟩
  obtain ⟨s, hs, hus, -⟩ := thmM L hW hg₂ hg₃ hT 1 isAlgebraic_one one_ne_zero _ (I * Real.pi * z)
    (qbar_of_logE (logE_of_wp L.pp hg₂ hg₃ hwp))
    (mem_Ltilde_of_log isAlgebraic_one one_ne_zero (by rwa [one_mul])) (by ring)
  have e := coeff_eq L.ω_ne_zero hus (show L.ω * z = z * L.ω by ring)
  have hz0 : z ≠ 0 := by rintro rfl; exact hz1 Complex.exp_zero
  exact hHL z (e ▸ hs) hz0 hz

/-- **(Mη)** `η(ϖ)u ∉ 𝓛̃` for `u ∈ 𝓛_{E_i} \ ℚ(i)ϖ` (`η(ϖ) = π/ϖ`). -/
theorem meta_I (hW : Thm11KappaM latI) (hg₂ : IsAlgebraic ℚ lemniscatic.g₂)
    (hg₃ : IsAlgebraic ℚ lemniscatic.g₃) (hT : Transcendental ℚ ((varpi : ℂ) / Real.pi)) (hMa : MasserCM)
    (u : ℂ) (hu : LogE lemniscatic u) (hnot : ¬ ∃ p q : ℚ, u = (p + q * I) * varpi) :
    (Real.pi / varpi : ℂ) * u ∉ Ltilde := by
  intro hm
  have hv := varpi_ne_zero'
  obtain ⟨p, q, h, -⟩ := thmM_I_k hW hg₂ hg₃ hT hMa u (I * ((Real.pi / varpi : ℂ) * u)) hu
    (Ltilde_smul isAlgebraic_I hm) (by field_simp)
  exact hnot ⟨p, q, h⟩

end CM4E.Gen
