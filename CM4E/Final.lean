/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Ext.Bridge.Lemniscatic
import CM4E.Ext.SchneiderMain
import CM4E.MainQi
import CM4E.TwoThree
import CM4E.MainNat
import CM4E.MX
import CM4E.Gen.Instances
import CM4E.Gen.MXGen
import CM4E.Gen.SMG
import CM4E.Gen.MG13
import CM4E.Gen.Deg2
import CM4E.Gen.ThmMCor
import CM4E.Gen.MGnK

/-!
# The main theorems with every hypothesis except W88 discharged

`CM4E/Ext/` (a copy of the needed part of the sibling project `lean_lsg`; see `CM4E/Ext/PROVENANCE.md`) proves, with
standard axioms only:
* `g₂(ϖℤ[i])` is algebraic (`CM4E.Ext.Bridge.isAlgebraic_g₂`; it proves `g₂ = 4` from the Γ-formula for `ϖ`);
* Schneider's theorem: a nonzero period of a lattice with algebraic `g₂, g₃` is transcendental, and so is the period
  divided by `π` (`CM4E.Ext.Schneider.period_transcendental`, `CM4E.Ext.Bridge.irrational_varpi_div_pi_of`).

`CM4E.Ext.LemniscateIndep.varpi` has the same body as `CM4E.varpi`, so the two are equal by `rfl` (used implicitly
below). This file feeds these facts into the conditional theorems. What remains assumed is the hyperplane hypothesis
`hW` (W88 §5d for the relevant group model); for the `Ω_ρ` and MX results, `g₂, g₃` of `Ω_ρ ℤ[ρ]` (`hg₂'`, `hg₃'`);
and the named classical inputs where used (Theorems S, MX, MX′, M; Cors. MG1, MG3, MX1, deg2, Mη, M3′): `hΓ`, `hM`,
`Gen.WuestholzMX`, `Gen.WuestholzSix`, `Gen.MasserCM`, `Gen.Baker3`, `Gen.NotLtilde`, `Gen.HermiteLindemann`,
`Gen.LaurentZeta` (all consequences of Wüstholz's analytic subgroup theorem or classical results; see `TRUST.md`).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Final

/-- `g₂(ϖℤ[i]) ∈ ℚ̄` (`CM4E/Ext`). -/
theorem hg₂ : IsAlgebraic ℚ lemniscatic.g₂ := CM4E.Ext.Bridge.isAlgebraic_g₂ lemniscatic rfl rfl

/-- `ϖ/π ∉ ℚ` (`CM4E/Ext`: Schneider). -/
theorem hS : Irrational (varpi / Real.pi) := CM4E.Ext.Bridge.irrational_varpi_div_pi_of lemniscatic rfl rfl

/-- `ϖ` is transcendental (`CM4E/Ext`: Schneider). -/
theorem hT : Transcendental ℚ (varpi : ℂ) :=
  CM4E.Ext.Schneider.period_transcendental hg₂ g₃_lemniscatic_isAlgebraic lemniscatic.ω₁_mem_lattice
    (by exact_mod_cast varpi_ne_zero)

/-- **Theorem 1(b) for `c ∈ ℚ(i)ˣ`**: four exponentials at `t = ((p + qi)/D)·ϖ/π`, assuming only W88 §5d for
`G_m⁴ × E_i`. -/
theorem fourExpAt_Qi (hW : Thm11Kappa lemniscatic 4)
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (MainQi.tExp p q D) :=
  MainQi.fourExpAt_Qi hW hg₂ hS p q D hD hpq

/-- **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic**, assuming only W88 §5d for `G_m⁴ × E_i`. -/
theorem two_three (hW : Thm11Kappa lemniscatic 4) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 3))) :=
  TwoThree.two_three hW hg₂ hS

/-- **Theorem 1(a) for `c ∈ ℚ(i)ˣ`**: four exponentials at `t = Dϖ/(p + qi)`, assuming only W88 §5d for
`G_m⁸ × Q''`. -/
theorem fourExpAt_varpi (hW : MainNat.Thm11KappaNat)
    (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (MainNat.tN p q D) :=
  MainNat.main hW hg₂ hT p q D hD hpq

/-- **`2^ϖ` and `3^ϖ` are not both algebraic**, assuming only W88 §5d for `G_m⁸ × Q''`. -/
theorem two_three_varpi (hW : MainNat.Thm11KappaNat) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 3))) :=
  MainNat.two_three_varpi hW hg₂ hT

/-- **Theorem MX, `K`-form, for every `β ∈ ℚ̄ˣ`**, with `g₂, g₃(ϖℤ[i])` discharged. -/
theorem mx_K (hW : Gen.Thm11KappaMXG)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi))
    (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : MX.LogNat lemniscatic etaLem zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (β * MX.etaRho) = (wX + wY + t) * varpi) :
    ∃ x x' : ℂ, IsAlgebraic ℚ x ∧ IsAlgebraic ℚ x' ∧ zX + zY + a = x * varpi + x' * omegaRho :=
  Gen.mx_K hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃' hΓ hM β hβ hβ0 zX wX zY wY a t hX hY ha ht hrel

/-- **Theorem MX** (`a = 0`, `z(X) ∈ ℚ(i)ϖ`, `z(Y) ∈ ℚ(ρ)Ω_ρ`) for every `β ∈ ℚ̄ˣ`, with `g₂, g₃(ϖℤ[i])` discharged. -/
theorem mx (hW : Gen.Thm11KappaMXG)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (hWu : Gen.WuestholzMX)
    (hMa : Gen.MasserCM) (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : MX.LogNat lemniscatic etaLem zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t)
    (hrel : (zX + zY + a) * (β * MX.etaRho) = (wX + wY + t) * varpi) :
    a = 0 ∧ (∃ p q : ℚ, zX = (p + q * I) * varpi) ∧ (∃ p q : ℚ, zY = (p + q * MX.rho) * omegaRho) :=
  Gen.mx_full hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃' hΓ hWu hMa β hβ hβ0 zX wX zY wY a t hX hY ha ht
    hrel

/-- **Corollary MX1**, with `g₂, g₃(ϖℤ[i])` discharged. -/
theorem mx1 (hW : Gen.Thm11KappaMXG)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (hWu : Gen.WuestholzMX)
    (hMa : Gen.MasserCM) (hLa : Gen.LaurentZeta) (u : ℂ)
    (hwp : IsAlgebraic ℚ (lemniscatic.weierstrassP u)) (hwp' : IsAlgebraic ℚ (lemniscatic.derivWeierstrassP u))
    (hu' : ¬ ∃ p q : ℚ, u = (p + q * I) * varpi) (a t : ℂ) (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t) :
    Transcendental ℚ ((varpi : ℂ) * omegaRho * (CM4E.Ext.Weierstrass.zeta lemniscatic u + t) /
      (Real.pi * (u + a))) :=
  Gen.mx1 hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃' hΓ hWu hMa hLa u hwp hwp' hu' a t ha ht

/-! ## Theorem 1 for every algebraic `c` (general `K`; `CM4E/Gen/`) -/

/-- **Theorem 1(a) for `Ω = ϖ` and every algebraic `c ≠ 0`**: `FourExpAt (cϖ)`, assuming only W88 §5d for the groups
`G_m^{2n} × Q''` (`Gen.Thm11KappaMGn Gen.latI`). -/
theorem fourExpAt_varpi_all (hW : Gen.Thm11KappaMGn Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) : FourExpAt (c * varpi) :=
  Gen.fourExpAt_MGn Gen.latI hW Gen.kappaOneZero_latI hg₂ g₃_lemniscatic_isAlgebraic hT c hc hc0

/-- **Theorem 1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`**: `FourExpAt (cϖ/π)`, assuming only W88 §5d for the groups
`G_m^{2n} × A''` (`Gen.Thm11KappaMG Gen.latI`). -/
theorem fourExpAt_varpi_div_pi_all (hW : Gen.Thm11KappaMG Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) : FourExpAt (c * varpi / Real.pi) :=
  Gen.fourExpAt_MG Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) c hc hc0

/-- **Theorem 1(a) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**: `FourExpAt (cΩ_ρ)`, assuming W88 §5d
(`Gen.Thm11KappaMGn Gen.latRho`) and that `g₂, g₃` of `Ω_ρ ℤ[ρ]` are algebraic. -/
theorem fourExpAt_omegaRho_all (hW : Gen.Thm11KappaMGn Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : FourExpAt (c * omegaRho) :=
  Gen.fourExpAt_MGn Gen.latRho hW Gen.kappaOneZero_latRho hg₂' hg₃'
    (CM4E.Ext.Schneider.period_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero) c hc hc0

/-- **Theorem 1(b) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**: `FourExpAt (cΩ_ρ/π)`, assuming W88 §5d
(`Gen.Thm11KappaMG Gen.latRho`) and that `g₂, g₃` of `Ω_ρ ℤ[ρ]` are algebraic. -/
theorem fourExpAt_omegaRho_div_pi_all (hW : Gen.Thm11KappaMG Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) : FourExpAt (c * omegaRho / Real.pi) :=
  Gen.fourExpAt_MG Gen.latRho hW hg₂' hg₃'
    (CM4E.Ext.Schneider.period_div_pi_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero) c hc hc0

/-- **`2^{Ω_ρ}` and `3^{Ω_ρ}` are not both algebraic**, assuming W88 §5d and `g₂, g₃(Ω_ρ ℤ[ρ]) ∈ ℚ̄`. -/
theorem two_three_omegaRho (hW : Gen.Thm11KappaMGn Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((omegaRho : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((omegaRho : ℂ) * Complex.log 3))) := by
  have h := fourExpAt_omegaRho_all hW hg₂' hg₃' 1 isAlgebraic_one one_ne_zero (Complex.log 2)
    (Complex.log 3) (by simpa using log_mem_logAlg 2 two_ne_zero)
    (by simpa using log_mem_logAlg 3 three_ne_zero) linearIndependent_two_three
  simpa using h

/-! ## Theorem S (paper [II]) -/

/-- **Theorem S for `Ω = ϖ`**: for `t ∈ ℚ̄ˣϖ ∪ ℚ̄ˣ/ϖ ∪ ℚ̄ˣϖ/π ∪ ℚ̄ˣπ/ϖ` and `ℚ̄`-independent `y₁, y₂`, the numbers
`y₁, y₂, ty₁, ty₂` are not all in `𝓛̃ = ℚ̄ + ℚ̄𝓛`. Assumes W88 §5d (`hWa`, `hWb`) and `Gen.NotLtilde Gen.latI`. -/
theorem thmS_varpi (hWa : Gen.Thm11KappaSMG Gen.latI) (hWb : Gen.Thm11KappaSMGn Gen.latI)
    (hNot : Gen.NotLtilde Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (t : ℂ)
    (ht : t = c * varpi ∨ t = c / varpi ∨ t = c * varpi / Real.pi ∨ t = c * Real.pi / varpi)
    (y₁ y₂ : ℂ) (hind : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * y₁ + a₂ * y₂ = 0 →
      a₁ = 0 ∧ a₂ = 0) :
    ¬ (y₁ ∈ Gen.Ltilde ∧ y₂ ∈ Gen.Ltilde ∧ t * y₁ ∈ Gen.Ltilde ∧ t * y₂ ∈ Gen.Ltilde) :=
  Gen.thmS Gen.latI hWa hWb hg₂ g₃_lemniscatic_isAlgebraic hT
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hNot c hc hc0 t ht y₁ y₂ hind

/-- **Theorem S for `Ω = Ω_ρ`**, assuming also `g₂, g₃(Ω_ρ ℤ[ρ]) ∈ ℚ̄`. -/
theorem thmS_omegaRho (hWa : Gen.Thm11KappaSMG Gen.latRho) (hWb : Gen.Thm11KappaSMGn Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hNot : Gen.NotLtilde Gen.latRho) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (t : ℂ)
    (ht : t = c * omegaRho ∨ t = c / omegaRho ∨ t = c * omegaRho / Real.pi ∨ t = c * Real.pi / omegaRho)
    (y₁ y₂ : ℂ) (hind : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * y₁ + a₂ * y₂ = 0 →
      a₁ = 0 ∧ a₂ = 0) :
    ¬ (y₁ ∈ Gen.Ltilde ∧ y₂ ∈ Gen.Ltilde ∧ t * y₁ ∈ Gen.Ltilde ∧ t * y₂ ∈ Gen.Ltilde) :=
  Gen.thmS Gen.latRho hWa hWb hg₂' hg₃'
    (CM4E.Ext.Schneider.period_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero)
    (CM4E.Ext.Schneider.period_div_pi_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero) hNot c hc hc0 t ht y₁ y₂ hind

/-! ## Corollaries MG1, MG3 -/

/-- **Corollary MG1 for `ϖ`**: one of `e^{π²}`, `e^{πϖ}`, `e^{π²/ϖ}` is transcendental. Assumes W88 §5d for the groups
of Theorem SMG and `Gen.NotLtilde Gen.latI` (`π` transcendental is proved, `Gen.transcendental_pi`). -/
theorem mg1_varpi (hW : Gen.Thm11KappaSMG Gen.latI) (hNot : Gen.NotLtilde Gen.latI) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (Real.pi * varpi)) ∧
      IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2 / varpi))) := by
  have := Gen.mg1 Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic hT
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hNot 1 1 1
    isAlgebraic_one one_ne_zero isAlgebraic_one one_ne_zero isAlgebraic_one one_ne_zero
  simpa [Gen.latI] using this

/-- **Corollary MG3 for `ϖ`**: if `e^{π²}` and `e^{cπϖ}` are algebraic and `2πi, π², log α` are `ℚ`-independent, then
`α^{ϖ/π}` is transcendental. Assumes W88 §5d (SMG) and Baker's theorem. -/
theorem mg3_varpi (hW : Gen.Thm11KappaSMG Gen.latI) (hBaker : Gen.Baker3) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (hπω : IsAlgebraic ℚ (Complex.exp (c * Real.pi * varpi))) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x))
    (hind : LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]) :
    Transcendental ℚ (Complex.exp (varpi / Real.pi * x)) :=
  Gen.mg3 Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hBaker c hc hc0 hπ2 hπω x hx hind

/-- **Corollary deg2 (ii)**: `1, ϖ, Ω_ρ, ϖΩ_ρ/π` are linearly independent over `ℚ̄`. Assumes W88 §5d (MX groups),
`g₂, g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`, `hΓ`, and the named input `Gen.WuestholzSix`. -/
theorem deg2_ii (hW : Gen.Thm11KappaMXG)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (h6 : Gen.WuestholzSix)
    (c0 c1 c2 c3 : ℂ) (h0 : IsAlgebraic ℚ c0) (h1 : IsAlgebraic ℚ c1) (h2 : IsAlgebraic ℚ c2)
    (h3 : IsAlgebraic ℚ c3)
    (hrel : c0 + c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho / Real.pi) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 :=
  Gen.deg2_ii hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃' hΓ h6 c0 c1 c2 c3 h0 h1 h2 h3 hrel

/-- **Proposition D′ (Theorem MX′), `K`-form, for every `β ∈ ℚ̄ˣ`**, with `g₂, g₃(ϖℤ[i])` discharged: if
`(z(X) + w(Y) + a)·βΩ_ρ = (w(X) + z(Y) + c)·ϖ` then `z(X) + w(Y) + a ∈ ℚ̄ϖ + ℚ̄η_ρ`. -/
theorem mxP_K (hW : Gen.Thm11KappaMXP)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi))
    (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a c : ℂ)
    (hX : MX.LogNat lemniscatic etaLem zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (hc : IsAlgebraic ℚ c)
    (hrel : (zX + wY + a) * (β * omegaRho) = (wX + zY + c) * varpi) :
    ∃ x x' : ℂ, IsAlgebraic ℚ x ∧ IsAlgebraic ℚ x' ∧ zX + wY + a = x * varpi + x' * MX.etaRho :=
  Gen.mxP_K hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃' hΓ hM β hβ hβ0 zX wX zY wY a c hX hY ha hc
    hrel

/-- **Corollary deg2 (i)**: `π, ϖ, Ω_ρ, ϖΩ_ρ` are linearly independent over `ℚ̄`. Assumes W88 §5d (MX′ groups),
`g₂, g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`, `hΓ`, and the named input `Gen.WuestholzSix`. -/
theorem deg2_i (hW : Gen.Thm11KappaMXP)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (h6 : Gen.WuestholzSix)
    (c0 c1 c2 c3 : ℂ) (h0 : IsAlgebraic ℚ c0) (h1 : IsAlgebraic ℚ c1) (h2 : IsAlgebraic ℚ c2)
    (h3 : IsAlgebraic ℚ c3)
    (hrel : c0 * Real.pi + c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 :=
  Gen.deg2_i hW hg₂ g₃_lemniscatic_isAlgebraic hg₂' hg₃' hΓ h6 c0 c1 c2 c3 h0 h1 h2 h3 hrel

/-! ## Theorem M and Corollary M -/

/-- **Theorem M for `Ω = cϖ`**: if `u ∈ ℚ̄𝓛_{E_i}`, `ℓ ∈ 𝓛̃` and `iπu = cϖℓ` (`c ∈ ℚ̄ˣ`), then `u = s·cϖ`, `ℓ = s·iπ`
with `s ∈ ℚ̄`. Assumes only W88 §5d for the groups `A'' × G_m^n × G_a` (`Gen.Thm11KappaM Gen.latI`). -/
theorem thmM_varpi (hW : Gen.Thm11KappaM Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (u ℓ : ℂ)
    (hu : u ∈ Gen.QbarLogE lemniscatic) (hℓ : ℓ ∈ Gen.Ltilde) (hrel : I * Real.pi * u = c * varpi * ℓ) :
    ∃ s : ℂ, IsAlgebraic ℚ s ∧ u = s * (c * varpi) ∧ ℓ = s * (I * Real.pi) :=
  Gen.thmM Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) c hc hc0 u ℓ hu hℓ hrel

/-- **Theorem M for `Ω = cΩ_ρ`**, assuming also `g₂, g₃(Ω_ρ ℤ[ρ]) ∈ ℚ̄`. -/
theorem thmM_omegaRho (hW : Gen.Thm11KappaM Gen.latRho)
    (hg₂' : IsAlgebraic ℚ MX.equianharmonic.g₂) (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (u ℓ : ℂ)
    (hu : u ∈ Gen.QbarLogE MX.equianharmonic) (hℓ : ℓ ∈ Gen.Ltilde)
    (hrel : I * Real.pi * u = c * omegaRho * ℓ) :
    ∃ s : ℂ, IsAlgebraic ℚ s ∧ u = s * (c * omegaRho) ∧ ℓ = s * (I * Real.pi) :=
  Gen.thmM Gen.latRho hW hg₂' hg₃'
    (CM4E.Ext.Schneider.period_div_pi_transcendental hg₂' hg₃' MX.equianharmonic.ω₁_mem_lattice
      MX.omegaRho_ne_zero) c hc hc0 u ℓ hu hℓ hrel

/-- **Theorem M on `E_i` with `s ∈ ℚ(i)`** for `u ∈ 𝓛_{E_i}`, assuming also Masser's theorem (`Gen.MasserCM`). -/
theorem thmM_varpi_k (hW : Gen.Thm11KappaM Gen.latI) (hMa : Gen.MasserCM) (u ℓ : ℂ)
    (hu : Gen.LogE lemniscatic u) (hℓ : ℓ ∈ Gen.Ltilde) (hrel : I * Real.pi * u = varpi * ℓ) :
    ∃ p q : ℚ, u = (p + q * I) * varpi ∧ ℓ = (p + q * I) * (I * Real.pi) :=
  Gen.thmM_I_k hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hMa u ℓ hu hℓ hrel

/-- **(M1)** `℘(cϖ/π) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`, assuming only W88 §5d (`Gen.Thm11KappaM Gen.latI`). -/
theorem m1_varpi (hW : Gen.Thm11KappaM Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    Transcendental ℚ (lemniscatic.weierstrassP (c * varpi / Real.pi)) :=
  Gen.m1 Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) c hc hc0

/-- **(M3)** If `e^{π²} ∈ ℚ̄` then `℘(cπϖ) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`; in particular one of `e^{π²}`, `℘(πϖ)` is
transcendental. Assumes only W88 §5d. -/
theorem m3_varpi (hW : Gen.Thm11KappaM Gen.latI)
    (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2))) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    Transcendental ℚ (lemniscatic.weierstrassP (c * Real.pi * varpi)) :=
  Gen.m3 Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hπ2 c hc hc0

/-- **(M3′)** For `α = e^z ∈ ℚ̄ \ {0, 1}`, one of `e^{iπz}`, `℘(ϖz)` is transcendental. Assumes W88 §5d and
Hermite–Lindemann (`Gen.HermiteLindemann`). -/
theorem m3'_varpi (hW : Gen.Thm11KappaM Gen.latI) (hHL : Gen.HermiteLindemann) (z : ℂ)
    (hz : IsAlgebraic ℚ (Complex.exp z)) (hz1 : Complex.exp z ≠ 1) :
    ¬ (IsAlgebraic ℚ (Complex.exp (I * Real.pi * z)) ∧ IsAlgebraic ℚ (lemniscatic.weierstrassP (varpi * z))) :=
  Gen.m3' Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hHL z hz hz1

/-- **(Mη)** `η(ϖ)u ∉ 𝓛̃` for `u ∈ 𝓛_{E_i} \ ℚ(i)ϖ`. Assumes W88 §5d and Masser's theorem. -/
theorem meta_varpi (hW : Gen.Thm11KappaM Gen.latI) (hMa : Gen.MasserCM) (u : ℂ) (hu : Gen.LogE lemniscatic u)
    (hnot : ¬ ∃ p q : ℚ, u = (p + q * I) * varpi) : (Real.pi / varpi : ℂ) * u ∉ Gen.Ltilde :=
  Gen.meta_I hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hMa u hu hnot

/-! ## `K`-dimension forms of Theorems MG and MG♮ -/

/-- **Theorem MG, `K`-form, for `Ω = ϖ`**: for `s = cϖ/π` and a number field `K = span_ℚ θ ∋ i, c`, there are no
`x₁, x₂ ∈ K𝓛` with `sx₁, sx₂ ∈ K𝓛 + K𝓛_E` and `2πi, x₁, x₂` linearly independent over `K` (`dim_K S_K ≤ 2`). Assumes
only W88 §5d (`Gen.Thm11KappaMGK Gen.latI`). -/
theorem mg_K_varpi (hW : Gen.Thm11KappaMGK Gen.latI) {r : ℕ} {b : Fin r → ℂ} (hb : Gen.IsAdaptedFieldBasis I b)
    (c : ℂ) (hcK : c ∈ Gen.Kspan I b) (hc0 : c ≠ 0) (hIK : I ∈ Gen.Kspan I b)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ Gen.KLog (Gen.Kspan I b))
    (hsx : ∀ k, ∃ y ∈ Gen.KLog (Gen.Kspan I b), ∃ e ∈ Gen.KLogE (Gen.Kspan I b) lemniscatic,
      c * varpi / Real.pi * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Gen.Kspan I b → a₁ ∈ Gen.Kspan I b → a₂ ∈ Gen.Kspan I b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False :=
  Gen.mg_K Gen.latI hW hg₂ g₃_lemniscatic_isAlgebraic
    (CM4E.Ext.Bridge.transcendental_varpi_div_pi lemniscatic rfl rfl) hb c hcK hc0 hIK x hx hsx hind

/-- **Theorem MG♮, `K`-form, for `Ω = ϖ`**: for `s = 1/(cϖ)` and `K = span_ℚ θ ∋ c` with `[K : ℚ] ≥ 4`, there are no
`x₁, x₂ ∈ K𝓛` with `sx₁, sx₂ ∈ K𝓛 + K·(fibre values)` and `2πi, x₁, x₂` linearly independent over `K`. Assumes only
W88 §5d (`Gen.Thm11KappaMGnK Gen.latI`). -/
theorem mgn_K_varpi (hW : Gen.Thm11KappaMGnK Gen.latI) {r : ℕ} {b : Fin r → ℂ}
    (hb : Gen.IsAdaptedFieldBasis I b) (hr : 2 ≤ r) (c : ℂ) (hcK : c ∈ Gen.Kspan I b) (hc0 : c ≠ 0)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ Gen.KLog (Gen.Kspan I b))
    (hsx : ∀ k, ∃ y ∈ Gen.KLog (Gen.Kspan I b), ∃ e ∈ Gen.KFib (Gen.Kspan I b) Gen.latI,
      (c * varpi)⁻¹ * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Gen.Kspan I b → a₁ ∈ Gen.Kspan I b → a₂ ∈ Gen.Kspan I b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False :=
  Gen.mgn_K Gen.latI hW Gen.kappaOneZero_latI hg₂ g₃_lemniscatic_isAlgebraic hT hb hr c hcK hc0 x hx hsx hind

end CM4E.Final
