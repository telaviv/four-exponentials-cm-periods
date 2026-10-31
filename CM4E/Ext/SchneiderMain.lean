/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import CM4E.Ext.Schneider
import CM4E.Ext.SchneiderLang.Main
import CM4E.Ext.Weierstrass.OrderTwo
import CM4E.Ext.SchneiderWp

/-!
# Schneider's theorem on elliptic periods (unconditional)

For a lattice `Λ` whose Weierstrass invariants `g₂, g₃` are algebraic, every nonzero period `ω`
satisfies: `ω` is transcendental, and `ω / π` is transcendental (Schneider 1937).

The conditional versions are in `CM4E.Ext/Schneider.lean`; here the two hypotheses are discharged by
the Schneider–Lang criterion `CM4E.Ext.schneiderLang` and the order-two representation of `℘`, `℘'`
by the Weierstrass σ function, `CM4E.Ext.Weierstrass.weierstrassOrderTwo`.
-/

open Complex

namespace CM4E.Ext.Schneider

variable {L : PeriodPair}

/-- **Schneider.** A nonzero period of a lattice with algebraic `g₂, g₃` is transcendental. -/
theorem period_transcendental (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {ω : ℂ}
    (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) : Transcendental ℚ ω :=
  period_transcendental_of CM4E.Ext.schneiderLang (CM4E.Ext.Weierstrass.weierstrassOrderTwo L) hg₂ hg₃ hω h0

/-- **Schneider.** For a nonzero period `ω` of a lattice with algebraic `g₂, g₃`, `ω / π` is
transcendental. -/
theorem period_div_pi_transcendental (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃)
    {ω : ℂ} (hω : ω ∈ L.lattice) (h0 : ω ≠ 0) : Transcendental ℚ (ω / (Real.pi : ℂ)) :=
  period_div_pi_transcendental_of CM4E.Ext.schneiderLang (CM4E.Ext.Weierstrass.weierstrassOrderTwo L) hg₂ hg₃
    hω h0

end CM4E.Ext.Schneider

namespace CM4E.Ext.Schneider

variable {L : PeriodPair}

/-- **Schneider.** If `g₂, g₃` are algebraic and `α ∉ Λ` is algebraic, then `℘(α)` is
transcendental. -/
theorem wp_transcendental (hg₂ : IsAlgebraic ℚ L.g₂) (hg₃ : IsAlgebraic ℚ L.g₃) {α : ℂ}
    (hα : IsAlgebraic ℚ α) (hαΛ : α ∉ L.lattice) : Transcendental ℚ (L.weierstrassP α) :=
  wp_transcendental_of CM4E.Ext.schneiderLang (CM4E.Ext.Weierstrass.weierstrassOrderTwo L) hg₂ hg₃ hα hαΛ

end CM4E.Ext.Schneider
