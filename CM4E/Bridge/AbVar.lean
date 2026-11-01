/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import CM4E.AbVar.ThmA
import CM4E.AbVar.CorA2
import LSG.W88.AbVarFinal

/-!
# The abelian-variety hypotheses at `y⁵ = x(1 − x)` from `lean_lsg`

`lean_lsg` (M1, commit 483e2b0) proves verbatim copies of `AbVar.Thm11KappaA 5 2 (·+1) perA5 0` and
`AbVar.Thm11KappaAK 5 2 (·+1) perA5 0 ∅` (`LSG.W88.thm11KappaA5`, `LSG.W88.thm11KappaAK5`) from its W88 §5d theorem
for `G_a^{d₀} × G_m^{d₁} × A^r` on toric-injective hyperplanes, with data whose `A`-components are periods
(`LSG.W88.hyperplaneKappaAbVar`; `A` is the torus of the period lattice of `Y² = 4X⁵ + 1`, classically `Jac(y⁵ = x(1 − x))`;
lean_lsg `REVIEW_STATEMENT_ABVAR.md`: no FATAL or MAJOR issues).
The copies use a separate `IsAdaptedBasisD` structure, repackaged here. Consequences, with no hypothesis:
Wüstholz's input `WuestholzA5`, Theorem MG-A at `B(1/5, 1/5)/π` and at `π/B(1/5, 1/5)`, its `K`-form with `LA = ∅`, and
the `2^t, 3^t` example.
Corollary A2 at `B(1/5, 1/5)` keeps its named input `NotLtildeA (perA5 0)`.
-/

namespace CM4E.Bridge

open CM4E.AbVar CM4E.Gen

/-- **`Thm11KappaA` at `y⁵ = x(1 − x)`**, unconditionally (`lean_lsg`). -/
theorem thm11KappaA5_uncond : Thm11KappaA 5 2 (fun s => (s : ℕ) + 1) perA5 0 := fun r b hb =>
  LSG.W88.thm11KappaA5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`Thm11KappaAK` (with `LA = ∅`) at `y⁵ = x(1 − x)`**, unconditionally (`lean_lsg`). -/
theorem thm11KappaAK5_uncond : Thm11KappaAK 5 2 (fun s => (s : ℕ) + 1) perA5 0 ∅ := fun r b hb =>
  LSG.W88.thm11KappaAK5 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`P₁/π ∉ ℚ̄` at `y⁵ = x(1 − x)`** (`WuestholzA5`), unconditionally. -/
theorem wuestholzA5_uncond : WuestholzA5 := wuestholzA5_of thm11KappaA5_uncond

/-- **Theorem MG-A at `B(1/5, 1/5)`**, unconditionally: `FourExpAt (c B(1/5, 1/5)/π)` for algebraic `c ≠ 0`. -/
theorem fourExpAt_beta5_uncond (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * Complex.betaIntegral (1 / 5) (1 / 5) / Real.pi) :=
  fourExpAt_beta5 thm11KappaA5_uncond c hc hc0

/-- **Theorem MG-A, inverted family**, unconditionally: `FourExpAt (cπ/B(1/5, 1/5))`. -/
theorem fourExpAt_pi_div_beta5_uncond (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * Real.pi / Complex.betaIntegral (1 / 5) (1 / 5)) :=
  fourExpAt_pi_div_beta5 thm11KappaA5_uncond c hc hc0

/-- **`2^t` and `3^t` are not both algebraic at `t = B(1/5, 1/5)/π`**, unconditionally. -/
theorem two_three_beta5_uncond :
    ¬ (IsAlgebraic ℚ (Complex.exp (Complex.betaIntegral (1 / 5) (1 / 5) / Real.pi * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp (Complex.betaIntegral (1 / 5) (1 / 5) / Real.pi * Complex.log 3))) :=
  two_three_beta5 thm11KappaA5_uncond

/-- **Theorem MG-A, `K`-form, at `P = (1 − ζ₅)B(1/5, 1/5)`**, unconditionally, with `z_σ(Λ(A))` replaced by `ℤP`
(`LA = ∅`): for `s = cP/π` and an adapted number field `K ∋ c, i`, no two logarithms `x₀, x₁ ∈ K𝓛`, `K`-independent
together with `2πi`, satisfy `s x_k ∈ K𝓛 + KP`. -/
theorem mgA5_K_uncond {r : ℕ} {b : Fin r → ℂ} (hb : IsAdaptedBasisD (zetaN 5) (Nat.totient 5) b)
    (c : ℂ) (hcK : c ∈ KspanD (zetaN 5) (Nat.totient 5) b) (hc0 : c ≠ 0)
    (hIK : Complex.I ∈ KspanD (zetaN 5) (Nat.totient 5) b)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ KLog (KspanD (zetaN 5) (Nat.totient 5) b))
    (hsx : ∀ k, ∃ y ∈ KLog (KspanD (zetaN 5) (Nat.totient 5) b),
      ∃ e ∈ KSlotA 2 perA5 0 ∅ (KspanD (zetaN 5) (Nat.totient 5) b), c * perA5 0 / Real.pi * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ KspanD (zetaN 5) (Nat.totient 5) b → a₁ ∈ KspanD (zetaN 5) (Nat.totient 5) b →
      a₂ ∈ KspanD (zetaN 5) (Nat.totient 5) b →
      a₀ * (2 * Real.pi * Complex.I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False :=
  mgA_K (LA := ∅) (by norm_num) thm11KappaAK5_uncond (by decide) rfl (by decide) wuestholzA5_uncond hb c hcK hc0
    hIK x hx hsx hind

/-- **Corollary A2 at `B(1/5, 1/5)`**, with only the named input `NotLtildeA (perA5 0)`: one of `e^{aπ²}`,
`e^{bπB(1/5,1/5)}`, `e^{cπ²/B(1/5,1/5)}` is transcendental (`a, b, c ∈ ℚ̄ˣ`). -/
theorem corA2_beta5_uncond (hNot : NotLtildeA (perA5 0)) (a b c : ℂ) (ha : IsAlgebraic ℚ a)
    (hb : IsAlgebraic ℚ b) (hc : IsAlgebraic ℚ c) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧
      IsAlgebraic ℚ (Complex.exp (b * (Real.pi * Complex.betaIntegral (1 / 5) (1 / 5)))) ∧
      IsAlgebraic ℚ (Complex.exp (c * (Real.pi ^ 2 / Complex.betaIntegral (1 / 5) (1 / 5))))) :=
  corA2_beta5 thm11KappaAK5_uncond hNot a b c ha hb hc ha0 hb0 hc0

end CM4E.Bridge
