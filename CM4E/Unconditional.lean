/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CM4E.Final
import CM4E.Bridge.Results
import CM4E.Bridge.M
import CM4E.Bridge.Vec
import LSG.W88.Main
import LSG.W88.K5dMain

/-!
# Unconditional results: W88 discharged by `lean_lsg`

The sibling project `lean_lsg` (Lake path dependency `../lean_lsg`) proves Waldschmidt's subgroup theorem with period
term (W88, Thm 4.1, under (NR)) for `G_a^{d₀} × G_m^{d₁} × E₁ × ⋯ × E_m` (`LSG.W88.theorem41Abelian`) and deduces from it
the §5d statement for `G_m^{d₁} × E`, verbatim our hypothesis `Thm11Kappa` (`LSG.W88.thm11Kappa`, stated for a verbatim
copy `LSG.W88.MStarCopy.Thm11Kappa` of `CM4E.Waldschmidt.Thm11Kappa`; the two unfold to the same term). Hence the
results that need only `Thm11Kappa lemniscatic 4` hold with **no hypotheses**:

* `fourExpAt_Qi`: the four exponentials statement at `t = ((p + qi)/D)·ϖ/π` for every `p + qi ∈ ℚ(i)ˣ`;
* `two_three`: `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic.

`lean_lsg` also proves the §5d statement for the standard model of `G_a^{d₀} × G_m^{d₁} × E^r`, one curve repeated, for
every period pair with algebraic invariants (`LSG.W88.hypStdCMAt`, stated for a verbatim copy of our
`CM4E.Bridge.HypStdCMAt`). Through the bridges of `CM4E/Bridge/` (proved) this gives, with no form of W88 assumed:

* `fourExpAt_varpi_div_pi_all`: **Theorem 1(b) for `Ω = ϖ`**: `FourExpAt (cϖ/π)` for every algebraic `c ≠ 0`
  (e.g. `2^{cϖ/π}, 3^{cϖ/π}` are not both algebraic);
* `fourExpAt_omegaRho_div_pi_all`: Theorem 1(b) for `Ω = Ω_ρ`, assuming only that `g₃(Ω_ρℤ[ρ])` is algebraic;
* `mg1_varpi_abc`: Corollary MG1 (one of `e^{aπ²}, e^{bπϖ}, e^{cπ²/ϖ}` is transcendental), assuming the named input
  `Gen.NotLtilde Gen.latI` (Wüstholz);
* `mg3_varpi`: Corollary MG3, assuming Baker's theorem (`Gen.Baker3`).

With the arithmetic of elliptic logarithms (`CM4E/Bridge/ELog.lean`: addition law, complex multiplication by `i` and
`ρ`) the models with elliptic logarithms reduce to the same statement (`Bridge.thm11KappaM_of_std`,
`Bridge.thm11KappaMGK_of_std`), so with no form of W88 assumed:

* `thmM_varpi`, `thmM_omegaRho`: **Theorem M** for `Ω = cϖ` (and for `cΩ_ρ`, given `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`);
* `m1_varpi`: (M1) `℘(cϖ/π) ∉ ℚ̄`; `m3_varpi`: (M3); `m3'_varpi`: (M3′) given Hermite–Lindemann;
* `thmM_varpi_k`, `meta_varpi`: Theorem M with `s ∈ ℚ(i)` and (Mη), given Masser's theorem (`Gen.MasserCM`);
* `mg_K_varpi`: the `K`-form of Theorem MG for `Ω = ϖ`.

`lean_lsg` also proves the vector-extension hypotheses (`Bridge.thm11KappaMXG_uncond`, `Bridge.thm11KappaMGn_uncond`,
`Bridge.thm11KappaMGnK_uncond`, `Bridge.thm11KappaNat_uncond`), so with no form of W88 assumed:

* `fourExpAt_varpi`, `two_three_varpi`, `fourExpAt_varpi_all`: **Theorem 1(a)** for `Ω = ϖ` (`2^ϖ, 3^ϖ` not both
  algebraic; `FourExpAt (cϖ)` for every algebraic `c ≠ 0`); `fourExpAt_omegaRho_all`, `two_three_omegaRho` for `Ω_ρ`
  (only `hg₃'`);
* `mgn_K_varpi`: the `K`-form of Theorem MG♮;
* `mx_K`, `mx`, `mx1`, `deg2_ii`: Theorem MX (`K`-form and full), Cor. MX1, deg2 (ii), with their named inputs;
* `thmS_varpi`, `thmS_omegaRho`: **Theorem S** of paper [II], assuming only `Gen.NotLtilde` (Wüstholz) (and `hg₃'`).
-/

open Complex CM4E.Waldschmidt

namespace CM4E.Unconditional

/-- **W88 §5d for `G_m^{d₁} × E`**, proved in `lean_lsg`. -/
theorem thm11Kappa (L : PeriodPair) (d₁ : ℕ) : Thm11Kappa L d₁ :=
  LSG.W88.thm11Kappa L d₁

/-- **Theorem 1(b) for `c ∈ ℚ(i)ˣ`, unconditionally**: `FourExpAt (((p + qi)/D)·ϖ/π)`. -/
theorem fourExpAt_Qi (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) : FourExpAt (MainQi.tExp p q D) :=
  Final.fourExpAt_Qi (thm11Kappa lemniscatic 4) p q D hD hpq

/-- **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic** (no hypotheses). -/
theorem two_three :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi / Real.pi : ℂ) * Complex.log 3))) :=
  Final.two_three (thm11Kappa lemniscatic 4)

/-- W88 §5d for `G_a^{d₀} × G_m^{d₁} × E^r` (one curve repeated), proved in `lean_lsg`. -/
theorem hypStdCMAt (L : PeriodPair) (d : ℕ) : Bridge.HypStdCMAt L d :=
  LSG.W88.hypStdCMAt L d

/-- **Theorem 1(b) for `Ω = ϖ` and every algebraic `c ≠ 0`, unconditionally**: `FourExpAt (cϖ/π)`. -/
theorem fourExpAt_varpi_div_pi_all (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * varpi / Real.pi) :=
  Bridge.fourExpAt_varpi_div_pi_all (hypStdCMAt lemniscatic 0) c hc hc0

/-- **Theorem 1(b) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄` (`g₂ = 0` is
proved, `MX.g₂_equianharmonic`). -/
theorem fourExpAt_omegaRho_div_pi_all (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * omegaRho / Real.pi) :=
  Bridge.fourExpAt_omegaRho_div_pi_all (hypStdCMAt MX.equianharmonic 0) hg₃' c hc hc0

/-- **Corollary MG1 for `ϖ`**: one of `e^{aπ²}, e^{bπϖ}, e^{cπ²/ϖ}` is transcendental (`a, b, c ∈ ℚ̄ˣ`), assuming only
the named input `Gen.NotLtilde Gen.latI` (Wüstholz 1989). -/
theorem mg1_varpi_abc (hNot : Gen.NotLtilde Gen.latI) (a b c : ℂ) (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0)
    (hb : IsAlgebraic ℚ b) (hb0 : b ≠ 0) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    ¬ (IsAlgebraic ℚ (Complex.exp (a * Real.pi ^ 2)) ∧ IsAlgebraic ℚ (Complex.exp (b * Real.pi * varpi)) ∧
      IsAlgebraic ℚ (Complex.exp (c * Real.pi ^ 2 / varpi))) :=
  Bridge.mg1_varpi_abc (hypStdCMAt lemniscatic 2) hNot a b c ha ha0 hb hb0 hc hc0

/-- **Corollary MG3 for `ϖ`**, assuming only Baker's theorem. -/
theorem mg3_varpi (hBaker : Gen.Baker3) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2)))
    (hπω : IsAlgebraic ℚ (Complex.exp (c * Real.pi * varpi))) (x : ℂ) (hx : IsAlgebraic ℚ (Complex.exp x))
    (hind : LinearIndependent ℚ ![2 * (Real.pi : ℂ) * I, (Real.pi : ℂ) ^ 2, x]) :
    Transcendental ℚ (Complex.exp (varpi / Real.pi * x)) :=
  Bridge.mg3_varpi (hypStdCMAt lemniscatic 2) hBaker c hc hc0 hπ2 hπω x hx hind

/-- W88 §5d for `A'' × G_m^n × G_a` over `ϖℤ[i]` (Theorem M's hypothesis). -/
theorem thm11KappaM_latI : Gen.Thm11KappaM Gen.latI :=
  Bridge.thm11KappaM_of_std Gen.latI (hypStdCMAt lemniscatic 1) Bridge.int_I Bridge.cmMulLogE_latI

/-- W88 §5d for `A'' × G_m^n × G_a` over `Ω_ρℤ[ρ]`. -/
theorem thm11KappaM_latRho : Gen.Thm11KappaM Gen.latRho :=
  Bridge.thm11KappaM_of_std Gen.latRho (hypStdCMAt MX.equianharmonic 1) Bridge.int_rho Bridge.cmMulLogE_latRho

/-- W88 §5d for `G_m^{2n} × A''` with elliptic logarithms over `ϖℤ[i]` (the `K`-form of Theorem MG). -/
theorem thm11KappaMGK_latI : Gen.Thm11KappaMGK Gen.latI :=
  Bridge.thm11KappaMGK_of_std Gen.latI (hypStdCMAt lemniscatic 0) Bridge.int_I Bridge.cmMulLogE_latI

/-- **Theorem M for `Ω = cϖ`, unconditionally**: if `u ∈ ℚ̄𝓛_{E_i}`, `ℓ ∈ 𝓛̃` and `iπu = cϖℓ` (`c ∈ ℚ̄ˣ`), then
`u = s·cϖ`, `ℓ = s·iπ` with `s ∈ ℚ̄`. -/
theorem thmM_varpi (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (u ℓ : ℂ)
    (hu : u ∈ Gen.QbarLogE lemniscatic) (hℓ : ℓ ∈ Gen.Ltilde) (hrel : I * Real.pi * u = c * varpi * ℓ) :
    ∃ s : ℂ, IsAlgebraic ℚ s ∧ u = s * (c * varpi) ∧ ℓ = s * (I * Real.pi) :=
  Final.thmM_varpi thm11KappaM_latI c hc hc0 u ℓ hu hℓ hrel

/-- **Theorem M for `Ω = cΩ_ρ`**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`. -/
theorem thmM_omegaRho (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (u ℓ : ℂ) (hu : u ∈ Gen.QbarLogE MX.equianharmonic) (hℓ : ℓ ∈ Gen.Ltilde)
    (hrel : I * Real.pi * u = c * omegaRho * ℓ) :
    ∃ s : ℂ, IsAlgebraic ℚ s ∧ u = s * (c * omegaRho) ∧ ℓ = s * (I * Real.pi) :=
  Final.thmM_omegaRho thm11KappaM_latRho hg₃' c hc hc0 u ℓ hu hℓ hrel

/-- **(M1), unconditionally**: `℘(cϖ/π) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`. -/
theorem m1_varpi (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    Transcendental ℚ (lemniscatic.weierstrassP (c * varpi / Real.pi)) :=
  Final.m1_varpi thm11KappaM_latI c hc hc0

/-- **(M3), unconditionally**: if `e^{π²} ∈ ℚ̄` then `℘(cπϖ) ∉ ℚ̄` for `c ∈ ℚ̄ˣ`. -/
theorem m3_varpi (hπ2 : IsAlgebraic ℚ (Complex.exp ((Real.pi : ℂ) ^ 2))) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) : Transcendental ℚ (lemniscatic.weierstrassP (c * Real.pi * varpi)) :=
  Final.m3_varpi thm11KappaM_latI hπ2 c hc hc0

/-- **(M3′)** For `α = e^z ∈ ℚ̄ \ {0, 1}`, one of `e^{iπz}`, `℘(ϖz)` is transcendental; assuming only
Hermite–Lindemann. -/
theorem m3'_varpi (hHL : Gen.HermiteLindemann) (z : ℂ) (hz : IsAlgebraic ℚ (Complex.exp z))
    (hz1 : Complex.exp z ≠ 1) :
    ¬ (IsAlgebraic ℚ (Complex.exp (I * Real.pi * z)) ∧ IsAlgebraic ℚ (lemniscatic.weierstrassP (varpi * z))) :=
  Final.m3'_varpi thm11KappaM_latI hHL z hz hz1

/-- **Theorem M on `E_i` with `s ∈ ℚ(i)`**, assuming only Masser's theorem. -/
theorem thmM_varpi_k (hMa : Gen.MasserCM) (u ℓ : ℂ) (hu : Gen.LogE lemniscatic u) (hℓ : ℓ ∈ Gen.Ltilde)
    (hrel : I * Real.pi * u = varpi * ℓ) :
    ∃ p q : ℚ, u = (p + q * I) * varpi ∧ ℓ = (p + q * I) * (I * Real.pi) :=
  Final.thmM_varpi_k thm11KappaM_latI hMa u ℓ hu hℓ hrel

/-- **(Mη)** `η(ϖ)u ∉ 𝓛̃` for `u ∈ 𝓛_{E_i} \ ℚ(i)ϖ`, assuming only Masser's theorem. -/
theorem meta_varpi (hMa : Gen.MasserCM) (u : ℂ) (hu : Gen.LogE lemniscatic u)
    (hnot : ¬ ∃ p q : ℚ, u = (p + q * I) * varpi) : (Real.pi / varpi : ℂ) * u ∉ Gen.Ltilde :=
  Final.meta_varpi thm11KappaM_latI hMa u hu hnot

/-- **Theorem MG, `K`-form, for `Ω = ϖ`, unconditionally**: for `s = cϖ/π` and `K = span_ℚ θ ∋ i, c` there are no
`x₁, x₂ ∈ K𝓛` with `sx₁, sx₂ ∈ K𝓛 + K𝓛_E` and `2πi, x₁, x₂` linearly independent over `K`. -/
theorem mg_K_varpi {r : ℕ} {b : Fin r → ℂ} (hb : Gen.IsAdaptedFieldBasis I b)
    (c : ℂ) (hcK : c ∈ Gen.Kspan I b) (hc0 : c ≠ 0) (hIK : I ∈ Gen.Kspan I b)
    (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ Gen.KLog (Gen.Kspan I b))
    (hsx : ∀ k, ∃ y ∈ Gen.KLog (Gen.Kspan I b), ∃ e ∈ Gen.KLogE (Gen.Kspan I b) lemniscatic,
      c * varpi / Real.pi * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Gen.Kspan I b → a₁ ∈ Gen.Kspan I b → a₂ ∈ Gen.Kspan I b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) : False :=
  Final.mg_K_varpi thm11KappaMGK_latI hb c hcK hc0 hIK x hx hsx hind

/-- **Theorem 1(a) for `c ∈ ℚ(i)ˣ`, unconditionally**: four exponentials at `t = Dϖ/(p + qi)`. -/
theorem fourExpAt_varpi (p q : ℤ) (D : ℕ) (hD : 0 < D) (hpq : p ≠ 0 ∨ q ≠ 0) :
    FourExpAt (MainNat.tN p q D) :=
  Final.fourExpAt_varpi Bridge.thm11KappaNat_uncond p q D hD hpq

/-- **`2^ϖ` and `3^ϖ` are not both algebraic** (no hypotheses). -/
theorem two_three_varpi :
    ¬ (IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((varpi : ℂ) * Complex.log 3))) :=
  Final.two_three_varpi Bridge.thm11KappaNat_uncond

/-- **Theorem 1(a) for `Ω = ϖ` and every algebraic `c ≠ 0`, unconditionally**: `FourExpAt (cϖ)`. -/
theorem fourExpAt_varpi_all (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) :
    FourExpAt (c * varpi) :=
  Final.fourExpAt_varpi_all (Bridge.thm11KappaMGn_uncond Gen.latI) c hc hc0

/-- **Theorem 1(a) for `Ω = Ω_ρ` and every algebraic `c ≠ 0`**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`. -/
theorem fourExpAt_omegaRho_all (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (c : ℂ) (hc : IsAlgebraic ℚ c)
    (hc0 : c ≠ 0) :
    FourExpAt (c * omegaRho) :=
  Final.fourExpAt_omegaRho_all (Bridge.thm11KappaMGn_uncond Gen.latRho) hg₃' c hc hc0

/-- **`2^{Ω_ρ}` and `3^{Ω_ρ}` are not both algebraic**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`. -/
theorem two_three_omegaRho (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) :
    ¬ (IsAlgebraic ℚ (Complex.exp ((omegaRho : ℂ) * Complex.log 2)) ∧
        IsAlgebraic ℚ (Complex.exp ((omegaRho : ℂ) * Complex.log 3))) :=
  Final.two_three_omegaRho (Bridge.thm11KappaMGn_uncond Gen.latRho) hg₃'

/-- **Theorem MG♮, `K`-form, for `Ω = ϖ`, unconditionally**: for `s = 1/(cϖ)` and `K = span_ℚ θ ∋ c` with
`[K : ℚ] ≥ 4`, no `x₁, x₂ ∈ K𝓛` with `sx_j ∈ K𝓛 + K·(fibre values)` and `2πi, x₁, x₂` `K`-independent. -/
theorem mgn_K_varpi {r : ℕ} {b : Fin r → ℂ} (hb : Gen.IsAdaptedFieldBasis I b) (hr : 2 ≤ r) (c : ℂ)
    (hcK : c ∈ Gen.Kspan I b) (hc0 : c ≠ 0) (x : Fin 2 → ℂ) (hx : ∀ k, x k ∈ Gen.KLog (Gen.Kspan I b))
    (hsx : ∀ k, ∃ y ∈ Gen.KLog (Gen.Kspan I b), ∃ e ∈ Gen.KFib (Gen.Kspan I b) Gen.latI,
      (c * varpi)⁻¹ * x k = y + e)
    (hind : ∀ a₀ a₁ a₂ : ℂ, a₀ ∈ Gen.Kspan I b → a₁ ∈ Gen.Kspan I b → a₂ ∈ Gen.Kspan I b →
      a₀ * (2 * Real.pi * I) + a₁ * x 0 + a₂ * x 1 = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    False :=
  Final.mgn_K_varpi (Bridge.thm11KappaMGnK_uncond Gen.latI) hb hr c hcK hc0 x hx hsx hind

/-- **Theorem MX, `K`-form, for every `β ∈ ℚ̄ˣ`**, assuming only `hg₃'`, `hΓ`, `hM`. -/
theorem mx_K (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hM : Transcendental ℚ ((omegaRho : ℂ) / varpi)) (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0)
    (zX wX zY wY a t : ℂ) (hX : MX.LogNat lemniscatic etaLem zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t) (hrel : (zX + zY + a) * (β * MX.etaRho) = (wX + wY + t) * varpi) :
    ∃ x x' : ℂ, IsAlgebraic ℚ x ∧ IsAlgebraic ℚ x' ∧ zX + zY + a = x * varpi + x' * omegaRho :=
  Final.mx_K Bridge.thm11KappaMXG_uncond hg₃' hΓ hM β hβ hβ0 zX wX zY wY a t hX hY ha ht hrel

/-- **Theorem MX** for every `β ∈ ℚ̄ˣ`, assuming only `hg₃'`, `hΓ` and the named inputs `WuestholzMX`, `MasserCM`. -/
theorem mx (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hWu : Gen.WuestholzMX) (hMa : Gen.MasserCM) (β : ℂ) (hβ : IsAlgebraic ℚ β) (hβ0 : β ≠ 0) (zX wX zY wY a t : ℂ)
    (hX : MX.LogNat lemniscatic etaLem zX wX) (hY : MX.LogNat MX.equianharmonic MX.etaR zY wY)
    (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t) (hrel : (zX + zY + a) * (β * MX.etaRho) = (wX + wY + t) * varpi) :
    a = 0 ∧ (∃ p q : ℚ, zX = (p + q * I) * varpi) ∧ (∃ p q : ℚ, zY = (p + q * MX.rho) * omegaRho) :=
  Final.mx Bridge.thm11KappaMXG_uncond hg₃' hΓ hWu hMa β hβ hβ0 zX wX zY wY a t hX hY ha ht hrel

/-- **Corollary MX1**, assuming only `hg₃'`, `hΓ` and the named inputs `WuestholzMX`, `MasserCM`, `LaurentZeta`. -/
theorem mx1 (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi))
    (hWu : Gen.WuestholzMX) (hMa : Gen.MasserCM) (hLa : Gen.LaurentZeta) (u : ℂ)
    (hwp : IsAlgebraic ℚ (lemniscatic.weierstrassP u)) (hwp' : IsAlgebraic ℚ (lemniscatic.derivWeierstrassP u))
    (hu' : ¬ ∃ p q : ℚ, u = (p + q * I) * varpi) (a t : ℂ) (ha : IsAlgebraic ℚ a) (ht : IsAlgebraic ℚ t) :
    Transcendental ℚ ((varpi : ℂ) * omegaRho * (CM4E.Ext.Weierstrass.zeta lemniscatic u + t) /
      (Real.pi * (u + a))) :=
  Final.mx1 Bridge.thm11KappaMXG_uncond hg₃' hΓ hWu hMa hLa u hwp hwp' hu' a t ha ht

/-- **Corollary deg2 (ii)**: `1, ϖ, Ω_ρ, ϖΩ_ρ/π` are `ℚ̄`-independent, assuming only `hg₃'`, `hΓ` and the named
input `WuestholzSix`. -/
theorem deg2_ii (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃)
    (hΓ : Transcendental ℚ ((varpi : ℂ) * omegaRho / Real.pi)) (h6 : Gen.WuestholzSix) (c0 c1 c2 c3 : ℂ)
    (h0 : IsAlgebraic ℚ c0) (h1 : IsAlgebraic ℚ c1) (h2 : IsAlgebraic ℚ c2) (h3 : IsAlgebraic ℚ c3)
    (hrel : c0 + c1 * varpi + c2 * omegaRho + c3 * (varpi * omegaRho / Real.pi) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 :=
  Final.deg2_ii Bridge.thm11KappaMXG_uncond hg₃' hΓ h6 c0 c1 c2 c3 h0 h1 h2 h3 hrel

/-- **Theorem S for `Ω = ϖ`** (paper [II]): for `t ∈ ℚ̄ˣϖ ∪ ℚ̄ˣ/ϖ ∪ ℚ̄ˣϖ/π ∪ ℚ̄ˣπ/ϖ` and `ℚ̄`-independent `y₁, y₂`, the
numbers `y₁, y₂, ty₁, ty₂` are not all in `𝓛̃ = ℚ̄ + ℚ̄𝓛`; assuming only `Gen.NotLtilde Gen.latI` (Wüstholz). -/
theorem thmS_varpi (hNot : Gen.NotLtilde Gen.latI) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (t : ℂ)
    (ht : t = c * varpi ∨ t = c / varpi ∨ t = c * varpi / Real.pi ∨ t = c * Real.pi / varpi)
    (y₁ y₂ : ℂ) (hind : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * y₁ + a₂ * y₂ = 0 →
      a₁ = 0 ∧ a₂ = 0) :
    ¬ (y₁ ∈ Gen.Ltilde ∧ y₂ ∈ Gen.Ltilde ∧ t * y₁ ∈ Gen.Ltilde ∧ t * y₂ ∈ Gen.Ltilde) :=
  Final.thmS_varpi (Bridge.thm11KappaSMG_of_std Gen.latI (hypStdCMAt lemniscatic 2) Bridge.int_I)
    (Bridge.thm11KappaSMGn_uncond Gen.latI) hNot c hc hc0 t ht y₁ y₂ hind

/-- **Theorem S for `Ω = Ω_ρ`**, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄` and `Gen.NotLtilde Gen.latRho`. -/
theorem thmS_omegaRho (hg₃' : IsAlgebraic ℚ MX.equianharmonic.g₃) (hNot : Gen.NotLtilde Gen.latRho) (c : ℂ)
    (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (t : ℂ)
    (ht : t = c * omegaRho ∨ t = c / omegaRho ∨ t = c * omegaRho / Real.pi ∨ t = c * Real.pi / omegaRho)
    (y₁ y₂ : ℂ) (hind : ∀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ → a₁ * y₁ + a₂ * y₂ = 0 →
      a₁ = 0 ∧ a₂ = 0) :
    ¬ (y₁ ∈ Gen.Ltilde ∧ y₂ ∈ Gen.Ltilde ∧ t * y₁ ∈ Gen.Ltilde ∧ t * y₂ ∈ Gen.Ltilde) :=
  Final.thmS_omegaRho (Bridge.thm11KappaSMG_of_std Gen.latRho (hypStdCMAt MX.equianharmonic 2) Bridge.int_rho)
    (Bridge.thm11KappaSMGn_uncond Gen.latRho) hg₃' hNot c hc hc0 t ht y₁ y₂ hind

end CM4E.Unconditional
