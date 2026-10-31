# CM4E blueprint: a Lean proof of "four exponentials at CM periods"

Library name `CM4E` (project folder renamed `lean_mstar/` on 2026-10-30; scope: all M* results, see TRUST.md §4).
Paper: `../schanuel/five_exp/pilot_thmM/paper/paper.tex` (16 pp.). This project aims at a complete Lean 4 + Mathlib
proof of its Theorem 1 using only the standard axioms. Theorems MG, MG♮, MX and MX′ come later. Status labels:
✔ proved in Lean · ◐ partly · ☐ open · ✱ reusable from elsewhere.

## 0. Targets (fixed; `CM4E/Defs.lean`)

| target | statement | first route |
|---|---|---|
| `Target.fourExp_varpi_div_pi` | 4E at t = cϖ/π (e.g. 2^{ϖ/π}, 3^{ϖ/π}) | Theorem MG on G_m⁴ × E_i, K = Q(i) (only ℘ needed) |
| `Target.fourExp_varpi` | 4E at t = cϖ (2^ϖ, 3^ϖ) | Theorem MG♮ (needs E^♮, i.e. ζ and quasi-periods) |
| `Target.mg1_varpi` | one of e^{π²}, e^{πϖ}, e^{π²/ϖ} | Theorem MG (K-version) + `Ω ∉ ℚ̄𝓛`, `Ω/π ∉ ℚ̄` (no Chudnovsky since paper Rev. 6) |
| `…omegaRho…` | the same for E_ρ | same, with Q(ρ) |

**Status 2026-10-30:** the first milestone is proved **conditionally**: `CM4E.TwoThree.two_three` says 2^{ϖ/π} and
3^{ϖ/π} are not both algebraic, assuming H1–H3 below. It uses the standard axioms only. The independent fidelity
check of H1 is `REFEREE_HYP.md`.

**Recommended first milestone:** `fourExp_varpi_div_pi` for c ∈ Q(i).
* Take K = Q(i), so n = 2. Theorem MG's count closes for every even n, and then G″ = G_m⁴ × A″ with A″ ≅ E_i (one
  elliptic factor).
* So the whole transcendence input is one instance of Waldschmidt's theorem on **G_m⁴ × E_i** with periods. That is
  the smallest group containing the mechanism.
* General algebraic c needs larger K (A″ of dimension n/2). Only N2 needs to cover E^{d₂}.

## 1. Dependency graph

```
Defs ✔ ──────────────────────────────────────────────────────────────┐
N1  ℘ for ϖℤ[i]: g₂ = 4, g₃ = 0, ℘(iz) = −℘(z), algebraic values     │
    at Q(i)-torsion, uniformisation ℂ/Λ → E(ℂ) a group hom          │
N2  Waldschmidt's theorem on G_m^{d₁} × E^{d₂} (E CM) with periods ──┤──► N7  MG dimension bound
     N2a auxiliary function / interpolation determinant               │       (Roy-form statement,
     N2b heights of ℘ at multiples (division polynomials)            │        case check ✔)
     N2c growth of ℘ (order 2; via Jacobi theta)                     │
     N2d Schwarz lemma ✱ (StrongSix), Liouville ✱ (StrongSix)          │
     N2e multiplicity estimate on G_m^{d₁} × E^{d₂}  ← bottleneck     │
N3  K-structure: G² → G″ = G_m⁴ × E_i explicitly (Weil restriction)  │
N4  subgroups of G_m⁴ × E_i: T_L × B, B ∈ {0, E} (Roy's linear form)  │
N5  Baker: Q-independent logs are Q̄-independent ✱ (from StrongSix    │
    waldschmidtTheorem1, W88 Cor 3.3 route)                           │
N6  Ω/π ∉ Q̄, Ω ∉ Q̄𝓛 (Schneider-type; instances of N2)              │
N7 + N5 + N6 ──► Theorem 1(b) at ϖ ──► Target.fourExp_varpi_div_pi ◄─┘
N8  E^♮: Weierstrass ζ, quasi-periods, Legendre ϖη(ϖ) = π, CM action on fibre ──► MG♮ ──► Target.fourExp_varpi
```

## 2. Node status

| node | content | status | notes / reuse |
|---|---|---|---|
| Defs | target statements | ✔ | elementary; no elliptic curves in the statements |
| **Conditional main theorem** | 4E at t = cϖ/π, c ∈ Q(i)^×, with 2πi, a, b Q-independent; headline 2^{ϖ/π}, 3^{ϖ/π} | ✔ (conditional) | `CM4E/MainQi.lean` (`main`), `CM4E/TwoThree.lean` (`two_three`). Hypotheses: H1 `Thm11Kappa lemniscatic 4` (W88 §5d on G_m⁴ × E, `CM4E/Waldschmidt.lean`), H2 g₂(ϖℤ[i]) algebraic, H3 ϖ/π irrational. Route: W88 §5d (no λ case analysis needed) |
| **Conditional Theorem 1(a)** | 4E at t = cϖ, c ∈ Q(i)^×; headline 2^ϖ, 3^ϖ | ✔ (conditional) | `CM4E/MainNat.lean` (`main`, `two_three_varpi`). K = Q(i,√2), n = 4, G″ = G_m⁸ × Q″ (Q″ = (E^♮)⁴/U, dim 3). Hypotheses: H1′ `Thm11KappaNat` (W88 §5d for the model `gmQ`), H2, H3′ ϖ transcendental. Count 12 > (8 + 6 − κ)·1 with κ ≥ 4. Fidelity of `gmQ`: `REFEREE_HYP_NAT.md` |
| H1 | W88 §5d for G_m^{d₁} × E | ☐ (= N2) | the whole transcendence content |
| H2 | g₂(ϖℤ[i]) = 4, g₃ = 0 | ◐ | **g₃ = 0 proved** (`g₃_lemniscatic`, symmetry iΛ = Λ); g₂ = 4 ⇔ the Γ-formula for ϖ (lemniscatic G₄), open |
| H3 | ϖ/π irrational | ☐ | Schneider; should follow from H1 with a small configuration |
| 2πi-restriction | remove "2πi, a, b Q-independent" | ✔ | removed: the period vectors are independent through their E-coordinates (REFEREE_HYP.md) |
| **Conditional Theorem MX (K-form)** | Prop. D: z(X)+z(Y)+a ∈ Kϖ + KΩ_ρ, K = Q(i,√3), β ∈ K^× | ✔ (conditional) | `CM4E/MX.lean` (`main`). G″ = G_a × G_ℓ, d₀ = 1, d₂ = 9; W″ = ker Ψ″ (dim 8). Count 12 > (18 − κ)·1 with κ ≥ 8 (lifts of θ_h w₁, θ_h w₂ in `per`). Hypotheses: `Thm11KappaMX` (model `gmX`), g's algebraic, Wüstholz `hΓ`, `hM`. Defines Weierstrass ζ (`weierstrassZeta`, locally uniform convergence proved). Next: general β (larger K), the Bertrand–Masser/Masser step, Cor. MX1. Fidelity: `REFEREE_HYP_MX.md` (pending) |
| CaseCheck | arithmetic of the Thm 4.1 case tables (MX, MG, MG♮), for all n | ✔ | `CM4E/CaseCheck.lean`; also certifies the n = 2 failures |
| LemmaL | algebra of the two parallel periods | ✔ | `CM4E/LemmaL.lean`; Legendre enters as a hypothesis |
| LemmaK | (ψ, φ) : kⁿ ≅ K × K | ☐ | pure algebra; K ⊗_Q k ≅ K × K |
| N1 | ℘ for ϖℤ[i] | ◐ ✱ | Mathlib `PeriodPair.weierstrassP` (A. Yang 2025): periodicity, analyticity, pole orders, ℘′² = 4℘³ − g₂℘ − g₃. Missing: g₂(ϖℤ[i]) = 4 (equivalent to the Γ-formula for ϖ, via lemniscatic G₄), the addition theorem / uniformisation as a group hom, algebraicity at torsion points |
| N2 | Waldschmidt on G_m^{d₁} × E^{d₂} with periods | ☐ | generalise StrongSix `Thm1/` (interpolation determinants, 3.9k lines) and `M2/` (multiplicity estimate for linear groups, 6.6k lines) |
| N2b | heights of n·P | ☐ ✱ | Mathlib division polynomials (`AlgebraicGeometry/EllipticCurve/DivisionPolynomial`) |
| N2c | ℘ has order 2 | ☐ ✱ | via Mathlib Jacobi theta (`NumberTheory/ModularForms/JacobiTheta`) or the σ-product |
| N2d | Schwarz lemma, Liouville inequality | ✱ | StrongSix `Analytic/`, `Arith/`; diaz-modulus-lean (Schwarz for products, Siegel's lemma) |
| N2e | multiplicity estimate with an elliptic factor | ☐ | the main new formalisation. Sources: Masser–Wüstholz, Invent. Math. 64 (1981); Philippon BSMF 114 (1986); Waldschmidt, DALAG Ch. 5, 8 (linear case, already ported in StrongSix) |
| N3 | Weil restriction G² → G″ | ☐ | explicit for K = Q(i): (z₁, z₂) ↦ z₁ + iz₂ on the E-factor, coordinates on G_m⁴ |
| N4 | subgroup classification of G_m⁴ × E_i | ☐ | in Roy's linear-algebra form (surjective maps with rationality constraints), as StrongSix encodes subgroups |
| N5 | Baker (homogeneous) | ☐ ✱ | from `StrongSix.M2.waldschmidtTheorem1` (W88 §3, Cor 3.3); needs StrongSix as a path dependency |
| N6 | Ω/π ∉ Q̄ etc. | ☐ | instances of N2 with tiny groups |
| N7 | MG dimension bound | ☐ | the paper's §3 proof: data, κ = n, case check (✔ arithmetic) |
| N8 | E^♮ and Legendre | ☐ | not in Mathlib: σ, ζ, η, Legendre (residue theorem around a period parallelogram) |

## 3. Reuse map (surveyed 2026-10-30)

* **In this repository**
  - `../schanuel/six_exp/lean` (**StrongSix**, axiom-clean): Waldschmidt's Theorem 1 on G_a^{d₀} × G_m^{d₁}, *with*
    the G_m-period term Ω = 0 × 2πiQ^{d₁}; Philippon's multiplicity estimate for G_a^{d₀} × G_m^{d₁}; Roy's reduction;
    Schwarz lemma; Liouville; Cohen–Macaulay port. Its formulation of subgroups by linear maps is the model for N4 and
    N7. **N2 is a generalisation of this project.**
  - `../schanuel/five_exp/padic_e2/lean` (**LogIrr**): the same theorem over ℂ_p (no periods).
  - `../schanuel/six_exp/ref/prior_art/diaz-modulus-lean` (carlok, GitHub; blueprint at carlok.github.io/
    diaz-modulus-lean): Gelfond–Schneider (restructured from Karatarakis–Wiedijk, arXiv:2603.24823),
    Lindemann–Weierstrass (port of Mathlib PR #28013), six exponentials, Siegel's lemma, a Schwarz lemma for products,
    zero counts for exponential polynomials.
* **Mathlib v4.35.0** (pinned):
  - `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` (℘, ℘′, the differential equation; A. Yang);
  - `AlgebraicGeometry/EllipticCurve/*` (Weierstrass curves, the group law, division polynomials, j-invariant);
  - `NumberTheory/ModularForms/*` (Eisenstein series, Jacobi theta, η, the discriminant);
  - `Algebra/Module/ZLattice/*`.

  Not in Mathlib: ζ, σ, quasi-periods, Legendre, the analytic–algebraic group isomorphism, CM, abelian varieties,
  commutative algebraic groups as Lie groups.
* **Elsewhere, not Lean:** Eberl's Isabelle/HOL library of elliptic functions (ITP 2026: lattices, ℘, the addition
  theorem, theta, η) is a model for N1/N8. No Lean formalisation of Baker's theorem, the analytic subgroup theorem, or
  transcendence with elliptic functions was found.

## 4. Honest scope

The deep inputs, N2e above all, are research-scale formalisations. StrongSix's linear-group analogue took about 11k
lines. The intermediate deliverable is a **conditional** main theorem: Theorem 1(b) at ϖ from an explicitly stated
`WaldschmidtGmE` hypothesis (N2 for G_m⁴ × E_i, in Roy's linear form) and the N1 facts. All the paper's own reasoning
(N3, N4, N7, case check, Lemma L, the deduction) would then be checked. Each hypothesis is then discharged in turn.
