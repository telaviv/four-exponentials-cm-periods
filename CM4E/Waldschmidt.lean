/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib

/-!
# The published input: Waldschmidt's κ-refined hyperplane theorem on `G_m^{d₁} × E`

This file only *states* a published theorem, as a `Prop` (`CM4E.Waldschmidt.Thm11Kappa`). It is used as an
explicit hypothesis of the conditional main theorem (`CM4E/MainQi.lean`). It is *not* proved here: proving it is the
long-term core of the project (`BLUEPRINT.md`, node N2).

## The source

M. Waldschmidt, *On the transcendence methods of Gel'fond and Schneider in several variables*, in New Advances in
Transcendence Theory (Durham 1986), CUP 1988, 375–398, §5d (p. 394). There Theorem 1.1 is proved with hypothesis
(1.2) replaced by

  (5.4)  `m > (d₁ + 2d₂ − κ)(d − 1 − t)`,  with `κ = rk_ℤ (Y ∩ Ker exp_G)`

(the scan prints `κ = ℓ − m`, a misprint for `m − ℓ`; cf. Lemma 5.2 there). In the setting of Theorem 1.1 (p. 375):
* `G` is a commutative algebraic group over `ℚ̄` of dimension `d`, written `G = G_a^{d₀} × G_m^{d₁} × G₂` with `d₀`,
  `d₁` maximal;
* `V` is a hyperplane of `T_G(ℂ)`;
* `W ⊂ V` is a subspace of dimension `t`, defined over `ℚ̄`;
* `Y = ℤy₁ + ⋯ + ℤy_m ⊂ V` has rank `m`, and `exp_G(Y) ⊂ G(ℚ̄)`.

The conclusion is that **`V` contains a nonzero algebraic Lie subalgebra of `T_G(ℂ)` defined over `ℚ̄`**.

## The instance stated here

`G = G_m^{d₁} × E`, where `E` is the elliptic curve `y² = 4x³ − g₂x − g₃` attached to a lattice `L` with algebraic
`g₂, g₃`. So `d₀ = 0`, `d₂ = 1` and `d = d₁ + 1`; `d₀` and `d₁` are then maximal.
* Coordinates on `T_G(ℂ) = ℂ^{d₁} × ℂ`: `exp_G(t, z) = ((e^{t_j})_j, (℘(z) : ℘'(z) : 1))`. They are `ℚ̄`-rational.
* `Ker exp_G = 2πi ℤ^{d₁} × L`.
* The connected algebraic subgroups of `G_m^{d₁} × E` are the products `T_ℒ × 0` and `T_ℒ × E`, where `T_ℒ` is the
  subtorus with Lie algebra `ℒ ⊗ ℂ` for a subspace `ℒ ⊂ ℚ^{d₁}`. (Standard: there are no nonzero homomorphisms
  between a torus and an elliptic curve in either direction, so Goursat's lemma gives products.)
* `Y` is taken as a `ℚ`-span `span_ℚ {y₁, …, y_m}` of generators with `exp_G(y_i) ∈ G(ℚ̄)`. This is equivalent to the
  `ℤ`-span version: the `ℤ`-span has rank `dim_ℚ Y`, and its intersection with `Ker exp_G` has rank
  `dim_ℚ (Y ∩ Ω_ℚ)`, where `Ω_ℚ` is the `ℚ`-span of `Ker exp_G`.
-/

open Complex Module

namespace CM4E.Waldschmidt

/-- The Lie algebra `ℂ^{d₁} × ℂ` of `G_m^{d₁} × E`. -/
abbrev T (d₁ : ℕ) := (Fin d₁ → ℂ) × ℂ

/-- A vector of `T d₁` with algebraic coordinates. -/
def AlgVec {d₁ : ℕ} (v : T d₁) : Prop := (∀ j, IsAlgebraic ℚ (v.1 j)) ∧ IsAlgebraic ℚ v.2

/-- A `ℂ`-subspace is *defined over `ℚ̄`* if it is spanned by vectors with algebraic coordinates. -/
def RationalOverQbar {d₁ : ℕ} (W : Submodule ℂ (T d₁)) : Prop :=
  ∃ S : Set (T d₁), (∀ v ∈ S, AlgVec v) ∧ W = Submodule.span ℂ S

/-- `exp_G(y) ∈ G(ℚ̄)`: the `G_m`-coordinates `e^{t_j}` are algebraic, and the `E`-coordinate is the origin
(`z ∈ L`) or a point `(℘(z), ℘'(z))` with algebraic coordinates. -/
def ExpAlg (L : PeriodPair) {d₁ : ℕ} (y : T d₁) : Prop :=
  (∀ j, IsAlgebraic ℚ (Complex.exp (y.1 j))) ∧
    (y.2 ∈ L.lattice ∨ (IsAlgebraic ℚ (L.weierstrassP y.2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP y.2)))

/-- `Ω_ℚ`: the `ℚ`-span of `Ker exp_G = 2πi ℤ^{d₁} × L`. -/
noncomputable def OmegaQ (L : PeriodPair) (d₁ : ℕ) : Submodule ℚ (T d₁) :=
  Submodule.span ℚ
    (Set.range (fun j : Fin d₁ => ((Pi.single j (2 * Real.pi * I) : Fin d₁ → ℂ), (0 : ℂ))) ∪
      (fun ω : ℂ => ((0 : Fin d₁ → ℂ), ω)) '' (L.lattice : Set ℂ))

/-- The Lie algebra of the connected algebraic subgroup `T_ℒ × (0 or E)`: `(ℒ ⊗ ℂ) × (0 or ℂ)`. -/
noncomputable def tangentSub {d₁ : ℕ} (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool) : Submodule ℂ (T d₁) :=
  (Submodule.span ℂ ((fun l : Fin d₁ → ℚ => fun j => ((l j : ℚ) : ℂ)) '' (ℒ : Set (Fin d₁ → ℚ)))).prod
    (if b then ⊤ else ⊥)

/-- **Waldschmidt's κ-refined hyperplane theorem** (W88, §5d, hypothesis (5.4)), for `G = G_m^{d₁} × E_L`, where
`L` is a lattice with algebraic invariants `g₂, g₃`. If
* `V` is a hyperplane of `ℂ^{d₁} × ℂ`;
* `W ⊂ V` is defined over `ℚ̄`;
* `Y = span_ℚ {y₁, …, y_m} ⊂ V` with every `exp_G(y_i)` algebraic;
* `dim_ℚ Y > (d₁ + 2 − κ)(d₁ − dim W)`, with `κ = dim_ℚ (Y ∩ Ω_ℚ)`;

then `V` contains the Lie algebra of a nonzero connected algebraic subgroup `T_ℒ × (0 or E)`. -/
def Thm11Kappa (L : PeriodPair) (d₁ : ℕ) : Prop :=
  IsAlgebraic ℚ L.g₂ → IsAlgebraic ℚ L.g₃ →
  ∀ (V W : Submodule ℂ (T d₁)) (m : ℕ) (y : Fin m → T d₁),
    finrank ℂ V = d₁ → W ≤ V → RationalOverQbar W →
    (∀ i, y i ∈ V ∧ ExpAlg L (y i)) →
    ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
      ((d₁ : ℤ) + 2 - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ OmegaQ L d₁)) *
        ((d₁ : ℤ) - finrank ℂ W)) →
    ∃ (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool), (ℒ ≠ ⊥ ∨ b = true) ∧ tangentSub ℒ b ≤ V

end CM4E.Waldschmidt
