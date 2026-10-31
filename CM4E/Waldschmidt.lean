/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The published input: Waldschmidt's κ-refined hyperplane theorem on `G_m^{d₁} × E`

This file only *states* a published theorem, as a `Prop`: the shared form `HyperplaneKappa G` for a group model `G`,
and its first instance `Thm11Kappa` (for `G_m^{d₁} × E`, used by `CM4E/MainQi.lean`). The other instances are
`MainNat.Thm11KappaNat` and those of `CM4E/Gen/` (`Thm11KappaMG`, `Thm11KappaMGn`, `Thm11KappaMXG`,
`Thm11KappaSMG`, `Thm11KappaSMGn`). The theorem is *not* proved here; it is the W88 hypothesis of the final theorems in
`CM4E/Final.lean`.

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

/-! ## The shared hypothesis form

Every conditional theorem of this project assumes `HyperplaneKappa G` for a *group model* `G`. That is W88 §5d,
(5.4), for the commutative algebraic group `G` described by the model. A model records
* the tangent space, with its `ℚ̄`-structure (`alg`: vectors with algebraic coordinates);
* the numbers `d₁` (the multiplicative factor) and `d₂ = dim G₂`;
* a set `lam` of logarithms of algebraic points;
* a `ℚ`-subspace `per` of the `ℚ`-span of the periods;
* a family `sub` of subspaces that contains the Lie algebras of all connected algebraic subgroups over `ℚ̄`.

**Soundness.** A model is *sound* for an algebraic group `G = G_a^{d₀} × G_m^{d₁} × G₂` over `ℚ̄` (`d₀`, `d₁` maximal,
`d₂ = d − d₀ − d₁`; (1.2)/(5.4) do not involve `d₀`, so a `G_a` factor needs no field) if
`lam ⊂ Λ(G)`, `per ⊂ ℚ ⊗ Ω(G)`, and every connected algebraic subgroup has its Lie algebra in `sub`. For a sound model
W88 §5d implies `HyperplaneKappa G`:
* a smaller `lam` strengthens the premise;
* a smaller `per` makes `κ` smaller, which only strengthens the premise `m > (d₁ + 2d₂ − κ)(d − 1 − t)`;
* a larger `sub` weakens the conclusion.

The soundness of each model is a mathematical fact that is **not** checked by Lean. It is stated next to each model,
with its source, and collected in `TRUST.md`. -/

/-- A group model: the coordinate data of a commutative algebraic group `G = G_a^{d₀} × G_m^{d₁} × G₂` over `ℚ̄`. -/
structure GroupModel (V : Type*) [AddCommGroup V] [Module ℂ V] [Module ℚ V] where
  /-- the dimension of the multiplicative factor -/
  d₁ : ℕ
  /-- `dim G₂` -/
  d₂ : ℕ
  /-- vectors with algebraic coordinates (the `ℚ̄`-structure of `T_G`) -/
  alg : V → Prop
  /-- (some) logarithms of algebraic points -/
  lam : Set V
  /-- (part of) the `ℚ`-span of the periods `Ker exp_G` -/
  per : Submodule ℚ V
  /-- a family containing the Lie algebras of all connected algebraic subgroups over `ℚ̄` -/
  sub : Submodule ℂ V → Prop

variable {Vt : Type*} [AddCommGroup Vt] [Module ℂ Vt] [Module ℚ Vt]

/-- `W` is defined over `ℚ̄`: spanned by vectors with algebraic coordinates. -/
def GroupModel.Rational (G : GroupModel Vt) (W : Submodule ℂ Vt) : Prop :=
  ∃ S : Set Vt, (∀ v ∈ S, G.alg v) ∧ W = Submodule.span ℂ S

/-- **The shared hypothesis: Waldschmidt's κ-refined hyperplane theorem (W88 §5d, (5.4)) for the group of `G`.**
Suppose
* `V` is a hyperplane;
* `W ⊂ V` is defined over `ℚ̄`;
* `Y = span_ℚ {y₁, …, y_m} ⊂ V` with every `y_i ∈ lam`;
* `dim_ℚ Y > (d₁ + 2d₂ − κ)(d − 1 − dim W)`, with `κ = dim_ℚ (Y ∩ per)`.

Then `V` contains a nonzero member of `sub`. -/
def HyperplaneKappa (G : GroupModel Vt) : Prop :=
  ∀ (V W : Submodule ℂ Vt) (m : ℕ) (y : Fin m → Vt),
    finrank ℂ V + 1 = finrank ℂ Vt → W ≤ V → G.Rational W →
    (∀ i, y i ∈ V ∧ y i ∈ G.lam) →
    ((finrank ℚ (Submodule.span ℚ (Set.range y)) : ℤ) >
      ((G.d₁ : ℤ) + 2 * G.d₂ - finrank ℚ ↥(Submodule.span ℚ (Set.range y) ⊓ G.per)) *
        ((finrank ℂ Vt : ℤ) - 1 - finrank ℂ W)) →
    ∃ S : Submodule ℂ Vt, G.sub S ∧ S ≠ ⊥ ∧ S ≤ V

/-- The model of `G_m^{d₁} × E_L`. It is sound when `g₂, g₃ ∈ ℚ̄` (see the module docstring: the coordinates, `Λ(G)`,
`Ker exp_G = 2πiℤ^{d₁} × L`, and the subgroups `T_ℒ × (0 or E)`). -/
noncomputable def gmE (L : PeriodPair) (d₁ : ℕ) : GroupModel (T d₁) where
  d₁ := d₁
  d₂ := 1
  alg := AlgVec
  lam := {y | ExpAlg L y}
  per := OmegaQ L d₁
  sub := fun S => ∃ (ℒ : Submodule ℚ (Fin d₁ → ℚ)) (b : Bool), S = tangentSub ℒ b

/-- **Waldschmidt's κ-refined hyperplane theorem** (W88, §5d, hypothesis (5.4)), for `G = G_m^{d₁} × E_L`, where
`L` is a lattice with algebraic invariants `g₂, g₃`. -/
def Thm11Kappa (L : PeriodPair) (d₁ : ℕ) : Prop :=
  IsAlgebraic ℚ L.g₂ → IsAlgebraic ℚ L.g₃ → HyperplaneKappa (gmE L d₁)

lemma tangentSub_bot_false {d₁ : ℕ} : tangentSub (⊥ : Submodule ℚ (Fin d₁ → ℚ)) false = ⊥ := by
  have h0 : (fun _ : Fin d₁ => (0 : ℂ)) = 0 := rfl
  simp [tangentSub, h0, Submodule.prod_bot]

end CM4E.Waldschmidt
