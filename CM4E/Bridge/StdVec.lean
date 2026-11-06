/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.Vec
import LSG.W88.StdVec

/-!
# The standard model with a vector-extension factor (copy of `lean_lsg`'s `gmStdVec`)

`gmStdVec d0 d1 Ls M` is this project's copy (body verbatim from `LSG.W88.MStarCopy.gmStdVec`, `lean_lsg` `dev/INTERFACE.md`,
last section) of the group model of `G = G_a^{d₀} × G_m^{d₁} × G₂`, `G₂` the push-out of the universal vector extension
`(E₁ × ⋯ × E_m)^♮` along the `r × m` matrix `M`, in the coordinates `LSG.W88.Vec.TanV d₀ d₁ m r = ℂ^{d₀} × ℂ^{d₁} × ℂ^m × ℂ^r`
(`(a, b, z, s)`, `s = M w` for the fibre coordinates `w` of `(E^m)^♮`): `d₁ = d1`, `d₂ = m + r`, algebraic vectors
`AlgVecV`, logarithms `LamV Ls M` (`a ∈ ℚ̄^{d₀}`, `e^{b_i} ∈ ℚ̄`, `z_j ∈ Λ_j` or `℘_j(z_j) ∈ ℚ̄`, `s − Mζ(z) ∈ ℚ̄^r`),
periods `span_ℚ PerV Ls M` (`0 × 2πiℤ^{d₁} × {(λ, Mη(λ))}`), and as `sub` the tangent spaces of all `SubgroupDataV`
(`Γ + T_U^⊥ + T_{B̃}`).

Soundness of the model (not checked by Lean): this is the statement of `lean_lsg`'s Theorem 4.1 for the class `𝒞`
(`LSG/W88/StatementVec.lean`, `dev/VECEXT.md` §2): the coordinates, `Λ(G)`, `Ω(G)` and the classification of
connected algebraic subgroups `T_U × (B̃ + Γ)` of `G`. Lean's `ζ` (the lattice series) equals `η` on the lattice
(`LSG.W88.Vec.zeta_of_mem_lattice`), so `LamV` needs no case split.

* `hypStdVec_cm`: `HyperplaneKappa (gmStdVec d0 d1 (fun _ => L.pp) M)` for one CM lattice `L` with `κ₁ = 0`, algebraic
  invariants, an algebraic `M` and `r ≤ 1` (`lean_lsg`'s `hypStdVecCM`, standard axioms).
-/

open Complex CM4E.Gen CM4E.Waldschmidt

namespace CM4E.Bridge

/-- **The standard model of `G_a^{d₀} × G_m^{d₁} × ((E₁ × ⋯ × E_m)^♮ pushed out along `M`)`** (verbatim copy). -/
noncomputable def gmStdVec (d0 d1 : ℕ) {m r : ℕ} (Ls : Fin m → PeriodPair)
    (M : Matrix (Fin r) (Fin m) ℂ) : GroupModel (LSG.W88.Vec.TanV d0 d1 m r) where
  d₁ := d1
  d₂ := m + r
  alg := LSG.W88.Vec.AlgVecV
  lam := LSG.W88.Vec.LamV Ls M
  per := Submodule.span ℚ
    (LSG.W88.Vec.PerV (d0 := d0) (d1 := d1) Ls M : Set (LSG.W88.Vec.TanV d0 d1 m r))
  sub := fun S => ∃ H : LSG.W88.Vec.SubgroupDataV (d0 := d0) (d1 := d1) Ls M, S = H.tan

/-- **W88 §5d for `G_a^{d₀} × G_m^{d₁} × ((E^m)^♮ pushed out along `M`)`**, one CM lattice with `κ₁ = 0`, `r ≤ 1`. -/
theorem hypStdVec_cm (L : CMLattice) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) (d0 d1 : ℕ) {m r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) (hr : r ≤ 1)
    (hM : LSG.W88.Vec.AlgMat M) : HyperplaneKappa (gmStdVec d0 d1 (fun _ : Fin m => L.pp) M) :=
  LSG.W88.hypStdVecCM (adaptL L) hκ hg₂ hg₃ d0 d1 M hr hM

end CM4E.Bridge
