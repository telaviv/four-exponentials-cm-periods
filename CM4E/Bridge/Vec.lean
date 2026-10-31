/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MGnK
import CM4E.MainNat
import CM4E.Gen.MXGen
import CM4E.Gen.SMG
import LSG.W88.V5dMGn
import LSG.W88.V5dMGnK
import LSG.W88.V5dNat
import LSG.W88.V5dOntoBridges
import LSG.W88.V5dSMGn
import LSG.W88.V5dMXPMain
import CM4E.Gen.MXP

/-!
# The vector-extension hypotheses from `lean_lsg`'s `Theorem41VecLA`

`lean_lsg` derives verbatim copies of `Gen.Thm11KappaMGn L`, `Gen.Thm11KappaMGnK L` (every CM lattice; both premised on
`KappaOneZero L`) and `MainNat.Thm11KappaNat` from its vector-extension theorem `LSG.W88.Vec.Theorem41VecLA`
(`LSG.W88.V5d.thm11KappaMGn_of`, `…MGnK_of`, `…Nat_of`; standard axioms). The copies use separate `CMLattice` and
`IsAdaptedFieldBasis` structures, repackaged here (`adaptL`). So Theorem 1(a), Theorem MG♮ and its `K`-form depend only
on `Theorem41VecLA` (see also `CM4E/Bridge/MXG.lean`).

`lean_lsg` 0ed4c24 also proves the copies outright (`LSG.W88.V5d.thm11KappaMXG_uncond`, `…MGn_uncond`, `…MGnK_uncond`,
`…Nat_uncond`, via its Theorem 4.1 for vector extensions onto `M`; `…SMGn_uncond`, 36b7f5c); the `_uncond` theorems
below repackage them.
-/

open Complex CM4E.Gen

namespace CM4E.Bridge

/-- A `CMLattice` as `lean_lsg`'s copy. -/
def adaptL (L : CMLattice) : LSG.W88.MStarCopy.CMLattice :=
  ⟨L.pp, L.ω, L.α, L.η₀, L.p, L.q, L.hω₁, L.hω₂, L.hquad, L.him, L.legendre⟩

/-- **`Gen.Thm11KappaMGn L` from `Theorem41VecLA`.** -/
theorem thm11KappaMGn_of_vec (h : LSG.W88.Vec.Theorem41VecLA) (L : CMLattice) : Thm11KappaMGn L :=
  fun hk h2 h3 r b hb =>
    LSG.W88.V5d.thm11KappaMGn_of h (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`Gen.Thm11KappaMGnK L` from `Theorem41VecLA`.** -/
theorem thm11KappaMGnK_of_vec (h : LSG.W88.Vec.Theorem41VecLA) (L : CMLattice) : Thm11KappaMGnK L :=
  fun hk h2 h3 r b hb =>
    LSG.W88.V5d.thm11KappaMGnK_of h (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`MainNat.Thm11KappaNat` from `Theorem41VecLA`.** -/
theorem thm11KappaNat_of_vec (h : LSG.W88.Vec.Theorem41VecLA) : MainNat.Thm11KappaNat :=
  LSG.W88.V5d.thm11KappaNat_of h

/-- **`Gen.Thm11KappaMXG`, unconditionally** (proved in `lean_lsg`). -/
theorem thm11KappaMXG_uncond : Thm11KappaMXG :=
  fun h1 h2 h3 h4 r b hb =>
    LSG.W88.V5d.thm11KappaMXG_uncond h1 h2 h3 h4 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`Gen.Thm11KappaMGn L`, unconditionally**, for every CM lattice (premised on `KappaOneZero L`). -/
theorem thm11KappaMGn_uncond (L : CMLattice) : Thm11KappaMGn L :=
  fun hk h2 h3 r b hb =>
    LSG.W88.V5d.thm11KappaMGn_uncond (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`Gen.Thm11KappaMGnK L`, unconditionally**, for every CM lattice (premised on `KappaOneZero L`). -/
theorem thm11KappaMGnK_uncond (L : CMLattice) : Thm11KappaMGnK L :=
  fun hk h2 h3 r b hb =>
    LSG.W88.V5d.thm11KappaMGnK_uncond (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`Gen.Thm11KappaSMGn L`, unconditionally**, for every CM lattice (premised on `KappaOneZero L`). -/
theorem thm11KappaSMGn_uncond (L : CMLattice) : Thm11KappaSMGn L :=
  fun hk h2 h3 r b hb =>
    LSG.W88.V5d.thm11KappaSMGn_uncond (adaptL L) hk h2 h3 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`Gen.Thm11KappaMXP`, unconditionally** (lean_lsg 4f27015, via its Theorem 4.1 for `d₀ = 0`, `r ≤ 2`). -/
theorem thm11KappaMXP_uncond : Thm11KappaMXP :=
  fun h1 h2 h3 h4 r b hb =>
    LSG.W88.V5d.thm11KappaMXP_uncond h1 h2 h3 h4 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

/-- **`MainNat.Thm11KappaNat`, unconditionally.** -/
theorem thm11KappaNat_uncond : MainNat.Thm11KappaNat := LSG.W88.V5d.thm11KappaNat_uncond

end CM4E.Bridge
