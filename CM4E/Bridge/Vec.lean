/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MGnK
import CM4E.MainNat
import LSG.W88.V5dMGn
import LSG.W88.V5dMGnK
import LSG.W88.V5dNat

/-!
# The vector-extension hypotheses from `lean_lsg`'s `Theorem41VecLA`

`lean_lsg` derives verbatim copies of `Gen.Thm11KappaMGn L`, `Gen.Thm11KappaMGnK L` (every CM lattice; both premised on
`KappaOneZero L`) and `MainNat.Thm11KappaNat` from its vector-extension theorem `LSG.W88.Vec.Theorem41VecLA`
(`LSG.W88.V5d.thm11KappaMGn_of`, `…MGnK_of`, `…Nat_of`; standard axioms). The copies use separate `CMLattice` and
`IsAdaptedFieldBasis` structures, repackaged here (`adaptL`). So Theorem 1(a), Theorem MG♮ and its `K`-form depend only
on `Theorem41VecLA` (see also `CM4E/Bridge/MXG.lean`).
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

end CM4E.Bridge
