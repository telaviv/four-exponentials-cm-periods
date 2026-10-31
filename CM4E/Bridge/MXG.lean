/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Gen.MXGen
import LSG.W88.V5dMXG

/-!
# Theorem MX's hypothesis from `lean_lsg`'s vector-extension statement

`lean_lsg` states the hypothesis of Theorems MX, MX1 and deg2 (ii) for a verbatim copy `LSG.W88.MStarCopy.Thm11KappaMXG`
of `Gen.Thm11KappaMXG` (same group model `gmXG`; `HyperplaneKappa` agrees by `Iff.rfl`). The only difference is that the
copy's `IsAdaptedFieldBasis` is a separate structure, so `thm11KappaMXG_of_copy` repackages the basis.
`lean_lsg` derives the copy from its vector-extension theorem `Theorem41VecLA` and five CM inputs
(`LSG.W88.V5d.thm11KappaMXG_of_cm`, in progress there); composed with `thm11KappaMXG_of_copy` it gives `Gen.Thm11KappaMXG`.
-/

open Complex CM4E.Gen

namespace CM4E.Bridge

/-- `Gen.Thm11KappaMXG` from `lean_lsg`'s verbatim copy. -/
theorem thm11KappaMXG_of_copy (H : LSG.W88.MStarCopy.Thm11KappaMXG) : Gen.Thm11KappaMXG :=
  fun h1 h2 h3 h4 r b hb => H h1 h2 h3 h4 r b ⟨hb.indep, hb.one_mem, hb.mul_mem, hb.inv_mem, hb.alg⟩

end CM4E.Bridge
