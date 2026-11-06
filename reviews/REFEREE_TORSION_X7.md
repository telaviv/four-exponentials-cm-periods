# Referee report: the torsion step of Theorem X7 and Corollary X7 (a), (b) (`CM4E/AbVar/X7Torsion.lean`)

Referee: adversarial AI reviewer (Claude), 2026-10-31. Commit 041b468.

**Scope.**
* In full: `CM4E/AbVar/X7Torsion.lean` (`TorsionTriple`, `TorsionX7`, `thmX7_torsion`, `x7a`, `x7b`).
* For context: `CM4E/AbVar/X7.lean` (`perT`, `aGen`, `thmX7`, `WuestholzX7`), `CM4E/AbVar/Fermat7.lean` (`zeta7`,
  `perA`, `omega7`, `alpha7`), `CM4E/Gen/ThmM.lean` (`LogE`), `TRUST.md` l. 160–200.
* Paper: draft [II], Theorem X (l. 618) and its proof, "Torsion" paragraph (l. 720–724);
  Theorem X7 (l. 750); Cor. X7 (l. 761) and its proof (l. 770–775); Cor. X7intro (l. 126).
* Read first: `reviews/REFEREE_HYP_X7.md` (model, period triple, CM direction, lattice of `E`) and
  `reviews/REFEREE_INPUTS_X7.md` (`WuestholzBeta7`, `WuestholzX7`). Their facts (G1)–(G3), (AST) are used below without
  repeating the derivations.

**Process.** No Lean file was edited and no git command was run. Scratch files are in `reviews/checks/torsionx7/`:
* `TorX7.lean` / `TorX7.out`: axiom audit; sanity lemmas `TorsionTriple perT`, `TorsionTriple 0`; the proposed
  strengthening `x7a_full` (proved, compiles); a sketch of a concrete Abel–Jacobi set `AJ1`, `LAJ` (compiles).
* `check_torsion.py` / `check_torsion.out`: the exponent convention of `TorsionTriple` tested on a known torsion point,
  40 digits.

Labels: [Lit] published theorem; [Proved] derived here from [Lit] with a complete argument; [Numerical].

## Verdicts

* **Item 1 (`TorsionTriple` = "exp_A(v) is torsion"): CORRECT.** For coherent triples in the `perT` normalisation, the
  definition is exactly `v ∈ ℚ ⊗ Ω(A) = Fγ`. The exponent `ζ^{(s+1)e}` matches `aGen`. The set it defines does not
  depend on the CM direction.
* **Item 2 (`TorsionX7`): TRUE WITH NOTES.**
  - Clause (i) is TRUE for every `LA ⊆ LA_A`, including `c = 0`, `v = perT` and the use of a single slot.
  - Clause (ii) is TRUE with no condition: it has no parameter.
  - Note: clause (i) is true on a *narrower* class of `LA` than `WuestholzX7`. It fails for the `ℚ̄`-span, for
    incoherent triples and for rescaled coordinates. TRUST.md must not carry over the "robustness" remarks of
    REFEREE_INPUTS_X7 §2.
* **Item 3 (fidelity): CORRECT WITH NOTES.**
  - `thmX7_torsion` is the full conclusion of Theorem X7, and `x7b` is Cor. X7(b) exactly.
  - `x7a` is a genuine but *removable* weakening of Cor. X7(a): it excludes `c = 0` and does not state
    `z₁(v) ≠ 0`. Both follow from `TorsionX7` (i) at `c = 0`, which is already a hypothesis. No new named input is
    needed; a drop-in replacement is proved in `TorX7.lean`.
* **Item 4 (literal Cor. X7 (a), (b) in Lean): opinion below.**
  - A fully faithful statement through a Riemann surface, a Jacobian and an Abel–Jacobi map is not possible in
    Mathlib today.
  - An *elementary* faithful statement is possible: integrals along lifted C¹ paths in `ℂ ∖ {0,1}`, with "infinite
    order" read as `¬ TorsionTriple`.
  - The parametric `LA` formulation plus a documented intended instance is an acceptable substitute. Instantiating
    `LA` with a concrete set is a cheap improvement.

**Axioms.** `lake env lean reviews/checks/torsionx7/TorX7.lean` (20 s) reports that `thmX7_torsion`, `x7a` and `x7b`
depend only on `[propext, Classical.choice, Quot.sound]`. `X7Torsion.lean` contains no `sorry`, `axiom` or
`native_decide`.

**No FATAL or MAJOR issue was found.**

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `TorsionTriple` | `{(Σ_e q_e ζ^{(s+1)e} P_{s+1})_s : q ∈ ℚ⁶} = {(σ_{s+1}(x)P_{s+1})_s : x ∈ F}` = the eigen-coordinates of `Fγ = ℚ⊗Ω(A)`. This uses `[F:ℚ] = 6 = rk Ω(A)`, `γ ≠ 0` and `{ζ^e}_{e<6}` a `ℚ`-basis of `F` |
| 2 | OK | exponent convention | it is the one in `aGen` (`z_s([ζ^e]v) = ζ^{(s+1)e} z_s(v)`). The opposite convention gives the same set (`x ↦ x̄`). [Numerical] the torsion point `Q − O`, with `O = (0,0)` and `Q = (1/2, 4^{−1/7})`, has `z_s = B_{s+1}/2`. This equals `TorsionTriple` with `q = (3/7, 5/14, 2/7, 3/14, 1/7, 1/14)`, i.e. `x = 1/(2(1−ζ))`, to 2e-40 |
| 3 | OK | (i), `c ≠ 0` | Wüstholz on `A²` at `(v, γ)`: `H` is a 3-dimensional graph of some `x ∈ End⁰(A) = F`, so `v = xγ` (derivation §2) |
| 4 | OK | (i), `c = 0` | Wüstholz on the simple `A` at `v`: `T_H ⊂ ker z_s` forces `H = 0`, so `v = 0`, which is a torsion triple (`q = 0`) |
| 5 | OK | (i), one slot | one eigen-coordinate is enough. The graph argument fixes all three coordinates at once: `z_t(v) = σ_{t+1}(x)P_{t+1}` for every `t` |
| 6 | OK | (i), `v = perT` | if `perT ∈ LA`, then `TorsionTriple perT` holds with `q = e₀`. Lean-checked (`TorX7.lean`). The conclusion holds, so there is no conflict |
| 7 | OK | (ii) | Wüstholz on `E²` at `(u, Ω)` (or Masser 1975) gives `u = xΩ` with `x ∈ End⁰(E) = ℚ(α)`. The analytic representation of `[α]` on `ℂ/Ωℤ[α]` is multiplication by `α`. `c = 0` is trivial |
| 8 | MINOR (docs) | domain of (i) | `TorsionX7 LA` is false for `LA = {√2·perT}`, which lies in the `ℚ̄`-span of `LA_A`. It is false for incoherent triples, e.g. `(P₁, z₂(w), z₃(w))` with `w` non-torsion. It is false for coordinates rescaled by factors not of the form `(σ_{s+1}(λ))_s`, `λ ∈ F`. It holds for every subset of `LA_A` and for the `ℚ`-span (`Λ(A)` is divisible). REFEREE_INPUTS_X7 §2 "robustness" points 2–4 must **not** be quoted for `TorsionX7` |
| 9 | OK | `thmX7_torsion` vs Theorem X7 | hypotheses identical (`v_i ∈ LA`, `u ∈ 𝓛_E`, `q_i ∈ ℚ̄`, `β ∈ ℚ̄ˣ`, the displayed relation). The conclusion `q₁ = q₂ = 0`, `TorsionTriple v_i`, `u ∈ ℚ(α)Ω` is exactly "`exp v_i`, `exp_E u` torsion", since `ℚΛ_E = ℚΩ + ℚαΩ` |
| 10 | OK | `x7b` vs Cor. X7(b) | exact. The paper itself says `ℚ̄ˣ`, and `u` non-torsion gives `u ≠ 0`, so `v 2 ≠ c·u·P₃/P₁` (`c ∈ ℚ̄ˣ`) is the ratio statement. The data are the paper's (`v₃ = v`, `β = c`, all others `0`) |
| 11 | MINOR (fidelity) | `x7a` vs Cor. X7(a) | the paper has `ℚ̄`, not `ℚ̄ˣ`. With `0` included it claims `z₂(v) ≠ 0`, and the ratio being defined claims `z₁(v) ≠ 0`. `x7a` has `hc0 : c ≠ 0` and no `z₁(v) ≠ 0`. Both are one-line consequences of `hTo.1` at `c = 0`, which is already a hypothesis. **Fix:** replace `x7a` by `x7a_full` (§3); it is proved in `TorX7.lean` |
| 12 | NIT | `h0 : 0 ∈ LA` (`x7a`, `x7b`) | true for the intended instance (the logarithm of `O`). Document it in TRUST.md, or discharge it by a concrete `LA` (#15) |
| 13 | MINOR (docs) | `TRUST.md` l. 162, 164, 200 | stale: "the torsion step … is not formalised", "Cor. X7 (a), (b) — ✗", "What is still missing: … the torsion step". There is no §3 row for `TorsionX7` and no §2 entry for `thmX7_torsion`, `x7a`, `x7b`. Draft in §5 |
| 14 | COSMETIC | `TorsionX7` docstring | "one slot coordinate in `ℚ̄P_s`" uses 1-indexed `P_s` against the 0-indexed `s` of the code (`perA (s+1)`). Write `ℚ̄P_{s+1}`. After #11, also update the `x7a` docstring (`ℚ̄ˣ` → `ℚ̄`) and the module docstring |
| 15 | SUGGESTION | Cor. X7(a), (b) literally | define the Abel–Jacobi set concretely (`AJ1`, `LAJ := span_ℚ AJ1`, sketch compiles in `TorX7.lean`) and state `x7a`, `x7b` for `LA = LAJ`. This removes the uninterpreted parameter. Trust then rests on the same classical facts, now about an explicitly defined set (§4) |

## 1. `TorsionTriple` [Proved, modulo (G1)]

* `A` is a CM abelian 3-fold with `End⁰(A) = F = ℚ(ζ₇)`, `[F:ℚ] = 6 = 2·dim A` ((G1), primitive type `{1,2,3}`). So
  `H₁(A,ℚ) = ℚ⊗Ω(A)` is a 1-dimensional `F`-vector space, and `ℚ⊗Ω(A) = Fγ` for any period `γ ≠ 0`.
* `γ` (the cycle of (G1)) is a genuine closed cycle with `z_s(γ) = perA(s+1)`. This was checked on one explicit loop
  to 1e-60 in REFEREE_HYP_X7 #1.
* `x ∈ F` acts on `Lie A` diagonally: `z_s(xw) = σ_{s+1}(x)z_s(w)` with `σ_{s+1}(ζ) = ζ^{s+1}` (REFEREE_HYP_X7 #2). With
  `x = Σ_{e<6} q_e ζ^e`, `q ∈ ℚ⁶` (a `ℚ`-basis of `F`), `z_s(xγ) = Σ_e q_e ζ^{(s+1)e} perA(s+1)`. This is the right
  side of `TorsionTriple` verbatim.
* `exp_A(v)` is torsion iff `Nv ∈ Ω(A)` for some `N ≥ 1`, iff `v ∈ ℚ⊗Ω(A) = Fγ`. `(z₁, z₂, z₃) : Lie A → ℂ³` is a
  `ℂ`-linear isomorphism, so the triple condition is equivalent to the condition on `v`.
* **Convention.** `aGen` writes `[ζ^e]v` as `ζ^{(s+1)e}v_s`, and `TorsionTriple` uses the same exponent. Even with the
  opposite CM direction, the defined set would be unchanged: `(σ_{−(s+1)}(x))_s = (σ_{s+1}(x̄))_s`, and `x̄` ranges over
  `F`.
* [Numerical] (`check_torsion.py`). Take `O = (0,0)` (a branch point) and `Q = (1/2, 4^{−1/7})`.
  - `Q − O` is torsion: the hyperelliptic involution fixes `Q` and acts as `[−1]`, so `2(Q − O) = O′ − O` with
    `O′ = (1,0)`, and `O′ − O` is 7-torsion.
  - Its Abel–Jacobi triple along `[0, 1/2]` on the sheet `y > 0` is `z_s = B_{s+1}/2`.
  - With `q` the coordinates of `1/(2(1−ζ))` in the basis `1, ζ, …, ζ⁵`, `TorsionTriple`'s formula reproduces
    `z_s` to 2e-40. The same `q` with the opposite exponent misses by `O(1)`: the convention changes which `q` works,
    not the set.
* Rationality: `q : Fin 6 → ℚ` (not `ℚ̄`) is essential and correct. `ℚ̄`-coefficients would give all of
  `ℚ̄`-multiples of the `[ζ^e]γ`, which is wrong.

## 2. `TorsionX7` [Proved from (AST) = Wüstholz 1989]

Intended `LA` = any subset of `LA_A = {(z₁(v), z₂(v), z₃(v)) : v ∈ Lie A, exp_A(v) ∈ A(ℚ̄)}`. The `z_s` are the
Abel–Jacobi coordinates of (G1), the ones with `z_s(γ) = perA(s+1)`.

**Clause (i).** Let `v ∈ LA_A`, `s ∈ {0,1,2}`, `c ∈ ℚ̄` and `z_s(v) = c·perA(s+1)`.
1. Let `G = A²`, `ξ = (v, γ)`; then `exp ξ = (exp v, 0) ∈ G(ℚ̄)`.
2. Let `ℓ = z_s^{(1)} − c·z_s^{(2)}`. It is `ℚ̄`-rational (`z_s` is dual to the `ℚ`-rational differential
   `dx/y^{6−s}`), nonzero (its `z_s^{(1)}`-coefficient is 1), and `ℓ(ξ) = 0`.
3. (AST) gives a connected `H ⊂ A²` with `ξ ∈ T_H ⊂ ker ℓ`. So `H` is an abelian subvariety and `H ≠ A²`.
4. `pr₂(H)` is an abelian subvariety of `A` whose tangent space contains `γ ≠ 0`. Since `A` is simple, `pr₂(H) = A`.
   Abelian subvarieties of `A²` have dimension `0`, `3` or `6` (`A` is simple and `A²` isotypic), so `dim H = 3` and
   `pr₂|_H` is an isogeny.
5. `φ := pr₁∘(pr₂|_H)^{−1} ∈ End⁰(A) = F`, say `φ = x`, and `T_H = {(xw, w)}`. From `(v, γ) ∈ T_H`, `v = xγ ∈ Fγ`. By §1
   this is `TorsionTriple v`.

This argument does not use `c ≠ 0`. For `c = 0` there is also the paper's direct route: Wüstholz on `A` at `v` with
`ℓ = z_s` gives `T_H ⊂ ker z_s`, so `H ≠ A`, so `H = 0` and `v = 0`. In the graph argument, `c = 0` forces
`σ_{s+1}(x) = 0`, so `x = 0`. Both give `v = 0 = TorsionTriple` with `q = 0`. Hence:
* **`c = 0`:** `z_s(v) = 0 ⇒ v = 0` holds for each single `s`. This is the paper's "values 0 and ∞ do not occur".
* **One slot suffices:** step 5 determines all three coordinates.
* **`v = perT`:** `x = 1`, consistent. It is Lean-checked that `TorsionTriple perT` holds.

**Clause (ii).** Let `u ∈ 𝓛_E = LogE E7`, `c ∈ ℚ̄` and `u = cΩ`.
* If `c = 0`, then `u = 0 = (0 + 0·α)Ω`.
* Otherwise, `E` is the curve over `ℚ̄` with lattice `Ωℤ[α]` ((G2): `g₂, g₃` algebraic, `j = −3375`), so `LogE E7` is the
  set of logarithms of `E(ℚ̄)`. Apply (AST) on `E²` at `(u, Ω)` with `ℓ = z^{(1)} − c·z^{(2)}`. This gives an elliptic
  curve `H ⊂ E²` that is the graph of some `x ∈ End⁰(E) = ℚ(α)`. Its analytic representation is multiplication by `x`,
  because `αΩℤ[α] ⊂ Ωℤ[α]`. So `u = xΩ = (p + qα)Ω`.
* Alternatively, Masser (*Elliptic functions and transcendence*, LNM 437, 1975): if `u, Ω` were `k`-independent, then
  `1, u, Ω` would be `ℚ̄`-independent, which contradicts `u = cΩ`.
* Clause (ii) has no parameter, so it is a plain true statement.

**Where clause (i) is false (#8).** These failures do not threaten soundness (a false hypothesis makes the theorems
vacuous), but they matter for documentation.
* *`ℚ̄`-span.* Take `v = √2·perT`. Then `v 0 = √2·P₁` with `√2 ∈ ℚ̄`. `TorsionTriple v` would need `x ∈ F` with
  `σ₁(x) = √2`, but the only quadratic subfield of `ℚ(ζ₇)` is `ℚ(√−7)`. So `TorsionX7 {√2·perT}` is false, although
  `WuestholzX7` holds on the `ℚ̄`-span (REFEREE_INPUTS_X7 §2, robustness point 2).
* *Incoherent triples.* `(P₁, z₂(w), z₃(w))` with `w` non-torsion has a `ℚ̄P₁` slot but is not a torsion triple.
* *Normalisation.* If `LA` is written in coordinates `λ_s z_s` with `λ_s ∈ ℚ̄ˣ`, then `γ`'s triple `(λ_s P_{s+1})` is a
  torsion triple only when `(λ_s) = (σ_{s+1}(λ))` for some `λ ∈ F`. So `TorsionX7` pins `LA` to the exact `perT`
  normalisation, more rigidly than `WuestholzX7` does.
* *Allowed.* Any subset of `LA_A`. Also `span_ℚ LA_A = LA_A`: `Λ(A)` is a `ℚ`-vector space, because division points of
  algebraic points are algebraic.

## 3. Fidelity

**`thmX7_torsion` vs Theorem X7.**
* The hypotheses are those of `thmX7` and the paper's.
* The conclusion `q₁ = q₂ = 0 ∧ TorsionTriple v₁ ∧ TorsionTriple v₂ ∧ TorsionTriple v₃ ∧ u ∈ ℚ(α)Ω` is Theorem X7's
  full conclusion under the reading of §1 and `ℚΛ_E = ℚ(α)Ω`.
* The proof applies `hTo.1` at slot 0 for `v₁`, slot 1 for `v₂` and slot 2 for `v₃`, and `hTo.2` for `u`. This is the
  paper's "Torsion" paragraph slot by slot. **CORRECT.**

**`x7b` vs Cor. X7(b).** Exact (#10). **CORRECT.**

**`x7a` vs Cor. X7(a).**
* The paper says `z₂(v)/z₁(v) ∉ ℚ̄·P₃/P₁` and adds "the values 0 and ∞ of the ratio do not occur for `v ≠ 0`".
  - The `c = 0` case needs a separate argument because the proof's data has `β = c`, and Theorem X7 requires
    `β ≠ 0`.
  - The paper's argument is Wüstholz on `A`, which is exactly `TorsionX7` (i) at `c = 0`.
* So the exclusion `hc0` in `x7a` is a real weakening as stated, **but not a weakening of what is proved from the
  hypotheses**. The missing statements are one-liners from `hTo`, which is already assumed:

```lean
theorem slot_ne_zero (LA : Set (Fin 3 → ℂ)) (hTo : TorsionX7 LA) (v : Fin 3 → ℂ) (hv : v ∈ LA)
    (hnt : ¬ TorsionTriple v) (s : Fin 3) : v s ≠ 0 := fun h =>
  hnt (hTo.1 v hv s 0 isAlgebraic_zero (by simp [h]))

theorem x7a_full (LA : Set (Fin 3 → ℂ)) (hW : Thm11KappaX7 LA) (hWB : WuestholzBeta7) (hWX : WuestholzX7 LA)
    (hTo : TorsionX7 LA) (h0 : (0 : Fin 3 → ℂ) ∈ LA) (v : Fin 3 → ℂ) (hv : v ∈ LA) (hnt : ¬ TorsionTriple v) :
    v 0 ≠ 0 ∧ ∀ c : ℂ, IsAlgebraic ℚ c → v 1 / v 0 ≠ c * (perA 3 / perA 1) := by
  have h0' := slot_ne_zero LA hTo v hv hnt 0
  refine ⟨h0', fun c hc h => ?_⟩
  by_cases hc0 : c = 0
  · subst hc0
    exact slot_ne_zero LA hTo v hv hnt 1 (by simpa [h0'] using h)
  · exact x7a LA hW hWB hWX hTo h0 v hv hnt c hc hc0 (by rw [div_eq_iff h0'] at h; rw [h]; ring)
```

  Both compile against commit 041b468 (`TorX7.lean`; only the standard axioms, via `x7a`). `x7a_full` is literally
  "`z₁(v) ≠ 0` and `z₂(v)/z₁(v) ∉ ℚ̄·P₃/P₁`". Recommendation: put `slot_ne_zero` and `x7a_full` in `X7Torsion.lean`, and
  either keep `x7a` as a lemma or rename.
* For `x7b` no change is needed. A by-product of `slot_ne_zero` (non-torsion `v` has `z₃(v) ≠ 0`) could be mentioned
  but is not in the paper's (b).
* **`h0 : 0 ∈ LA`.** It is used to put `v₃ = 0` (resp. `v₁ = v₂ = 0`) into Theorem X7, exactly as in the paper's data.
  It holds for every intended instance that contains the logarithm of `O`. It is harmless, but it should be listed in
  TRUST.md (or discharged as in §4).

## 4. Opinion: can the literal Cor. X7 (a), (b) be stated in Lean 4 + Mathlib today?

**What the literal statement involves.**
* `C(ℚ̄)` as points of the smooth projective model, including the three ramification points `(0,0)`, `(1,0)`, `∞`.
* Paths on the compact Riemann surface, with `y` continued along them.
* The integrals `∫_O^Q dx/y^{7−s}`. They depend on the path only modulo `Ω(A)`; the statement is meant for every path.
* "`Q − O` of infinite order in `A`", a statement about the group law of `Jac C`.

**What Mathlib lacks (to my knowledge, mid-2026).**
* It has general complex manifolds, but no construction of the compact Riemann surface of a plane curve. That would
  need the normalisation at `∞` and charts at ramification points.
* It has no integration of holomorphic 1-forms on manifolds with homotopy invariance, no `H₁` with periods, and no
  Jacobian, Abel–Jacobi map or Abel's theorem.
* So a definition through `Jac C` and `AJ : Div⁰(C) → Jac C` is out of reach. It would be a large project (Riemann
  surfaces plus Abel–Jacobi), unrelated to this paper.

**An elementary faithful statement is possible now.** This is the sketch in `TorX7.lean`; it compiles.
* An `AJPath` is:
  - a C¹ map `p : ℝ → ℂ` with `p(t) ∉ {0, 1}` on `[0,1]`;
  - a continuous `y` on `[0,1]` with `y⁷ = p(1−p)`;
  - algebraic endpoint data `(p 0, y 0)` and `(p 1, y 1)`.
  Its triple is `z_s = ∫₀¹ p′(t)/y(t)^{6−s} dt`, built from `intervalIntegral` and `deriv`. `AJ1` is the set of these
  triples, and `LAJ := span_ℚ AJ1`.
* **Why this is faithful (classical; unproved in Lean).**
  - `C ∖ {3 ramification points}` is the 7-sheeted cover of `ℂ ∖ {0,1}` given by `y`. Every path between two
    non-branch points of `C` is homotopic in `C` to the lift of a C¹ path avoiding the branch points.
  - The forms are holomorphic on all of `C`, so the values attained are exactly the coset `AJ(Q − O) + Ω(A)`.
  - Since `Ω(A) ⊂ Fγ`, "for every path" and "for one path" give the same non-torsion statement.
  - `span_ℚ AJ1 = Λ(A)`, by Jacobi inversion (every point of `A(ℚ̄)` is a sum of `≤ 3` differences) and divisibility.
* **"Infinite order".** State it as `¬ TorsionTriple v`. This is equivalent through `ℚ⊗Ω(A) = Fγ` (§1), the same fact
  the paper uses. An algebraic statement through principal divisors would need the function field of `C` with
  divisors, which Mathlib does not have for this curve.
* **Gaps of the sketch.**
  - Endpoints at the ramification points (or `∞`) are excluded. They can be added with improper integrals: the
    integrand is integrable at a branch endpoint, since `dx/y^k = 7t^{6−k}(…)dt` in the uniformiser. Alternatively, note
    that the cases `O` or `Q` a ramification point differ from the affine case by an explicit torsion triple.
  - The integrals are attached to `LA` only through the named inputs. Lean would not prove that `AJ1` consists of
    logarithms of `A`.
* **What this buys.**
  - `x7a_full` and `x7b` for `LA = LAJ`, with `h0` discharged by `Submodule.zero_mem`, are literal statements of Cor.
    X7intro(a) and Cor. X7(b) about explicitly defined complex numbers. The integrals `∫_O^Q dx/y^5`, `∫_O^Q dx/y^6` are
    `v 1`, `v 0`.
  - The named inputs `Thm11KappaX7 LAJ`, `WuestholzX7 LAJ` and `TorsionX7 LAJ` become claims about a concrete set.
    Their truth still rests on the classical facts of §1–§2 plus Abel–Jacobi theory, but the "uninterpreted parameter"
    gap disappears.
  - Effort: about 40 lines, all definitions; no proofs beyond `zero_mem`.

**Is the parametric formulation acceptable?** Yes, as a documented substitute.
* Nothing false can be derived: for a bad `LA` the hypotheses fail and the theorems are vacuous.
* The pattern is the one already accepted for `WuestholzMX`/`LogNat` and for `thmX7`.
* The concrete `LAJ` instance is a cheap fidelity upgrade, and I recommend it (#15). It is not required for
  correctness.

## 5. Suggested TRUST.md text

Coverage rows (replacing l. 162 and l. 164):

> | Theorem X7 | `AbVar.thmX7_torsion` (and `thmX7`, `propX7_K`, `propX7`) | ✔ for the parameter `LA`: `q₁ = q₂ = 0`, `v₁, v₂, v₃` torsion triples (`TorsionTriple`: `v ∈ Fγ = ℚ⊗Ω(A)`), `u ∈ ℚ(α)Ω`; Prop. X ◐ (first coordinate) |
> | Cor. X7 (a), (b) | `AbVar.x7a_full` (or `x7a`), `AbVar.x7b` | ✔ for the parameter `LA` (with `0 ∈ LA`); the literal statements about `∫_O^Q dx/y^k` are the instances `LA = LA_A` (see "The parameter `LA`") |

§3 row:

> | `AbVar.TorsionX7 LA` | (i) `v ∈ LA`, `z_s(v) ∈ ℚ̄·P_{s+1}` for one `s` ⇒ `v` is a torsion triple; (ii) `u ∈ 𝓛_E`, `u ∈ ℚ̄Ω` ⇒ `u ∈ ℚ(α)Ω` | Wüstholz 1989 on `A²` at `(v, γ)`: the smallest subgroup is the graph of `x ∈ End⁰(A) = ℚ(ζ₇)`, so `v = xγ`; for `c = 0`, Wüstholz on the simple `A` gives `v = 0`; (ii) the same on `E²` (or Masser 1975). [`reviews/REFEREE_TORSION_X7.md`](reviews/REFEREE_TORSION_X7.md): TRUE for every `LA ⊆ LA_A` (not for the `ℚ̄`-span, incoherent or rescaled triples) |

Paragraph (appended to "The parameter `LA`"):

> **Torsion and Corollary X7 (a), (b).** `TorsionTriple v` says that `v = xγ` for some `x ∈ ℚ(ζ₇)`, written in
> coordinates as `v_s = σ_{s+1}(x)P_{s+1}` with `σ_{s+1}(ζ) = ζ^{s+1}`, the convention of `aGen`. This is equivalent to
> "`exp_A(v)` is a torsion point" because `ℚ ⊗ Ω(A)` is the line `Fγ`; that fact is classical and not proved in Lean.
> The named input `TorsionX7 LA` is the torsion step of the paper's proof of Theorem X. It is true for every subset of
> `LA_A` in the normalisation `z_s(γ) = P_{s+1}`. Unlike `WuestholzX7`, it is false for `ℚ̄`-multiples of logarithms
> (e.g. `{√2·perT}`), for triples mixing coordinates of different points, and for rescaled coordinates. `x7a` and `x7b`
> also assume `0 ∈ LA` (the logarithm of `O`). Lean has no Riemann surfaces or Jacobians, so Cor. X7 (a), (b) are
> stated for the parameter `LA`. The literal statements about `∫_O^Q dx/y^k` for `O, Q ∈ C(ℚ̄)` are their instances
> for the set of Abel–Jacobi triples. "Infinite order of `Q − O`" corresponds to `¬ TorsionTriple`, independently of the
> path, since changing the path adds an element of `Ω(A) ⊂ Fγ`.

If #15 is adopted, replace the last two sentences with: "`LAJ` (`X7Torsion.lean`) is the `ℚ`-span of the triples
`∫ p′/y^{6−s}` along lifts of C¹ paths in `ℂ ∖ {0,1}` between points of `C(ℚ̄)`. `x7a_LAJ` and `x7b_LAJ` are Cor. X7 (a),
(b) for it. That `LAJ = LA_A` (Abel–Jacobi, Jacobi inversion) is a classical soundness fact, not proved in Lean."

Also update l. 200 ("What is still missing"): delete "the torsion step" and "definitions of `Λ(A)` … to state Cor.
X7 (a), (b) literally". If #15 is adopted, replace the latter with "ramification-point endpoints".

## Falsification attempts (none succeeded)

* **Wrong exponent sign in `TorsionTriple`.** The defined set is invariant under it (§1). A known torsion point is
  reproduced to 2e-40.
* **`c = 0` with `v ≠ 0`.** Excluded by Wüstholz on the simple `A`, for each single slot.
* **One slot algebraic, others not.** Impossible: the graph argument forces all three coordinates.
* **`ℚ` vs `ℚ̄` coefficients in `TorsionTriple`.** `ℚ` is right: `ℚ⊗Ω(A)` is a `ℚ`-space, and the `ζ^e` supply the
  `F`-structure.
* **Elliptic part.** The analytic representation of `End(ℂ/Ωℤ[α])` is the identity embedding of `ℚ(α)`, so
  `ℚΛ_E = ℚ(α)Ω` exactly.
* **Hidden extra hypotheses.** `thmX7_torsion` adds only `hTo`. `x7a`/`x7b` add `hTo` and `h0`, both true for the
  intended instance.

## Verdict lines

* Item 1 (`TorsionTriple` = "exp_A(v) torsion"; convention vs `aGen`): **CORRECT**.
* Item 2 (`TorsionX7` (i) and (ii)): **TRUE WITH NOTES**. Both clauses are true for every `LA ⊆ LA_A` in the `perT`
  normalisation, including `c = 0` (`v = 0`), `v = perT` and a single slot; (ii) has no condition. (i) is false for the
  `ℚ̄`-span, incoherent and rescaled triples, which is narrower than `WuestholzX7`; document this.
* Item 3 (`thmX7_torsion`, `x7a`, `x7b` vs Theorem X7, Cor. X7 (a), (b)): **CORRECT WITH NOTES**. `thmX7_torsion` and
  `x7b` are exact. `x7a` omits `c = 0` and `z₁(v) ≠ 0`; these are closable from the existing `TorsionX7` (`x7a_full`,
  proved in the scratch file, no new input). `h0 : 0 ∈ LA` should be documented.
* Item 4 (literal Cor. X7 (a), (b) in Lean): **opinion**. The Riemann-surface/Jacobian formulation is not feasible in
  Mathlib today. An elementary path-integral formulation (`AJ1`/`LAJ`) is feasible and faithful modulo classical
  Abel–Jacobi facts. The parametric `LA` statement with the documented intended instance is acceptable; TRUST.md text
  is drafted in §5.
