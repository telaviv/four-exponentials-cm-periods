# Referee report: the level-seven model `gmX7`, `Thm11KappaX7`, Proposition X / Theorem X7 / Corollary X7(c)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope.**
* In full: `CM4E/AbVar/Fermat7.lean`, `CM4E/AbVar/FrameX.lean`, `CM4E/AbVar/X7.lean`.
* For context: `CM4E/Waldschmidt.lean`, `CM4E/AbVar/Basis.lean` (`thetaD`, `KspanD`, `IsAdaptedBasisD`, `coordsD`),
  `CM4E/Gen/ThmM.lean` (`LogE`), `TRUST.md`.
* Paper: draft [II], §`sec:X` (set-up, Prop. `prop:X` l. 614, Theorem X l. 618, proof of the
  proposition and of the theorem), §`sec:X7` (l. 726–789: Theorem X7 l. 750, Cor. X7 l. 761), Cor. `cor:X7intro` (l. 126).
* Format and baseline: `reviews/REFEREE_HYP_MXP.md`.

**Process.** No project file other than this report and `reviews/checks/hypx7/` was edited, and no git command was run.
The scratch files are:
* `reviews/checks/hypx7/check_x7.py` and `check_x7.out`: numerics (mpmath, 60 digits);
* `reviews/checks/hypx7/check_x7_g2.py` and `check_x7_g2.out`: `g₂`, `g₃` at 120 digits;
* `reviews/checks/hypx7/AxX7.lean` and `AxX7.out`: the axiom audit.

## Verdicts

* **Item 1 (soundness facts of `Fermat7.lean`: the period triple, the CM action, the lattice of `E`): CORRECT.**
  - (a) One explicit closed loop on `C` gives `∫ dx/y^{7−j} = perA j` for `j = 1, 2, 3` simultaneously, to 1e-60. The
    loop is integrated numerically with `y` continued analytically along it.
  - (b) `[ζ]^*(dx/y^{7−j}) = ζ^j dx/y^{7−j}`, so `[ζ^e]γ` has coordinates `(ζ^{(s+1)e} perA(s+1))_s`, exactly as `aGen`
    writes it. The six cycles `[ζ^e]γ`, `e < 6`, span a lattice of rank 6.
  - (c) `g₂`, `g₃` of `omega7·ℤ[α]` are algebraic: roots of cyclic cubics over `ℚ`, at 120 digits. `j = −3375`.
* **Item 2 (`FrameX.lean`, `X7.lean`: `gmX7`, `Thm11KappaX7`, uniform `sub`, `d₂`, count, multipliers, `zp`/`zq`):
  CORRECT WITH NOTES.**
  - The model is sound for every adapted basis `b` and every `LA` made of eigen-coordinate triples of logarithms of
    algebraic points of `A`. In particular it is sound unconditionally for `LA = ∅` (used by `x7c`).
  - Lean's `A^{3r}` is the paper's `A″`, up to an explicit `F`-linear isogeny, and the slot forms are exactly the ones
    that descend.
  - No lifting is needed: Lean applies W88 directly to `A^{3r} × E^{3r} × G_a²`, and every generator is a genuine
    logarithm of that group.
  - Notes: `LA` is an uninterpreted parameter (a trust note), and `TRUST.md` is stale.
* **Item 3 (statement fidelity: `propX7_K`/`propX7`, `thmX7`, `x7c`): CORRECT WITH NOTES.**
  - `propX7` is a faithful weakening of Prop. X: first coordinate only, `ℚ̄` coefficients.
  - `thmX7` proves Theorem X's conclusion (`q₁ = q₂ = 0`, `z_j(v_j) ∈ ℚ̄P_j`, `u ∈ ℚ̄Ω`) for the level-7 instance. This
    is the first sentence of Theorem X7 up to the torsion step, which is not formalised.
  - `x7c` is exactly Cor. X7intro(b), the "equivalently" form of Cor. X7(c), with Mathlib's `Complex.betaIntegral`.
  - The extra named inputs `WuestholzBeta7` and `WuestholzX7 LA` are true. Derivations are below.

**Axioms.** I ran `lake env lean reviews/checks/hypx7/AxX7.lean` (28 s; the oleans are newer than the sources).
* Six declarations use only `propext`, `Classical.choice` and `Quot.sound`: `relation_R`, `frameX_false`, `propX7_K`,
  `propX7`, `thmX7` and `x7c`.
* The three files contain no `sorry`, `axiom` or `native_decide`.

**No FATAL or MAJOR issue was found.**

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | period triple (a) | the loop "circle around `x=1` (ccw) then circle around `x=0` (cw)", both from `x = 1/2`, with `y` continued, is closed and contracts to the paper's `γ`. It gives `perA 1, 2, 3` to 1.2e-60, 6.2e-61, 6.4e-61 |
| 2 | OK | CM direction (b) | the push-forward of the loop by `y ↦ ζy` gives `ζ^j·perA j` to 2e-61, so `σ_{s+1}(ζ) = ζ^{s+1}` in Lean's 0-indexed `s` |
| 3 | OK | lattice of `A` | `det` of the real `6×6` matrix of `[ζ^e]γ` (`e < 6`) is `1.27e7 ≠ 0`, so `per` is all of `ℚ ⊗ Ker exp` on each copy of `A`. The control with "type" `{1,6,2}` gives `det = 0` |
| 4 | OK | lattice of `E` (c) | `g₂(Ωℤ[α]) = 0.01235384…` and `g₃ = 0.000324935…` are real, and they are roots of irreducible cubics with square discriminants. `j = −3375`. `Ωℤ[α] = λ·L(y² = 4x³ − 140x − 392)` with `λ⁻²` a root of `x³ − 196x² + 10976x − 153664` |
| 5 | OK | `lam` | `aGen t j e v = [ζ^e]v` in copy `(t, j)`, `eGen p u`, `eGen p (αu)` and the `G_a` constants are all in `Λ(G″)`, and `Λ(G″)` is a `ℚ`-space. Requires `LA ⊂` eigen-triples of `Λ(A)` (#12) |
| 6 | OK | `per` | `[ζ^e]γ`, `Ω` and `αΩ` are periods; `perX7 = ℚ ⊗ Ker exp_{G″}` (#3), so `κ_Lean = κ_W88` |
| 7 | OK | group / `A″ = A^{3r}` | `A^n/B_ker ≅ A^{3r}` via `M = (φ_t^{-1}∘ψ_{σ_{t+1}})_t`, with `φ_t(s) = Σ_j b_j σ_{t+1}(s_j)`. The descended slot forms are exactly `mu1`, `mu2` (derivation below). Not needed for soundness, only for matching the paper |
| 8 | OK | uniform `sub` | no nonzero connected `H ⊂ A^{3r} × E^{3r} × G_a²` has `T_H ⊂ ker Ψ″`, for every adapted `b` |
| 9 | OK | `d₁ = 0`, `d₂ = 12r + 2` | the truth is `d₀ = 2`, `d₁ = 0`, `d₂ = 2n = 12r`. Lean overestimates `d₂`, which only weakens the hypothesis |
| 10 | OK | count | `3n > 4n + 4 − κ` with `κ ≥ 2n` needs `n ≥ 5`, and `n = 6r ≥ 6` (`hcount`: `2·12r + 4 < 30r`). Lean's margin is `n − 4`, against the paper's `n` (with `d₂ = 2n`) |
| 11 | OK | multipliers `1, 4, 5`; `zp`/`zq` | `σ₂(ζ)⁴ = ζ⁸ = ζ` and `σ₃(ζ)⁵ = ζ¹⁵ = ζ`. The `zp`/`zq` table holds to 1e-61. `{1, ζ, ζ²}` is a `k`-basis of `F` (embedding determinant `129.6 ≠ 0`). All three facts are Lean-proved anyway (`zeta_expand`, `zeta7_pow_eight/fifteen`); they affect only the lifts, not soundness |
| 12 | TRUST NOTE | `Thm11KappaX7 LA`, `WuestholzX7 LA` (`X7.lean:117`, `:489`) | `LA` is an uninterpreted `Set (Fin 3 → ℂ)`. Both hypotheses are sound **only** for `LA ⊆ {(z₁(v), z₂(v), z₃(v)) : v ∈ Λ(A)}`. For other `LA` they can be false, and then `propX7`/`thmX7` say nothing. `x7c` uses `LA = ∅` and carries no such caveat |
| 13 | OK | Lemma U range | true `d₀ = 2`: `2N = 4n + 2 ≥ 4 + κ` iff `κ ≤ 4n − 2`. `κ ≥ 4n − 1` forces `V ⊇ T(A^{3r} × E^{3r})`, which lies in `sub`, so the conclusion holds trivially (below) |
| 14 | OK | `propX7_K`/`propX7` vs Prop. X | the hypothesis is (eq:X) with `a = z₁`, `b = z₂`, `c = z₃`, `d = E`. The conclusion is the first coordinate of `Kw + Kw′` (`w′ = (Ω, βP₂/μ′) = σ·(Ω, …)` by `relation_R`) |
| 15 | OK (scope) | `thmX7` vs Theorem X7 | Lean concludes `q₁ = q₂ = 0`, `z_j(v_j) ∈ ℚ̄P_j` and `u ∈ ℚ̄Ω` (Theorem X's conclusion). The torsion conclusion of X7 is not formalised, as stated in the brief |
| 16 | OK | `WuestholzBeta7`, `WuestholzX7` | both are true consequences of Wüstholz 1989 (derivations below) |
| 17 | OK | `x7c` vs Cor. X7(c) | identical to Cor. X7intro(b). Dividing `P₁P₂, P₁P₃, P₁, P₃` by `P₁` gives `1, B(2/7,2/7), B(3/7,3/7), B(3/7,3/7)/B(1/7,1/7)` up to `ℚ(ζ)^×` factors. `betaIntegral` agrees with `betaG` (`betaG_eq_betaIntegral`) |
| 18 | MINOR (docs) | `TRUST.md:160` and §2, §3 | stale. l. 160 says "Theorem X, Prop. 15, Theorem X7, Cor. X7: ✗ not formalised". §2 lacks `AbVar.propX7`, `thmX7`, `x7c`. §3 lacks rows for `AbVar.Thm11KappaX7`, `WuestholzBeta7` and `WuestholzX7` |
| 19 | COSMETIC | `Waldschmidt.lean:12–13` | the instance list omits `AbVar.Thm11KappaX7` |
| 20 | COSMETIC | `X7.lean:30` | "`[ζ^e]` acts on `z_s` by `ζ^{(s+1)e}` (`σ_s(ζ) = ζ^s`)" mixes the 0-indexed `s` of the code with the 1-indexed `σ_s` of the paper. Write `σ_{s+1}(ζ) = ζ^{s+1}` |
| 21 | NIT | `X7.lean:20–21` | the docstring says the paper's `G″ = A″ × G_a²` "is written as" `A^{3r} × E^{3r} × G_a²`. More precisely, the two are isogenous via #7, and Lean never needs the isogeny |
| 22 | NIT (paper) | Cor. X7intro(b), l. 133–134 | the Gamma forms hold "up to the algebraic factors `sin(3π/7)`, `sin(π/7)`". The text says "equivalently", which is correct for `ℚ̄`-independence, but the factors could be named. Not formalised in Lean |

## Details

### 1. Numerical soundness facts [Numerical, 60 digits; `g₂`, `g₃` at 120]

**(a) One cycle, the whole triple.**
* Start at `x = 1/2` with `y₀ = 4^{−1/7} > 0`.
  - Piece 1: `x = 1 − e^{iφ}/2`, `φ ∈ [0, 2π]`, with `y = x^{1/7}·2^{−1/7}e^{iφ/7}`. Here `x^{1/7}` is principal, since
    `Re x ≥ 1/2`. The piece ends at `ζy₀`.
  - Piece 2: `x = e^{−iψ}/2`, with `y = ζ·2^{−1/7}e^{−iψ/7}(1−x)^{1/7}`. It ends at `y₀`.
  - `y⁷ = x(1−x)` along both pieces and continuity at both junctions are asserted in the script.
* Shrinking the circles: the loop is `[0,1]` on the sheet `y > 0` minus `[0,1]` on the sheet `ζ·(y > 0)`. This is the
  paper's `γ`.
* Numerical integration of `dx/y^k` (`k = 6, 5, 4`) along this single loop gives `perA 1, 2, 3` to about 1e-60. So the
  triple is consistent: it is `(z₁, z₂, z₃)(γ)` for one cycle, not each value up to its own constant.
* The real-segment check `∫₀¹(x(1−x))^{−k/7}dx = B(j/7, j/7)` agrees to 1e-28 (`j = 3`), 1e-18 (`j = 2`) and 8e-9
  (`j = 1`). The last is limited only by tanh-sinh at the exponent `−6/7`, and the loop integral has no such limit.

**(b) Direction of the CM action.**
* Pulling back by `y ↦ ζy` gives `dx/y^k ↦ ζ^{−k}dx/y^k`, and for `k = 7 − j` this is `ζ^j`. Hence
  `z_s([ζ]_*v) = ζ^{s+1}z_s(v)` (0-indexed `s`) and `σ_{s+1}(ζ) = ζ^{s+1}`.
* Numerically, the pushed loop gives `ζ^j·perA j` to 2e-61. This is exactly `aGen`'s factor `ζ^{((s:ℕ)+1)·e}`.
* For soundness the direction is in fact irrelevant:
  - `aGen` allows every `e ∈ ℕ`, and `[ζ^{-1}] = [ζ⁶]`;
  - the `sub` argument works for any three distinct embeddings.
* The direction matters only for the Lean-proved multipliers `4`, `5`.

**(c) `E`.**
* `τ = α = (−1+√−7)/2` has `Im α > 0`. Eisenstein series give `g₂ = (4π⁴/3)E₄(α)/Ω⁴` and `g₃ = (8π⁶/27)E₆(α)/Ω⁶`.
* Both are real and algebraic:
  - `g₂` is a root of `−1075648x³ + 384160x² − 14700x + 125` (disc `2¹²5⁶7¹⁰13²`);
  - `g₃` is a root of `−60236288x³ + 2612288x² − 3920x + 1` (disc `2¹⁸7¹⁴13²`).
  - Both cubics are irreducible and cyclic, so both values lie in `ℚ(ζ₇)⁺`. The residual at 120 digits is about 1e-119.
* `j = 1728g₂³/(g₂³ − 27g₃²) = −3375`, so the endomorphism ring is the maximal order `ℤ[α]`.
* Direct truncated lattice sums agree to 1e-5 for `g₂` and 1e-10 for `g₃`.
* So `E7` (`ω₁ = B(1/7, 2/7)`, `ω₂ = αω₁`) is the period lattice of an elliptic curve over `ℚ̄`. This is the
  Chowla–Selberg fact the model needs. `LogE E7` refers to the `℘` of this lattice, so it is the correct `𝓛_E`.

### 2. Soundness of `gmX7` [Proved, modulo standard CM theory]

**The group.**
* `G″ = A^{3r} × E^{3r} × G_a²`, of dimension `9r + 3r + 2 = 2n + 2` with `n = 6r`. It is defined over `ℚ̄`: `A = Jac(C)`
  is over `ℚ`, and `E` is over `ℚ̄` by #4.
* The tangent coordinates are `ℚ̄`-rational:
  - on `A`, `z₁, z₂, z₃` are dual to the `ℚ`-rational basis `dx/y⁶, dx/y⁵, dx/y⁴` of `H⁰(Ω¹)` (holomorphic exactly for
    `k = 4, 5, 6`: orders `6 − k` at `0`, `1` and `2k − 8` at `∞`);
  - on `E`, `dz = dx/y`.
* `algQX7` is therefore the right `ℚ̄`-structure.
* `A` is simple with `End⁰(A) = F = ℚ(ζ)`: the type `{1, 2, 3}` has trivial stabiliser in `(ℤ/7)^×`. I checked all
  `t = 2, …, 6`.
* `A` is not isogenous to `E` (dimensions 3 and 1).

**`A″ = A^{3r}` (#7).** In the paper, `A^n` (`n = 6r` copies, `θ_{(j,e)} = ζ^e b_j`) carries three slot maps on `F^n`:
`ψ_σ(s) = Σ_h θ_h σ(s_h) ∈ K`.
* Via `F ⊗_ℚ K ≅ ∏_{τ: F→K} K`, these are three distinct projections. So `(ψ_{σ₁}, ψ_{σ₂}, ψ_{σ₃}) : F^n → K³` is onto,
  and `F^n/ker` has `F`-dimension `3r`. This is Lemma K′: `dim A″ = 3n/2`.
* Give the `t`-th factor `K` the twisted structure `f·k = σ_{t+1}(f)k`. Then `φ_t(s) = Σ_j b_j σ_{t+1}(s_j)` is an
  `F`-isomorphism `F^r → K`, because `b` is an `F`-basis and `σ_{t+1}(F) = F`.
* So `M = (φ_t^{−1}ψ_{σ_{t+1}})_t : F^n → F^{3r}` is onto, and it defines `A^n/B_ker ~ A^{3r}`.
* On the `σ_{t+1}`-eigenspace, `ψ_{σ_{t+1}} = φ_t∘M_t` reads `Σ_j b_j y^{(t)}_j`, where `y^{(t)}` are the
  `σ_{t+1}`-coordinates of block `t`. This form is unique, because `σ(M)` is onto, and it is zero on the other blocks.
  These are exactly `mu1`'s block-0 term `Σ b_j zA 0 0 j` and `mu2`'s terms `Σ b_j zA 1 1 j + Σ b_j zA 2 2 j`.
* Likewise `E^n/B′_ker ≅ E^{3r}` via the `k`-basis `{ζ^e b_j}_{e<3}` of `K`. This gives `mu1`'s term
  `Σ ζ^e b_j zE(j, e)`.
* **Lifting is not an issue.** Lean applies W88 to `A^{3r} × E^{3r} × G_a²` itself. Every element of `lamX7` is a
  logarithm of an algebraic point of *that* group: `[ζ^e]` is an automorphism defined over `ℚ(ζ)`, `[α] ∈ End(E)` is
  defined over `ℚ̄`, and `G_a` has `exp = id`. Each element of `perX7` is a period. No element of `G^n` is involved.

**Uniform `sub` (#8).**
* Let `H ≠ 0` be connected. Then `H = L × B × B′`:
  - `Hom(abelian, G_a) = 0`, so the section of `H` over its abelian image vanishes;
  - `Hom(A, E) = 0` gives the product of the abelian parts.
* So `T_H ⊂ ker Ψ″` forces `L ⊂ ker`, `T_B ⊂ ker` and `T_{B′} ⊂ ker` separately.
* **`L`.** `Ψ″|_{G_a²} = id`, so `L = 0`.
* **`B = B_S ⊂ A^{3r}`, with `S ⊂ F^{3r}` an `F`-subspace.**
  - `T(B_S) = ⊕_σ σ(S) ⊗ ℂ` is the direct sum of its eigen-parts, since it is an `F ⊗ ℂ`-submodule.
  - So `μ₂ = Σ b_j z₃^{(2,j)} + Σ b_j z₂^{(1,j)}` vanishes on `T(B_S)` iff its `σ₃`-part and its `σ₂`-part vanish
    separately. No cancellation between the two slots feeding the second target coordinate is possible.
  - Each part vanishes iff `Σ_j b_j σ_{t+1}(s_{t,j}) = 0` for all `s ∈ S`.
  - `σ_{t+1}(s_{t,·}) ∈ F^r`, and `b` is `F`-independent (`F = ℚ(ζ) ⊂ K ⊂ ℂ`, the same embedding as `zeta7`). So
    `s_{t,·} = 0` for `t = 0, 1, 2` (block 0 via `μ₁`'s `A`-part), and hence `S = 0`.
  - The unused eigen-coordinates of each block are harmless: every nonzero `s` has a nonzero block, and that block's
    used slot detects it.
* **`B′ = B′_{S″} ⊂ E^{3r}`, with `S″ ⊂ k^{3r}`.**
  - `T = span_ℂ S″`, using the identity embedding, since `[α]` acts on `T₀E` by `α` for the lattice `Ωℤ[α]`.
  - `μ₁` vanishes on `T` iff `Σ_{j,e<3} ζ^e b_j s_{j,e} = 0` for all `s ∈ S″`.
  - `{ζ^e b_j}_{j<r, e<3}` is a `k`-basis of `K`: `b` is an `F`-basis and `{1, ζ, ζ²}` is a `k`-basis of `F`, since
    `[F : k] = 3`; numerically the determinant is `129.6`. So `s = 0`.
* Hence `T_H ⊄ ker Ψ″`. `T_H` is `ℚ̄`-rational, so it contains an `algX` vector `x` with `Ψ″x ≠ 0`.
* Only "`b` is an `F`-basis of a number field `K ⊂ ℂ`" is used. `IsAdaptedBasisD zeta7 6 b` gives this: `K = span_ℚ θ` is
  a field, `ζ ∈ K` (`zeta7_mem`), and `θ = (ζ^e b_j)_{e<6}` is a `ℚ`-basis. So `Thm11KappaX7` is sound for **every**
  quantified `b`.

**Falsification attempts on `sub`.** None succeeded.
* Mixed `σ₂`/`σ₃` kernels are excluded by the eigen-decomposition.
* Mixed `A`/`E` kernels are excluded because `Hom(A, E) = 0`.
* Graphs into `G_a²` are excluded because `Hom(abelian, G_a) = 0`.
* `ᾱ` in place of `α` on `E`: the `k`-independence argument is symmetric under conjugation. In any case the analytic
  representation for `Ωℤ[α]` is `α`.
* Reversing the direction of `[ζ]` relabels `σ_{s+1}` as `σ_{−(s+1)}`. These are still three distinct automorphisms, so
  the argument is unchanged.

**`d`-fields and count (#9, #10).**
* The truth is `d₀ = 2`, `d₁ = 0`, `d₂ = 2n`. Lean has `d₂ = 2n + 2`, which makes `d₁ + 2d₂` larger, and
  `d − 1 − t ≥ 0`. So the premise of `HyperplaneKappa` is stronger, and the hypothesis is weaker.
* In `frameX_false`: `m = 3n`, `κ ≥ 2n`, `t = dim ker Ψ″ = 2n`, `d − 1 − t = 1`. So
  `3n > 4n + 4 − κ ⇐ 3n > 2n + 4 ⇐ n ≥ 5`.

**Lemma U range (#13).**
* With `d₀ = 2`, Lemma U covers `2N = 4n + 2 ≥ 2d₀ + d₁ + κ = 4 + κ`, that is, `κ ≤ 4n − 2`.
* Suppose `κ ≥ 4n − 1`. Then `Y ∩ per` is a `ℚ`-subspace of `Ker exp ⊗ ℚ ⊂ T_ab = T(A^{3r} × E^{3r})` of rank
  `≥ 4n − 1`. Lattice-independent vectors are `ℝ`-independent, so it spans a real subspace of dimension `≥ 4n − 1`.
* This cannot lie in a complex hyperplane of `T_ab` (real dimension `4n − 2`). So `V ⊇ T_ab`.
* `T_ab` is in `sub`: it contains `(single3 0 0 j, 0)`, with `μ₁ = b_j ≠ 0`. So the conclusion holds trivially.
* The paper's own instance has `κ = 2n`.

### 3. Statement fidelity

**`propX7_K`/`propX7` vs Prop. X.**
* The hypothesis is (eq:X) at `(a, b, c, d) = (z₁, z₂, z₃, E)`: `(Σc₁z₁(v₁) + Σd·u + q₁)·βP₃ = (Σc₃z₃(v₃) + Σc₂z₂(v₂) + q₂)·P₁`.
  Coefficients are in `K`, `vᵢ ∈ LA ∪ {γ}` and `u ∈ 𝓛_E`.
* Independent `v`'s per slot are allowed. This is the paper's (Ch) remark (l. 635), and Lean realises it with separate
  blocks.
* The conclusion `x ∈ KP₁ + KΩ` is the first coordinate of `V ∩ Ψ(Λ_K(G)) = Kw + Kw′`, with `w = (P₁, βP₃)` and
  `w′ = (Ω, βP₂/μ′)`. That `w′ ∈ ℂw` is `relation_R`.
* `σ = βP₃/P₁ ∉ ℚ̄` comes from `WuestholzBeta7`, in place of the paper's `P_c/P_a ∉ ℚ̄`.
* `propX7` takes `K` large enough to contain all coefficients. This is a faithful weakening.

**`thmX7` vs Theorem X7.**
* Hypotheses: `v₁, v₂, v₃ ∈ LA`, `u ∈ LogE E7`, `q₁, q₂ ∈ ℚ̄` and `β ∈ ℚ̄^×`, with the displayed relation. These are
  the paper's hypotheses.
* Conclusion: `q₁ = q₂ = 0`, `z_j(v_j) ∈ ℚ̄P_j` and `u ∈ ℚ̄Ω`. These are Theorem X's first sentence specialised to level
  seven. The torsion step, Theorem X7's actual conclusion, is not formalised.
* The deduction uses `WuestholzX7 LA`, the paper's "slot splitting" paragraph.

**`x7c` vs Cor. X7(c).**
* `x7c` is Cor. X7intro(b) verbatim, for `Complex.betaIntegral` at complex `2/7, 3/7, 1/7`.
* `hBj` reduces it to `perA j/(1 − ζ^j)`. The proof follows the paper's (c): substitute `relation_R` and take both
  coordinates.
* It needs only `Thm11KappaX7 ∅` and `WuestholzBeta7`, and both are true.
* The Gamma identities for `B(2/7, 2/7)` and `B(3/7, 3/7)` (paper l. 785–787) were checked to 6e-61.

### 4. The named inputs are true [Proved modulo Wüstholz 1989]

* **`WuestholzBeta7`.** Take the point `(1, γ, Ω) ∈ T(G_a × A × E)`; its exponential is algebraic. The smallest
  algebraic subgroup whose Lie algebra contains it is `G_a × B × B′`, with `γ ∈ T_B` and `Ω ∈ T_{B′}`. Then `B = A`
  (`A` is simple and `γ ≠ 0`) and `B′ = E`. So a `ℚ̄`-form `a₀t + a₁z₁ + a₂z₂ + a₃z₃ + a₄z_E` vanishing there vanishes
  identically, and all `a_i = 0`.
* **`WuestholzX7`, first conjunct.** Take the point `(1, v, γ, u, Ω)` on `G_a × A² × E²` and the form
  `qt + z₁^{(1)} − cz₁^{(2)} + z_E^{(1)} − c′z_E^{(2)}`.
  - The smallest subgroup is `G_a × B_A × B_E`, so `q = 0`, and the `A`- and `E`-parts vanish separately at the point.
  - With `v = γ` this gives `c = 1`, which is still consistent with the stated conclusion.
* **`WuestholzX7`, second conjunct.** Take the point `(1, v, v′, γ)` on `G_a × A³` and the form
  `qt + z₂^{(1)} − c′z₂^{(3)} + z₃^{(2)} − cz₃^{(3)}`.
  - `T(B_S)` is stable under the eigen-projections, so the `σ₂`- and `σ₃`-parts of the point lie in `T(B_S)` separately.
    Each part of the form then vanishes there.
* All three need `LA ⊆` eigen-triples of `Λ(A)` (#12).

## Suggested fixes

1. **`TRUST.md`.**
   - l. 160: set Theorem X7 to ◐ (`AbVar.thmX7`: Theorem X's conclusion at level seven; torsion not formalised), Prop.
     X to ◐ (`propX7`, first coordinate), and Cor. X7(c) to ✔ (`x7c`).
   - §2: list the three theorems.
   - §3: add a row for `hW : AbVar.Thm11KappaX7 LA`. It is W88 §5d for `A^{3r} × E^{3r} × G_a²` (`A = Jac(y⁷ = x(1−x))`,
     `E = ℂ/B(1/7,2/7)ℤ[α]`), for every adapted `K ⊇ ℚ(ζ₇)`. It is sound when `LA` consists of eigen-coordinate
     triples of `Λ(A)`. Review: this file.
   - §3: add rows for `WuestholzBeta7` and `WuestholzX7` (Wüstholz 1989; derivations in §4 above).
   - Add `gmX7` to the list at l. 78–84: "out-of-range κ forces `V ⊇ T_ab`". (#18)
2. **`X7.lean`.**
   - At l. 117 and in the `thmX7` docstring, state explicitly: "the intended instance is
     `LA = {(z₁(v), z₂(v), z₃(v)) : v ∈ Λ(A)}`; for other `LA` the hypotheses `Thm11KappaX7 LA` and `WuestholzX7 LA` may
     be false" (#12).
   - Fix the indexing at l. 30 (#20).
   - Optionally, describe the isogeny of #7 at l. 20–21 (#21).
3. **`Waldschmidt.lean:12–13`.** Add `AbVar.Thm11KappaX7` to the instance list. (#19)
4. **Paper (optional).** In Cor. X7intro(b), say "up to the algebraic factors `sin(kπ/7)`". (#22)

## Falsification attempts (none succeeded)

* **An inconsistent period triple.** The three integrals were computed on one explicit closed loop, so the triple
  `(P₁, P₂, P₃)` belongs to one cycle (#1).
* **The wrong CM direction.** It was checked numerically (#2), and in any case it is irrelevant for soundness.
* **A non-algebraic `E`.** `g₂` and `g₃` are algebraic cubic irrationalities and `j = −3375` (#4).
* **A non-logarithm in `lam`.** Every generator is `[ζ^e]` (an automorphism) of a logarithm, `[α]` of an elliptic
  logarithm, a period, or a `G_a` constant. The only gap is the parameter `LA` (#12).
* **A connected subgroup in `ker Ψ″`.** Excluded for every `F`-basis `b` (§2).
* **A spurious κ.** `perX7 = ℚ ⊗ Ker exp` exactly. Out-of-range κ is trivial (#13).
* **The `d`-fields.** Lean's `d₂` overestimates the true value, which is harmless.

## Verdict lines

* Item 1 (period triple on one cycle, CM action, lattice `omega7·ℤ[α]`): **CORRECT**.
* Item 2 (`gmFX`/`gmX7`, `Thm11KappaX7`, uniform `sub`, `d₂`, count, multipliers, `zp`/`zq`): **CORRECT WITH NOTES**
  (sound for every adapted `b`; `LA` is an uninterpreted parameter, sound only for eigen-triples of `Λ(A)`; `TRUST.md`
  stale).
* Item 3 (`propX7_K`/`propX7`, `thmX7`, `x7c` vs Prop. X, Theorem X7, Cor. X7(c)): **CORRECT WITH NOTES** (faithful
  weakenings; torsion not formalised; `x7c` exact, and unconditional apart from W88 and `WuestholzBeta7`).
