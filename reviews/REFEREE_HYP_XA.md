# Referee report: the generic Theorem X (`gmXA`, `Thm11KappaXA`, `propX15`, `thmXA`, (Ch), `thmX7_of_gen`)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope.**
* In full: `CM4E/AbVar/XGen.lean`, `CM4E/AbVar/XThm.lean`, `CM4E/AbVar/Ch.lean`, `CM4E/AbVar/X7Gen.lean`.
* For context: `CM4E/AbVar/FrameX.lean` (`gmFX`, `frameX_false`), `CM4E/AbVar/X7.lean` (`gmX7`, `thmX7`,
  `WuestholzX7`), `CM4E/AbVar/Basis.lean`, `CM4E/Waldschmidt.lean` (`GroupModel`, `HyperplaneKappa`), `TRUST.md`
  (the rows for Theorem X).
* Paper: draft [II]:
  - §`sec:setting` (l. 309–414: (S1), (P), (Ch), (W), Lemma K′);
  - §`sec:X` (l. 589–725: set-up, Prop. `prop:X`, Theorem X, Lemmas S′ and L′, the proof of Theorem X).
* Baseline: `reviews/REFEREE_HYP_X7.md`, whose findings on `gmFX`, the level-seven data and the count are not repeated
  here.

**Process.** No project file other than this report and `reviews/checks/hypxa/` was edited, and no git command was run.
The scratch files are:
* `reviews/checks/hypxa/AxXA.lean` and `AxXA.out`. These hold the axiom audit, plus a referee lemma
  `distinct_of_wuestholz` (finding #8), proved sorry-free.

The oleans of all four files are newer than their sources. `lake env lean` on the scratch file took about 40 s.

## Verdicts

* **Item 1 (model soundness, `gmXA` / `Thm11KappaXA`): CORRECT WITH NOTES.**
  - For four pairwise distinct first-kind slots of simple CM abelian varieties with faithful records, `HyperplaneKappa
    (gmXA S b)` is a true instance of W88 §5d for every adapted `b`. Here a faithful record means: `κ_s = σ_s(α)` with
    `α` a primitive element of `F`, `P` the eigen-vector of one cycle, and `LA ⊆` eigen-vectors of `Λ(A)`.
  - All six parts check out: the group, the generators, the periods, the `ℚ̄`-structure, `d₁`/`d₂`, and the uniform
    subgroup condition.
  - Distinctness is necessary. With two equal slots, an explicit nonzero abelian subvariety lies in `ker Ψ″` (#7).
  - `Thm11KappaXA` does not carry distinctness, and `XSetup.Distinct` only sees slots on the same `AV` index. However:
    - the non-distinct cases are exactly those in which `WuestholzXA` is false (for faithful records);
    - `Distinct` is a Lean consequence of `WuestholzXA X.slot` (#8).

    So the combined hypotheses of `propX15`/`thmXA` are never satisfiable with an unsound `hW`.
  - The `Thm11KappaXA` docstring should say all of this explicitly (#10).
* **Item 2 (faithfulness of `propX15`, `thmXA`): CORRECT WITH NOTES.**
  - `propX15` is Proposition 15 verbatim, under the extra hypothesis `5 ≤ [K : ℚ]`. That hypothesis is a frame artifact
    and never restrictive: four pairwise distinct first-kind slots force `[K : ℚ] ≥ 6` (#13).
  - `hκK` (type conjugates in `K`) is equivalent to the paper's "K contains the Galois closures" (#12).
  - `thmXA` is Theorem X's first conclusion, exactly.
  - The torsion sentence of Theorem X is not formalised. This is acceptable, because Lean has no `exp_{A_j}`, but it is
    not flagged in the docstrings, and `TRUST.md` is stale (#15).
* **Item 3 ((Ch)): CORRECT.**
  - `ch_span` is the paper's (Ch), written in the power basis of `F`.
  - It is used exactly where the paper uses it: in `propX15_sup`, via `exists_coord_log` with `ℓ = γ`, giving
    `w, w′ ∈ Ψ(Ω_K(G))`; and in `thmXA`, to build one point of `Λ_K(G)` carrying all the data.
* **Item 4 (instance `thmX7_of_gen`): CORRECT.**
  - The conclusion is character-for-character that of `thmX7`.
  - `X7S` is faithful: `κ_s = ζ^{s+1}`; `E` with `κ = α7` and period `Ω`; slots `a, b, c, d = z₁, z₂, z₃, E`; (R) is
    `relation_R` with `μ = mu7'`.
  - The hypotheses differ from those of `thmX7`, and both sets are true (#17).
* **Item 5 (axioms): CORRECT.** All four requested declarations, and `propXA_K`, `propX15_sub`, `propX15_sup`, use only
  `propext`, `Classical.choice` and `Quot.sound`. The four files contain no `sorry`, `axiom`, `admit` or
  `native_decide`.

**No FATAL or MAJOR issue was found.**

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | 1, group | `∏_j A_j^{r_j} × G_a²` (one block per slot, even when slots share a variety) is a commutative algebraic group over `ℚ̄`. Lean's group and the paper's `G″ = G^n/U` are isogenous: Lemma K′ gives `A^n/B_ker ~ A^{Σ_{j∈Σ_A} r_j}` for each class `A`, as in `REFEREE_HYP_X7` #7. Lean applies W88 to its own group, so no lift is needed |
| 2 | OK | 1, generators | `genA S j i e v = [α^e]v` in copy `i` of block `j`, for all `e ∈ ℕ`. If `α ∉ 𝒪_F`, then `[α^e]v ∈ ℚ ⊗ Λ(A) = Λ(A)`, because division points of algebraic points are algebraic. `lam` is a `ℚ`-span, so this is harmless. `P ∈ LA ∪ {P}` is the log of `0`. The `G_a` generators `(0, c₁, c₂)` with `c_i ∈ ℚ̄` are logs |
| 3 | OK | 1, periods | `[α^e]γ ∈ F·γ ⊂ ℚ ⊗ Ω(A)`, because `H₁(A, ℚ)` is an `F`-module. So `per ⊂ ℚ ⊗ Ker exp`, and `κ_Lean ≤ κ_W88`, which only strengthens the premise |
| 4 | OK | 1, `ℚ̄`-structure | `algQA` (all eigen-coordinates algebraic) is right: the `z_σ` are dual to eigen-differentials defined over `ℚ̄`. The `G_a` coordinates are standard |
| 5 | OK | 1, `d₁`, `d₂` | The truth is `d₀ = 2`, `d₁ = 0`, `d₂ = Σ r_j g_j` (`= 2n` when `2g_j = d_j`). Lean's `d₂ = Σ r_j g_j + 2` overestimates, which only weakens the hypothesis, because `d − 1 − t ≥ 0`. The cost is the count `3n > 2n + 4`, that is `n ≥ 5` (`hcount`) |
| 6 | OK | 1, uniform `sub` | For pairwise distinct slots, no nonzero connected `H` has `T_H ⊂ ker Ψ″`, for every adapted `b`. Proof in §1 |
| 7 | NOTE | 1, distinctness necessary | If `S 0 = S 3` (or two slots on one record with the same `s`), the subvariety `B_S`, `S = {(m, m′) : ψ₀(m) + ψ₃(m′) = 0}` (F-dimension `r ≥ 1`), has `T(B_S) ⊂ ker Ψ″`. So `gmXA` is not a sound model there (§1, counterexample). The same holds for slots on isogenous records with corresponding embeddings. In every such case `P_j/P_{j′} ∈ ℚ̄^×`, so `WuestholzXA S` is false |
| 8 | NOTE | 1, `Distinct` | `XSetup.Distinct` checks only slots with the same `cls`. That different `AV i` are non-isogenous is a convention, not checked. But `Distinct` follows from `WuestholzXA X.slot`. The referee lemma `distinct_of_wuestholz` (`reviews/checks/hypxa/AxXA.lean`, standard axioms) proves it. So `hD` is redundant in `propX15`, `propX15_sup` and `thmXA`. Harmless |
| 9 | TRUST NOTE | 1, records | `CMAV` is uninterpreted data `(g, κ, P, LA)`. `Thm11KappaXA`, `WuestholzXA` and `WuestholzSplitXA` are sound only for faithful records (`κ_s = σ_s(α)` acting on `z_s`, `α` primitive, `P = (z_s(γ))_s`, `LA ⊆ {(z_s(v))_s : v ∈ Λ(A)}`). Primitivity is genuinely needed: if `ℚ(α) ⊊ F`, then `b_j` is only `ℚ(κ_{s_j})`-independent and the uniform condition can fail. For a faithful record, `CMAV.Good.cm` (`2g ≤ deg κ_s`) forces primitivity. `Thm11KappaXA` does not assume `Good` |
| 10 | MINOR (docs) | 1, `Thm11KappaXA` docstring (`XGen.lean:114–116`) | It says "pairwise distinct first-kind slots of simple CM abelian varieties" and "LA … logarithms". It omits three things: what "distinct" means for records (#7, #8), the faithfulness of `κ` and `P` (#9), and that the hypothesis may be unsound for non-distinct slots, where `WuestholzXA` is false anyway. The module docstring (l. 26–33) covers the convention, but not the last point |
| 11 | OK | 1, Lemma U range | The out-of-range argument of `REFEREE_HYP_X7` #13 carries over. With `D = Σ r_j g_j`, `κ ≥ 2D − 1` forces `V ⊇ T_ab`, and `T_ab` contains the algebraic vector `eA S 0 i s₀` with `Ψ″ = (b₀ᵢ, 0) ≠ 0` (`r₀ ≥ 1` by `one_mem`; `b₀ᵢ ≠ 0` by independence) |
| 12 | OK | 2, `propX15` | `lamK` is the `K`-span of `Λ(A)` when `LA = Λ(A)` (the `α^e` are then redundant). The `G_a` part is `ℚ̄ = K·ℚ̄`, `V = ℂw`, and `Kw + Kw′` with `w = (P_a, βP_c)`, `w′ = (P_d, βP_b/μ)`. (R) enters as `hR`. `hκK` asks only for the type conjugates. Since `σ(F)` is stable under complex conjugation and `Φ ⊔ Φ̄ = Hom(F, ℂ)`, this is the paper's "K ⊇ Galois closures" |
| 13 | NOTE (docs) | 2, `hK5` | `5 ≤ [K : ℚ]` is a frame artifact, and the docstring explains it correctly. It is never restrictive: with `[K : ℚ] ≤ 4` at most two pairwise distinct first-kind slots have `σ_j(F_j) ⊂ K` (§2). Prop. 15 for small `K` does not follow formally from large `K`, so the hypothesis is a real (if empty) restriction of the Lean statement. Suggest saying so in the docstring |
| 14 | OK | 2, `thmXA` | Hypotheses: `z_j(v_j) = Σ_k c_{jk} z_j(v_{jk})` with `c ∈ ℚ̄` and `v_{jk} ∈ LA ∪ {γ}` (that is, `v_j ∈ ℚ̄Λ(A_j)`); `q_i ∈ ℚ̄`; `μ, β ∈ ℚ̄^×`; (R); (eq:X). Conclusion: `q₁ = q₂ = 0` and `z_j(v_j) ∈ ℚ̄P_j`, with the right constants (`x`, `yβ/μ`, `xβ`, `y`). `thmXA` chooses `K` itself, as the paper does |
| 15 | MINOR (scope/docs) | 2, torsion; `TRUST.md:205` | Theorem X's sentence "if `v_j ∈ Λ(A_j)` then `exp(v_j)` is torsion" is omitted. Acceptable: it needs `exp_{A_j}`, or a named input like `TorsionX7` (`X7Torsion.lean`). But neither the module docstring nor the `thmXA` docstring says so. `TRUST.md` l. 205 still says "Theorem X (general …), Prop. 15 in general: ✗ only the level-seven instance" |
| 16 | OK | 3, (Ch) | `ch_span`: `(κ_s^e)_s`, `e < d`, span `K^g` over `K`. This is (Ch), because `{α^e}` is a `ℚ`-basis of `F` and `(σ_s(α^e))_s = (κ_s^e)_s`. `exists_coord_log` is the consequence "slot coordinates can be prescribed independently". Used in `propX15_sup` (with `ℓ = γ`) and in `thmXA` (with `ℓ = v_{jk}`) |
| 17 | OK | 4, instance | Same conclusion as `thmX7`. Hypotheses: `Thm11KappaXA (X7S LA).slot` replaces `Thm11KappaX7 LA` (blocks `A^{n/6}` ×3 and `E^{n/2}`, as before). `WuestholzSplitXA (X7S LA).slot` replaces `WuestholzX7 LA`; it is formally stronger (`ℚ̄`-combinations, not single logs), and it is true by the same Wüstholz argument. `WuestholzBeta7` is unchanged. `LA` is the same trust note as `REFEREE_HYP_X7` #12 |
| 18 | OK | 5, axioms | see `AxXA.out` |
| 19 | OK | named inputs | `WuestholzXA` and `WuestholzSplitXA` are true for distinct slots with faithful records (§3) |
| 20 | COSMETIC | `Waldschmidt.lean:12–14` | the instance list omits `AbVar.Thm11KappaXA` |

## Details

### 1. Soundness of `gmXA` [Proved, modulo (S1), (P), standard CM theory]

**Uniform condition (#6).** Let `H ≠ 0` be a connected algebraic subgroup of `∏_j A_j^{r_j} × G_a²`.
* By (P), `H = L × B` with `L ⊂ G_a²` and `B` an abelian subvariety. `Ψ″` is the identity on `G_a²`, so `T_H ⊂ ker Ψ″`
  forces `L = 0` and `T_B ⊂ ker μ₁ ∩ ker μ₂`.
* Group the blocks by isogeny class (by (S1), `Hom = 0` between non-isogenous simple varieties). Then `B = ∏_A B_{S_A}`
  with `S_A ⊂ F_A^{R_A}`, where `R_A = Σ_{j ∈ Σ_A} r_j`.
* In eigen-coordinates, `T(B_S) = ⊕_{σ∈Φ} σ(S) ⊗ ℂ`. It is a sum of its `σ`-parts, and each part has dimension
  `dim_F S` in every `σ`-coordinate.
* Each target coordinate is a sum of two slot forms. They lie either on non-isogenous classes (product
  decomposition), or on one class at distinct embeddings (distinct slots). In both cases the two forms see independent
  summands of `T_B`, so each slot form vanishes on `T_B` separately.
* Slot form `j` vanishes on `T_B` iff `Σ_i b_{j,i} σ_{s_j}(m_i) = 0` for every `m ∈ S` (block-`j` part). The columns
  of `M` span `S` over `F`, and `ψ` is `σ`-semilinear.
* `IsAdaptedBasisD (κ_{s_j}) d_j (b j)` says that `κ^e b_{j,i}` (`e < d_j`) are `ℚ`-independent, that is, `b_j` is
  `ℚ(κ_{s_j}) = σ_{s_j}(F_j)`-independent (this uses `α` primitive). So the block-`j` part of `S` is `0`.
* Every block carries its own slot, so `S = 0` and `B = 0`. This contradicts `H ≠ 0`.
* `T_H` is `ℚ̄`-rational and `⊄ ker Ψ″`, so it contains an `algX` vector with `Ψ″ ≠ 0`. That is `gmFX`'s `sub`.

Unused eigen-coordinates of a block cannot hide a subvariety: a nonzero block part of `S` is nonzero in every
`σ`-coordinate, in particular in `σ_{s_j}`. The argument uses only `IsAdaptedBasisD` per slot. The common-`K` condition
`IsAdaptedX.span` plays no role in soundness, so `Thm11KappaXA` is sound for every quantified `b`.

**Counterexample without distinctness (#7).** Let `S 0 = S 3 = (A, s)`.
* Then `b₀`, `b₃` are both `σ_s(F)`-bases of the same `K`, with `r₀ = r₃ = r`.
* `ψ_j(m) = Σ_i b_{j,i} σ_s(m_i)` is a `σ_s`-semilinear bijection `F^r → K`.
* So `S = {(m, m′) ∈ F^r × F^r : ψ₀(m) + ψ₃(m′) = 0}`, placed in blocks 0 and 3 with zero in blocks 1 and 2, is the
  graph of `−ψ₀^{-1}ψ₃`. It has `F`-dimension `r ≥ 1`.
* On `T(B_S)`: `μ₁ = ψ₀(M)u_σ + ψ₃(M′)u_σ = 0`, and `μ₂ = 0`. So `0 ≠ T(B_S) ⊂ ker Ψ″`, and `sub` misses it.

The same construction works for two slots on isogenous records whose embeddings correspond under the isogeny. The
eigen-coordinates differ only by a `ℚ̄^×` factor `c`; put `c` into `ψ₃`, which works whenever `cK ∩ K ≠ 0`, for
instance when `c ∈ K`. In all these cases `P_j/P_{j′} ∈ ℚ̄^×`, so `WuestholzXA` fails. Hence `hW ∧ hWB` is never
satisfiable with an unsound `hW`. For records on the same index, `distinct_of_wuestholz` even derives this in Lean.

**`Distinct` vs "pairwise distinct" (#8).** In the paper, two slots are equal iff the varieties are isogenous and the
embeddings correspond. `Distinct` encodes this for slots with the same `cls`, under the convention (docstrings of
`XGen` and `XThm`) that distinct indices `AV i` are non-isogenous. Without the convention, `Distinct` is weaker than
paper-distinctness, but `WuestholzXA` makes up the difference, as above. The referee lemma is:
```lean
theorem distinct_of_wuestholz (X : XSetup) (hWB : WuestholzXA X.slot) : X.Distinct
```
It is proved in `reviews/checks/hypxa/AxXA.lean` with the axioms `propext`, `Classical.choice`, `Quot.sound`.

### 2. `[K : ℚ] ≤ 4` admits at most two distinct slots (#13)

Each slot `j` gives a CM subfield `L_j = σ_j(F_j) ⊂ K` of degree `2g_j`, so `[K : ℚ]` is even.
* **`[K : ℚ] = 2`.** `K` is imaginary quadratic. All elliptic curves with CM by `K` are isogenous, so there is one slot.
* **`[K : ℚ] = 4`, `L_j` imaginary quadratic.** There is one slot per imaginary quadratic subfield, and there are at most
  two such subfields. If `K` contains one, `K` is biquadratic, and its quartic CM types are all induced, so no simple
  surface occurs.
* **`[K : ℚ] = 4`, `L_j = K`, cyclic `K`.** All four types lie in one `Aut(K)`-orbit. That gives one class, with two
  slots.
* **`[K : ℚ] = 4`, `L_j = K`, non-Galois `K`.** There are two classes. Exactly one of `{id, c}` lies in each type, so
  each class has exactly one slot with image `K`. That makes two slots.

Four pairwise distinct slots therefore force `[K : ℚ] ≥ 6`. The X7 instance has `[K : ℚ] ≥ 6`. `thmXA` adjoins `ζ₇`
for the same reason, which is harmless.

### 3. The named inputs [Proved modulo Wüstholz 1989]

* **`WuestholzXA`.** This is (W) for four distinct first-kind slots. Take the point `(1, γ_A, …)` on
  `G_a × ∏_A A`. Its smallest algebraic subgroup is `G_a × ∏_A A`, since each `A` is simple and the subgroup is a
  product by (P). A `ℚ̄`-form `a₀t + Σ a_j z_j` vanishes on that tangent space only if every coefficient is zero: the
  `z_j` are distinct eigen-coordinates or lie on distinct factors.
* **`WuestholzSplitXA`.** This is the paper's slot-splitting paragraph, with `ξ = (1, (u_i), γ's)` on
  `G_a × ∏_A A^m`. `L = G_a` gives `q = 0`. By (S1), the two slot forms see independent `u_σ`, so each vanishes at `ξ`.
  The `ℚ̄`-combinations in `zQbar` change nothing. Both inputs need faithful records (#9).

### 4. Fidelity of the instance

* `A7`: `g = 3`, `κ_s = ζ^{s+1}` (type `{1, 2, 3}`), `P = perT = (perA 1, perA 2, perA 3)`, `LA` a parameter.
* `E7AV`: `g = 1`, `κ = alpha7 = ζ + ζ² + ζ⁴ = (−1 + √−7)/2`, `P = Ω = omega7` (lattice `Ωℤ[α]`, so `[α]` acts by
  `α`), `LA = {w | LogE E7 (w 0)}`. The last is faithful by definition.
* `cls = ![0, 0, 0, 1]` and `sl = 0, 1, 2, 0`, so `per = perA 1, perA 2, perA 3, omega7` (`X7S_per`).
* (R) is `relation_R`: `perA 1 · perA 2 = mu7' · perA 3 · omega7`.
* (eq:X) specialises to `(v₁ 0 + u + q₁)·β perA 3 = (v₃ 2 + v₂ 1 + q₂)·perA 1`, which is `thmX7`'s `hrel`.
* `X7S_good` and `X7S_distinct` are proved.

## Recommended fixes

1. **`XGen.lean:114–116` (`Thm11KappaXA` docstring; #9, #10).** State that it is sound when:
   - each record is faithful: `κ_s = σ_s(α)` for a primitive `α` of the CM field, acting on the `ℚ̄`-rational
     eigen-coordinate `z_s`; `P = (z_s(γ))_s` for one cycle; `LA ⊆` eigen-vectors of logarithms of algebraic points;
   - the varieties are simple of primitive type;
   - the four slots are pairwise distinct in the paper's sense. Records that are equal or isogenous must have different
     `s`, or non-corresponding embeddings.

   Add: "For non-distinct slots the model is unsound (an abelian subvariety lies in `ker Ψ″`), but then `WuestholzXA S`
   is false, so no theorem using both is affected."
2. **`XThm.lean` (`propX15`, `thmXA`; #8).** Optional: drop `hD`, deriving it from `hWB` with the two-line
   `distinct_of_wuestholz` above. Otherwise, note in the `Distinct` docstring that it follows from `WuestholzXA`.
3. **`XThm.lean` module docstring (#13).** After "the paper's count has no such condition", add: "the condition is
   never restrictive: four pairwise distinct first-kind slots force `[K : ℚ] ≥ 6`."
4. **`XThm.lean` (`thmXA` docstring and module docstring; #15).** Add: "The torsion sentence of Theorem X is not
   formalised (for level seven it is `thmX7_torsion` with the named input `TorsionX7`)."
5. **`TRUST.md` (#15).**
   - l. 205: Theorem X and Prop. 15 in general → ◐: `AbVar.XSetup.propX15` (with `[K:ℚ] ≥ 5`) and `AbVar.XSetup.thmXA`
     (no torsion), relation (R) a hypothesis.
   - §3: add rows for `AbVar.Thm11KappaXA` (soundness conditions as in fix 1; review: this file), `AbVar.WuestholzXA`
     and `AbVar.WuestholzSplitXA`.
6. **`Waldschmidt.lean:12–14` (#20).** Add `AbVar.Thm11KappaXA` to the instance list.

## Falsification attempts

* **Two slots on one variety, mixing blocks.** Slots on one `A` give blocks of the same `A`, and `B_S` may mix them.
  Each block is still detected by its own slot, at its own `σ`. Survives.
* **Two slots feeding one target coordinate on one variety.** Distinct `σ` give independent summands of `T(B_S)`.
  Survives.
* **Isogenous but different records, non-corresponding embeddings.** These are distinct `σ` after transport. Survives.
* **Identical or corresponding slots.** The model fails (#7), but `WuestholzXA` fails too. Harmless.
* **Non-primitive `α`.** The model can fail. This is excluded by the `CMAV` docstring, and by `Good.cm` for faithful
  records (#9).
* **Graphs into `G_a²`.** `Hom(B, G_a) = 0`. Survives.
* **Out-of-range `κ`.** It forces `V ⊇ T_ab ∈ sub` (#11). Survives.
* **Small `K`.** The `[K : ℚ] ≥ 5` restriction is empty in the intended setting (#13).

## Verdict lines

* Item 1 (`gmXA`, `Thm11KappaXA`, uniform condition, distinctness): **CORRECT WITH NOTES** (sound for distinct slots
  with faithful records; distinctness is necessary, is not carried by `Thm11KappaXA`, and is enforced by `WuestholzXA`;
  the docstring needs to say so).
* Item 2 (`propX15`, `thmXA` vs Prop. 15, Theorem X): **CORRECT WITH NOTES** (faithful; `[K:ℚ] ≥ 5` is a harmless
  artifact; torsion clause omitted and not flagged; `TRUST.md` stale).
* Item 3 ((Ch)): **CORRECT**.
* Item 4 (`thmX7_of_gen`, `X7S`): **CORRECT**.
* Item 5 (axioms): **CORRECT** (standard three only).
