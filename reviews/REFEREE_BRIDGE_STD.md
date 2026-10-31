# Referee report: `CM4E/Bridge/*.lean` (standard model `gmStd`, `HypStd`/`HypStdCM`, MG/SMG bridges)

Date: 2026-10-31. Scope: fidelity of `CM4E/Bridge/{Transport,Std,MG,SMG,Results}.lean` (commit 0bd32bd, plus working-tree
edits made during the review). No Lean file was edited. Scratch: `reviews/checks/bridgestd/`.

**Snapshot note.** `Std.lean`, `MG.lean`, `SMG.lean` and `Results.lean` were rewritten at 02:20:50 while this review ran.
The change added `HypStdCM` and `hypStdCM_of_hypStd` and switched the bridges from `HypStd` to `HypStdCM L.pp`. This report
covers the post-change files. The oleans (02:21) are newer than these sources, and the axiom audit below was run on them.

## Axiom audit

Command: `lake env lean reviews/checks/bridgestd/AxBridge.lean`, which imports `CM4E.Bridge.Results`; no rebuild was
needed. Every one of the following depends only on `[propext, Classical.choice, Quot.sound]`:
`hyperplaneKappa_transport`, `hypStdCM_of_hypStd`, `ker_E0`, `phiE`, `comap_phiT_torusLie`, `thm11KappaMG_of_std`,
`thm11KappaSMG_of_std`, `int_I`, `int_rho`, `fourExpAt_varpi_div_pi_all`, `fourExpAt_omegaRho_div_pi_all`, `mg1_varpi`,
`mg3_varpi`.

The check file also confirms the following by elaboration:
* `Gen.latI.pp = lemniscatic` (`rfl`);
* `latI.α = I` with `(p, q) = (−1, 0)`, and `latRho.α = ρ` with `(p, q) = (−1, −1)`;
* the Results statements have the same types as the `Final` statements, with `hW` replaced by `hS`.

`grep` finds no `sorry`, `native_decide` or `axiom` in `CM4E/Bridge/`.

## Item 1. `Transport.lean`: `hyperplaneKappa_transport`. Verdict: CORRECT

The hypotheses are the right ones, and each inclusion points the right way.
* `halg` (`G₁.alg → G₂.alg ∘ Φ`): this is needed so that a `G₁`-rational `W` maps to a `G₂`-rational `Φ W`. Direction
  correct.
* `hlam` (integer-multiple trick): each `yᵢ` is replaced by `Φ(Dᵢ yᵢ)` with `Dᵢ > 0`.
  - `span_ℚ{Dᵢ yᵢ} = span_ℚ{yᵢ}` is proved (`hspanD`, l. 47–59).
  - `Φ` is injective, so `dim_ℚ Y` is unchanged (`hfinY`).
  - `κ` is not claimed to be unchanged. What is proved is `κ₁ ≤ κ₂`: `Φ(Y ∩ per₁) ⊂ Y′ ∩ per₂` by `hper`, and `Φ` is
    injective. This is the direction needed, because the `G₂` premise has `−κ₂` on its right-hand side.
  - The rank and the `ℚ`-span really are unchanged, and `κ` can only grow, which only helps.
* `hd` (`G₂.d₁ + 2G₂.d₂ ≤ G₁.d₁ + 2G₁.d₂`): together with `κ₁ ≤ κ₂` and `d − 1 − t ≥ 0`, it gives that the `G₁` premise
  implies the `G₂` premise. Correct. In both uses the two sides are equal, `4r + 2r`.
* `hsub` (pull-back of nonzero `G₂.sub` members into `G₁.sub`): the conclusion for `G₂` gives `S ≤ Φ V`, so
  `Φ⁻¹S ≤ V`, and `Φ⁻¹S ≠ 0` because `Φ` is surjective. Direction correct.
* `Φ V` is a hyperplane, `Φ W ≤ Φ V`, and `Φ(Dᵢyᵢ) ∈ Φ V`. All are checked.

"Is the conclusion genuinely W88 for `G₁`?" `HyperplaneKappa G₁` is now *implied by* `HypStdCM`. Whether `gmMG` /
`gmSMG` are sound models is therefore no longer load-bearing for the results routed through the bridge: any unsound
`lam`, `per` or `sub` would either have blocked the proof or is harmless. This is the main gain of the bridge, and TRUST
§3 should say so (see issue 5).

## Item 2. `Std.lean`: `gmStd`, `HypStd`, `HypStdCM`. Verdict: CORRECT WITH NOTES (faithful and true modulo W88; the hand-off from `lean_lsg` is not yet automatic when `d₀ > 0`)

### Faithfulness of the model, field by field

* **`d₁ = d1`, `d₂ = m`, `G_a` in `d₀`.** For `G_a^{d₀} × G_m^{d₁} × ∏E_j` we have `Hom(G, G_a) = ℚ̄^{d₀}` and
  `Hom(G, G_m) = ℤ^{d₁}`, so `d₀` and `d₁` are maximal and `G₂ = ∏E_j` has dimension `m`. This matches the project's
  reading of (5.4) (REFEREE_HYP_M #1: weight 0 for `G_a`).
* **`alg`.** All coordinates algebraic. The coordinates `a`, `b` (with `exp = e^b`) and `z` (with `dz = dx/y`) are
  `ℚ̄`-rational, so this is the standard `ℚ̄`-structure. `Rational W` (∃ spanning set of algebraic vectors) is equivalent
  to `lean_lsg`'s `RationalOverQbarTan`.
* **`lam = Lam Ls`.** This is exactly `Λ(G)`: `a ∈ ℚ̄^{d₀}`, `e^{bᵢ} ∈ ℚ̄`, and `z_j ∈ Λ_j` or `℘_j(z_j) ∈ ℚ̄`. The last
  case also gives `℘′ ∈ ℚ̄` from the Weierstrass equation.
* **`per = span_ℚ(Per Ls)`.** This is `ℚ ⊗ Ker exp_G`. HyperplaneKappa's `κ = dim_ℚ(span_ℚ Y ∩ span_ℚ Per)` equals
  `rk_ℤ(Y_ℤ ∩ Per)`, because a `ℚ`-combination of elements of an additive group has an integer multiple in the group
  (`exists_nsmul_mem_closure`).
* **`sub = {H.tan : H : SubgroupData}`.** This is a complete list of the connected algebraic subgroups, for any curves
  (non-CM, isogenous, CM):
  - *Products.* For connected `G′ ⊂ L × A` (`L` linear, `A` abelian), Goursat gives an isomorphism
    `L′/N₁ ≅ B/N₂` between a quotient of a connected linear group and an abelian variety. It must be trivial (affine and
    complete), so `G′ = L′ × B`. The same argument, with unipotent against torus, splits `L′ = H₀ × T`.
  - *Factors.* `H₀` is a `ℚ̄`-subspace (`h0_rat`). Subtori are given by `ℚ`-subspaces `U`, with Lie algebra
    `U^⊥ ⊗ ℂ` (`torusLie`).
  - *Abelian part.* `IsAbelianTangent t` (`t ∩ ∏Λ_j` spans `t` over `ℝ`) holds iff `t/(t∩Λ)` is a compact complex
    subtorus of `ℂ^m/Λ`. Such subtori are exactly the abelian subvarieties. This includes graphs of isogenies and
    `ℤ[α]`-twisted diagonals, so it covers non-CM and isogenous factors.
  - Abelian subvarieties of `A_ℂ` with `A/ℚ̄` are defined over `ℚ̄`. In any case a larger `sub` only weakens the
    conclusion.
* **Count.** `d = d0 + d1 + m`, and `(d₁ + 2d₂ − κ)(d − 1 − t)` is literally (5.4).

**Is `HypStd` true?** Yes, as an instance of W88 Thm 1.1/(5.4), which is published and has no (NR). I also checked the
configurations outside the (NR) range of a hyperplane by hand. For `N = d − 1`, (NR) reads `κ ≤ d₁ + 2m − 2`, and `d₀`
drops out. Each out-of-range case is either trivially true or a classical theorem:
* `κ = d₁ + 2m`: `V ⊃ 0 × ℂ^{d₁} × ℂ^m`. When `d₁ = m = 0`, any `y ≠ 0` gives an algebraic `h₀` line.
* `κ = d₁ + 2m − 1` with `d₁ ≥ 2`: `V` contains a rational toric line.
* `κ = d₁ + 2m − 1` with `m ≥ 2`: a `ℚ`-subspace of `Λ_ℚ` of rank `2m − 1 > 2(m − 1)` spans all of `ℂ^m`. A complex
  subspace of dimension `j` meets `Λ` in rank at most `2j`.
* `(d₁, m) = (0, 1)`: the period line `0 × ℂ` is the tangent of `E`.
* `(d₁, m) = (1, 1)`: either a toric line, or `t_E`, or the whole `T_m × E` lies in `V`.
* `(d₁, m) = (1, 0)`, `d₀ ≥ 1`, `κ = 0` (that is, `G = G_a^{d₀} × G_m`): a genuine Gel'fond–Schneider–Lang statement,
  true by W88 Thm 1.1 (sanity check: `d₀ = 1`, `W = 0` is Gel'fond–Schneider).

No configuration makes `HypStd` false.

### Is `HypStd` exactly what `lean_lsg` Thm 4.1 yields via §5d?

* **For `d₀ = 0`: yes in shape.** `gmStd 0 d₁ (fun _ : Fin 1 => L)` is `gmE L d₁` up to coordinates: `torusLie U` versus
  `span ℒ`, and `t ∈ {0, ℂ}`. This is the target of `thm11Kappa_of_theorem41`. The §5d induction applies Thm 4.1 to the
  `a/e`-maximal `G′ = T′ × B′`; `lean_lsg` handles a `B′` that is not a product by `LSG/CM/Transport.lean:thm41Sub`
  (proved). The (NR) corners of `G′` (`κ′ ≥ d₁′ + 2d₂′ − 1`) are all trivial when `d₀ = 0`:
  - `d₁′ ≥ 2`: a toric line;
  - `dim B′ ≥ 2`: `t_{B′} ⊂ V`;
  - `(1, 0)`: `V′ = 0`;
  - `(0, 1)`: a period line;
  - `(1, 1)`: a toric line, or `t_{B′}`, or `V′ = T_{G′}`, which is impossible.

  This is the same case split as the `m = 1` file.
* **For `d₀ > 0`: no, not from `Theorem41Abelian` alone.** The §5d induction (and the top level itself, for
  `G = G_a^{d₀} × G_m`) can need Thm 4.1 for a *linear* `G′ = H₀ × T′` with `dim T′ ≤ 1` and `κ′ = 0`. There (NR) fails
  identically: `2 dim V′ = 2k < 1 + 2k`. `lean_lsg` is addressing exactly this in `LSG/W88/K5dRoy.lean`: Thm 4.1 for
  `G_a^{k₀} × G_m^{k₁}` without (NR), from Roy 1992 via StrongSix. At review time that file still had a `sorry` (l. 419).
  The corners with an abelian factor and `d₀ > 0` are trivial by the same case split.

## Item 3. `MG.lean`, `SMG.lean`, `Results.lean`. Verdict: CORRECT WITH NOTES

**`MG.lean`.**
* `E0 z = (z_{j0} + α z_{j1})_j` is surjective.
* `Wpsi ≤ ker E0`: each `E0 v j ∈ k` and `b` is `k`-independent (`b_kindep`). Combined with `dim Wpsi ≥ r`, this gives
  `ker E0 = Wpsi`. So `phiE : Qm ≃ ℂ^r` is legitimate, and `lamM = Σ b_j (phiE q)_j`.
* `phiT` is a reindexing `ℂ^ι × ℂ^ι ≅ ℂ^{card(ι⊕ι)}`. `comap_phiT_torusLie` identifies pulled-back torus Lie algebras
  with `torSub` of the annihilator.
* The counts agree: `4r + 2r = 2·2r + 2·dim Qm`.
* The subgroup condition is now a *theorem*. A nonzero abelian tangent contains a nonzero lattice vector, and on it
  `λ = ω Σ b_j(m_j + n_jα) ≠ 0` by `k`-independence.

**`SMG.lean`.** The same, with `G_a²` placed in `d₀ = 2` (consistent with REFEREE_HYP_M / SMG), and the uniform
"algebraic vector with `Ψ″ ≠ 0`" condition proved.

**Source hypotheses.** `thm11KappaMG_of_std` and `thm11KappaSMG_of_std` conclude the very constants `Gen.Thm11KappaMG L`
and `Gen.Thm11KappaSMG L` that `Final.fourExpAt_*_div_pi_all`, `Final.mg1_varpi` and `Final.mg3_varpi` take as `hW`.
The Results proofs are one-line applications of the `Final` theorems, so `HypStdCM` really replaces those `hW` there.

**`int_I`, `int_rho`.** `i² = −1 + 0·i` and `ρ² = −1 − ρ`, which is correct. The premise is the right one: `[α]` must be
an endomorphism of `E`, so that `L` is `ℤ[α]`-stable and `αω e_p`, `α²ω` lie in `L` (`E0_single_mem`). It is discharged
for both lattices used.

**Paper match.**
* **Theorem 1(b).** `FourExpAt (cΩ/π)` for every `c ∈ ℚ̄ˣ`, for `Ω = ϖ` and `Ω = Ω_ρ`. Every period of `E_i`, `E_ρ` is
  a `ℚ̄ˣ`-multiple of these, so the two curves are fully covered. Other CM curves are not (already noted in TRUST §5).
  `Ω_ρ` keeps `hg₂′`, `hg₃′`, as in `Final`.
* **Cor. MG1.** `Bridge.mg1_varpi` is the case `a = b = c = 1` on `E_i`, that is, the intro Corollary (paper l. 99).
  The main-text Cor. MG1 (l. 451) asserts it for all `a, b, c ∈ ℚ̄ˣ` and every CM curve; see issue 4.
* **Cor. MG3.** Matches paper l. 472 for `Ω = ϖ`:
  - `x` plays the role of a determination of `log α`;
  - `ℚ`-independence of `2πi, π², x` is the paper's hypothesis;
  - "transcendental" is the same as `∉ ℚ̄`, since `α^{Ω/π} ≠ 0`;
  - Baker is a named input, as in `Final`; the paper's "hence `K`-independent" is Baker.

## Issues

| # | severity | file:line | issue | fix |
|---|---|---|---|---|
| 1 | MEDIUM (documentation) | `Std.lean:42–43` (`HypStdCM` docstring) | The docstring says `lean_lsg` "proves it unconditionally for CM lattices with algebraic invariants". That is false today: `lean_lsg` has no such theorem, the §5d deduction exists only for `G_m^{d₁} × E`, and `K5dRoy.lean:419` has a `sorry`. It also contradicts `Results.lean:12` ("to be supplied") and TRUST l. 24 ("in progress"). | Say "to be supplied by `lean_lsg`". Upgrade the wording only once a `lean_lsg` theorem discharges it by `exact`. |
| 2 | MEDIUM (dependency / plan) | `Std.lean:38–45`; TRUST l. 24 | For `d₀ > 0`, `HypStdCM` cannot be derived from `Theorem41Abelian` under (NR) alone. The §5d induction can reach a linear `G′ = H₀ × T′` (`dim T′ ≤ 1`, `κ′ = 0`), and at the top level `G = G_a^{d₀} × G_m`; there (NR) fails identically. This needs the (NR)-free linear Thm 4.1, which is Roy 1992, via `lean_lsg/LSG/W88/K5dRoy.lean` (in progress). Not a falsity: W88 asserts it, and so does Roy (proved in StrongSix). | In TRUST, write "Thm 4.1 under (NR) is proved; for `d₀ > 0` the deduction also needs Roy's (NR)-free linear case (K5dRoy, in progress)". **Split `HypStdCM` into a `d₀ = 0` part and a `d₀ = 2` part.** Theorem 1(b) uses only `hS 0 _ r` (MG.lean:200), so it depends only on the `d₀ = 0` part. That is the semiabelian regime where every (NR) corner is trivial (item 2) and only the §5d bookkeeping for `m ≥ 2` remains in `lean_lsg`. MG1 and MG3 use `hS 2 _ r` (SMG.lean:61). |
| 3 | LOW | TRUST l. 24 | The row lists "Theorem MG, Theorem SMG" as conditional only on `HypStdCM`, but `Bridge/` states no such theorems. They follow only by composing the `Gen` theorems with `thm11Kappa*_of_std`, and only for lattices with integral `α` (`latI`, `latRho`). | Either add `Bridge.thmMG_*` / `thmSMG_*` wrappers, or say "via `thm11KappaMG_of_std` (for `latI`, `latRho`)". |
| 4 | LOW / NOTE | `Results.lean:43–47` | `mg1_varpi` is only `a = b = c = 1` on `E_i`, which is weaker than the main-text Cor. MG1 (all `a, b, c ∈ ℚ̄ˣ`). `Gen.mg1` already takes general `a, b, c` (Final.lean:188–190 instantiates `1 1 1`). | Export the general-`a, b, c` version through the bridge, or label the theorem as the intro corollary. |
| 5 | NOTE | TRUST §3 rows `Gen.Thm11KappaMG`, `Gen.Thm11KappaSMG` | For `L = latI, latRho`, soundness of the hand-written models `gmMG` / `gmSMG` is no longer load-bearing: the proved bridge derives their hypotheses from `HypStdCM`. The trust base for these results shrinks to `gmStd`, which is reviewed here and is a much simpler model. | Add this sentence to TRUST §3. |
| 6 | NOTE | `Std.lean` | `HypStd`/`HypStdCM` live in `lean_mstar`, and `lean_lsg` does not depend on `lean_mstar`. | When `lean_lsg` delivers, keep a verbatim copy (as `MStarCopy.lean` does for `Thm11Kappa`), and check the hand-off by `exact` in `Axioms.lean`. `HyperplaneKappa` itself must also be copied verbatim. |
| 7 | NOTE | `Std.lean:38–40` | `HypStd` quantifies over all `(d₀, d₁, m)` and all curves, which is far more than the bridges use (`d₀ ∈ {0, 2}`, `d₁ = 4r`, one curve). This is harmless (it is true), but every extra case is something `lean_lsg` must deliver, including the `G_a^{d₀} × G_m` corner of issue 2. | Optional: narrow it to what is used (compare issue 2). |

No issue makes `HypStd`/`HypStdCM` false, and no issue breaks the logical chain `HypStdCM ⇒ Thm11KappaMG/SMG ⇒` Results.

## Verdicts

* Item 1 (`Transport.lean`, `hyperplaneKappa_transport`): **CORRECT**
* Item 2 (`Std.lean`, `gmStd` / `HypStd` / `HypStdCM`): **CORRECT WITH NOTES**. It is a faithful and true W88 §5d
  statement with a complete subgroup list. Fix the overclaiming docstring (issue 1). Delivery from `lean_lsg` for
  `d₀ > 0` needs the (NR)-free linear case (issue 2).
* Item 3 (`MG.lean`, `SMG.lean`, `Results.lean`): **CORRECT WITH NOTES**. The hypotheses are the same constants used in
  `Final.lean`, `int_I` / `int_rho` are correct, and the statements match the paper for `Ω = ϖ`, `Ω_ρ`. MG1 is the
  `a = b = c = 1` case only (issue 4).
* Axiom audit: **PASS** (standard axioms only, for all 13 Bridge declarations checked).
