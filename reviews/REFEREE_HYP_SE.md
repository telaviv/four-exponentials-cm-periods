# Referee report: Theorem SE(1) (`gmFX1`, `gmES`/`gmSE`, `Thm11KappaSE`, `thmSE`, the SE bridge, the `ϖ`/`Ω_ρ` wrappers)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope.**
* In full:
  - `CM4E/AbVar/FrameX1.lean`: `gmFX1`, `frameX1_false`;
  - `CM4E/AbVar/SE.lean`: `LtildeE`, `LtildeEE`, `gmES`, `gmSE`, `Thm11KappaSE`, `thmSE`;
  - `CM4E/Bridge/SE.lean`: `hyperplaneKappa_gmES`, `uniform_SE`, `thm11KappaSE_of_nonIsog`,
    `transcendental_div_of_nonIsog`, `thmSE_of_nonIsog`, `thmSE_varpi_omegaRho`;
  - the two new wrappers in `CM4E/Unconditional.lean` (l. 288–303).
* For context:
  - `CM4E/Waldschmidt.lean` (`GroupModel`, `HyperplaneKappa`);
  - `CM4E/AbVar/FrameX.lean` (`gmFX`);
  - `CM4E/Bridge/{Transport,Std}.lean`;
  - `CM4E/Bridge/ELog.lean` (`CMMulLogE`), `CM4E/Gen/ThmM.lean` (`LogE`), `CM4E/Gen/CMLattice.lean`,
    `CM4E/Gen/Instances.lean`;
  - in `lean_lsg`: `LSG/W88/Statement.lean`, `LSG/W88/K5dNonIsog.lean`, `LSG/W88/MStarCopyStd.lean`, and the header of
    `LSG/W88/K5dMain.lean`.
* Paper:
  - the first draft of Theorem SE §1;
  - the merged draft §4.3 (l. 1540–1646: Theorem 4.12 = `thm:SE`, Cor. `cor:SE4`, Lemma `lem:SE0`,
    the proof, and the Example);
  - `paper.tex` §4.1 (l. 470–502: `d₀ = 2`, (NR)).
* Baselines, whose findings are not repeated here:
  - `REFEREE_HYP_M` #1 and `REFEREE_HYP_SMG` #14 (`G_a` in `d₀`);
  - `REFEREE_BRIDGE_STD` (transport, `gmStd`);
  - `REFEREE_HYP_XA` (format, the `gmFX` uniform condition).

**Process.** No project file other than this report and `reviews/checks/hypse/` was edited, and no git command was run.
The scratch files are:
* `reviews/checks/hypse/AxSE.lean` and `AxSE.out`: the axiom audit, plus `#check`/`#print` of the statements.
* `reviews/checks/hypse/NonIsogField.lean` and `NonIsogField.out`: five referee lemmas, proved sorry-free with standard
  axioms only:
  - `sameField_of_not_nonIsog`, `not_nonIsog_of_field`, `nonIsog_of_field`, `nonIsog_iff`: `NonIsog` ⇔ `k ≠ k'`;
  - `thmSE_paper`: Theorem 4.12(1) with the paper's hypothesis `k ≠ k'` and arbitrary nonzero periods `Ω`, `Ω'`.

The oleans of the new files (10:29–10:50) are newer than their sources. `lake env lean` on each scratch file took about
30 s.

## Verdicts

* **Item 1 (`gmFX1`, `HyperplaneKappa`, `frameX1_false`): CORRECT.**
  - Putting `G_a²` in `d₀` (weight 0) is the reading already accepted in `REFEREE_HYP_M` #1 and `SMG` #14, and justified
    in `paper.tex` §4.1. It is exactly `gmStd`'s convention (`d₂ = m`, `G_a^{d₀}` not counted).
  - In the transport, `hd` holds with equality, `0 + 2m ≤ 0 + 2m`.
  - The reading is no longer only a reading: `lean_lsg` proves `HyperplaneKappa (gmStd 2 0 Ls)` in Lean for the families
    used here (#3).
  - The count is right. With `m = 3n`, `κ ≥ n` and `d − 1 − t = 1`, (5.4) is `3n > 2·dim Q − κ`. That follows from
    `dim Q < 2n`, with slack at least 2.
* **Item 2 (model soundness of `gmES`/`gmSE`, uniform condition): CORRECT WITH NOTES.**
  - For non-isogenous `E`, `E'` the model is sound, and the uniform condition is now a Lean theorem (`uniform_SE`).
  - Subgroups mixing the two `E`-blocks are harmless: `μ₁` reads only block 1 and `μ₂` only blocks 2 and 3, so a vector
    `(s₁, s₂, 0)` with both `μ` zero has `s₁ = s₂ = 0` by `k`-independence of `γ`.
  - The only counterexample is the mixing of block 2 (`E`) with block 3 (`E'`) when `E ~ E'`. There `Thm11KappaSE L L'` is
    *false* (#7).
  - That case is harmless: `hT` (`L'.ω/L.ω ∉ ℚ̄`) fails for isogenous curves, and the bridge discharges `Thm11KappaSE`
    only under `NonIsog`. But the docstring of `Thm11KappaSE` does not say this (#8).
  - `NonIsog` in both directions is exactly `k ≠ k'`. One direction implies the other (#10).
* **Item 3 (bridge): CORRECT.**
  - `phiFX` is a linear isomorphism. It sends `alg` into `algStd`, `D·lam` into `Lam` (through the subgroup `lamLogF`,
    using the addition law `logE_add`), and `per` into `span Per`.
  - It pulls every nonzero `SubgroupData.tan` back into `gmES.sub`: an `h₀` part gives an algebraic `G_a` vector with
    `Ψ'' ≠ 0`, and otherwise `huni` applies.
  - `uniform_SE` proves exactly the `huni` that `hyperplaneKappa_gmES` needs. It uses `abTan_rat_nonIsog` and
    `mul_mem_of_blockConst` correctly.
  - `hypStd_of_pair` returns `MStarCopy.HyperplaneKappa (MStarCopy.gmStd …)` and is used by `exact` for
    `CM4E.Waldschmidt.HyperplaneKappa (Bridge.gmStd …)`. So the kernel checks that the verbatim copy is definitionally the
    `lean_mstar` statement.
* **Item 4 (faithfulness of the theorems): CORRECT WITH NOTES.**
  - `LtildeE` is `ℚ̄ + ℚ̄𝓛_E` as a set, and `LtildeEE` is `ℚ̄ + ℚ̄𝓛_E + ℚ̄𝓛_{E'}`.
  - The independence hypothesis, `t`, and the conclusion `¬(ty₁ ∈ … ∧ ty₂ ∈ …)` match Theorem 4.12(1).
  - The differences from the paper are all harmless:
    - `Ω = L.ω`, `Ω' = L'.ω` instead of arbitrary nonzero periods (absorbed into `c`);
    - `NonIsog` both ways instead of `k ≠ k'` (equivalent, proved);
    - the extra hypotheses `CMMulLogE L`, `CMMulLogE L'`, which are true for every CM lattice with algebraic invariants
      and are proved for `ϖℤ[i]` and `Ω_ρℤ[ρ]`.
  - The referee lemma `thmSE_paper` derives the paper's form (arbitrary `Ω`, `Ω'`, hypothesis `k ≠ k'`) from
    `thmSE_of_nonIsog` in 25 lines.
  - `thmSE_varpi_omegaRho` is Theorem 4.12(1) for the Example's curves. It is not the Example itself, which goes through
    Cor. SE4 and Lemma SE0 (#14).
  - `transcendental_div_of_nonIsog` is correctly stated and soundly proved, with no circularity: W88 §5d with `V = W` a
    `ℚ̄`-line, inside a closed Lean proof.
* **Item 5 (axioms): CORRECT.** All three requested declarations depend only on `propext`, `Classical.choice` and
  `Quot.sound`, and so do the six further declarations audited (#16). The three new files contain no `sorry`, `axiom`,
  `admit` or `native_decide`.

**No FATAL or MAJOR issue was found.** The unconditional results `Bridge.thmSE_of_nonIsog`,
`Unconditional.thmSE_varpi_omegaRho` and `Unconditional.transcendental_omegaRho_div_varpi` are Lean theorems over
Mathlib. No form of W88 is assumed: `lean_lsg`'s `hypStd_of_pair` is proved with standard axioms.
* The general theorem has these residual hypotheses: algebraic invariants, `NonIsog`, and `CMMulLogE`.
* The `ϖ`/`Ω_ρ` wrappers have only one: `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`.

So their correctness reduces to the faithfulness of the statement (item 4), not to the soundness of any model.

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | 1, `d₀` | `G = G_a² × G₂`, where `G₂ = E^r × E^r × E'^r` has no `G_a` or `G_m` factor. So `d₀ = 2` and `d₁ = 0` are maximal, and `d₂ = dim Q = 3r` exactly. (5.4) does not involve `d₀` (W88 p. 394; `REFEREE_HYP_M` #1). A model that counted `G_a²` in `d₂` (`gmFX`) would only weaken the hypothesis: it would need `2·dim Q + 4 < 4n`, i.e. `r ≥ 3`. `gmFX1` is the exact count and matches `gmStd 2 0` field by field |
| 2 | OK | 1, `frameX1_false` count | `m = 3n`: the `3n` lifts are `ℚ`-independent, because their `Ψ''₁`-values `θ_h·(A, x₁, x₂)` are independent over `K = span θ` (`hind`). `κ ≥ n` from the `n` period lifts. `W = ker Ψ''` (dimension `dim Q`, `ℚ̄`-rational via `T`), `V = ker(Ψ''₂ − σΨ''₁)` a hyperplane, `d − 1 − t = 1`. Premise `3n > 2·dim Q − κ`. With `dim Q ≤ 2n − 1` and `κ ≥ n`, the right side is at most `3n − 2`. Conclusion: an algebraic `x ∈ V` with `Ψ''(x) ≠ 0` would make `σ` algebraic. Correct |
| 3 | OK (strengthening) | 1, status of the reading | `LSG.W88.hypStd_of_pair` proves `HyperplaneKappa (gmStd d₀ d₁ Ls)` in Lean, for all `d₀` and `d₁`, with only standard axioms. `Ls` is any family taking two non-isogenous values with algebraic invariants. The proof (`K5dMain.lean` header) goes through `lean_lsg`'s proved Thm 4.1, Roy's (NR)-free linear case via StrongSix, and the corner analysis. So "`G_a` has weight 0 in (5.4)" is a *theorem* in the regime used here (`d₀ = 2`, `d₁ = 0`). `REFEREE_BRIDGE_STD` issue 2 (`d₀ > 0` needs Roy) is resolved for this family |
| 4 | OK | 2, group, `lam`, `per`, `alg` | `lamES` consists of `v e_j` (`v ∈ 𝓛_{E_j}`, where `LogE` includes the lattice) and algebraic `G_a` vectors, so `lam = span_ℚ lamES ⊂ ℚ ⊗ Λ(G)`. `perES` consists of `ω e_j` (`ω ∈ Λ_j`). `algVF × ℚ̄²` is the standard `ℚ̄`-structure (`z_j` dual to `dx/y`). The paper's `G'' = G^n/U` is isogenous to Lean's `G_a² × E^r × E^r × E'^r`, and Lean applies W88 to its own group, as in `REFEREE_HYP_XA` #1 |
| 5 | OK | 2, lifts | `eLiftB` writes `x ∈ K` in the `k`-basis `γ`, and needs `αv ∈ 𝓛_E` (`CMMulLogE`). The period lift `p_h = θ_hΩ e_{b1} + θ_h cΩ' e_{b3}` (with `θ_h c` written in the `k'`-basis `γ'`) has `Ψ'' = θ_hΩ(1, t)`. The data lifts have `Ψ'' = θ_h(y_j, ty_j)`: block 1 carries `y_j`'s logarithms, the `G_a` vector carries `(β₀, δ₀)`, block 2 carries `ty_j`'s `E`-logarithms, and block 3 its `E'`-logarithms. This is the paper's `w = (Ω, cΩ')`, `v_j = (y_j, ty_j)` |
| 6 | OK | 2, uniform condition, non-isogenous | Connected subgroups are `H₀ × B₁₂ × B'`. A nonzero `H₀` gives `Ψ'' = (a₁, a₂) ≠ 0`. A nonzero `B₁₂` has a nonzero lattice vector `(s₁, s₂, 0)` with `s_i ∈ ω k^r`. `μ₁ = Σγ s₁` and `μ₂ = Σγ s₂` vanish only if `s₁ = s₂ = 0` (`γ` is `k`-independent). The same holds for `B'` with `γ'`. **Mixing blocks 1 and 2 cannot defeat this,** because `μ₁` and `μ₂` read disjoint blocks. `uniform_SE` is the Lean proof |
| 7 | NOTE | 2, isogenous case: `Thm11KappaSE` false | Let `L = L'` (any CM lattice with algebraic invariants), `r = 1`, `γ = γ' = (1)` (adapted: `Kspan = k`). The antidiagonal `{(0, P, −P)} ⊂ E³` has tangent `ℂ(0, 1, −1) ⊂ ker μ₁ ∩ ker μ₂`, so `gmSE` misses it. In fact `HyperplaneKappa (gmSE L L (1) (1))` is false. Take `u ∈ 𝓛_E` non-torsion and `σ = u/ω` (transcendental, Masser). Take `V = ker(Ψ''₂ − σΨ''₁)`, `W = ker Ψ''`, and the six logs `(ω, u, 0)`, `(αω, αu, 0)`, `(ω, 0, u)`, `(αω, 0, αu)`, `(0, ω, −ω)`, `(0, αω, −αω)`. They are `ℚ`-independent (because `u/ω ∉ k`), `m = 6`, `κ ≥ 2`, so the premise `6 > 6 − κ` holds. But no member of `sub` lies in `V`, since that would make `σ` algebraic. So `Thm11KappaSE L L'` fails for every isogenous pair (rescale by the isogeny). **Not a leak:** isogeny forces `L'.ω/L.ω ∈ ℚ̄`, so `thmSE`'s `hT` is false, and `thm11KappaSE_of_nonIsog` assumes `NonIsog`. This is the same pattern as `REFEREE_HYP_XA` #7 |
| 8 | MINOR (docs) | 2, `Thm11KappaSE` docstring (`AbVar/SE.lean:148–150`), module docstring l. 40–42 | The docstring says "W88 §5d for `G_a² × E^r × E^r × E'^r` … for every pair of adapted bases", and l. 40–42 says the uniform condition "is sound for `gmSE`". Neither says that this holds only for non-isogenous `E`, `E'`, and that for isogenous curves the hypothesis is false while `hT` is false too (#7) | Add "(sound, and true, only when `E`, `E'` are not isogenous; for isogenous curves it is false, but then `hT` fails)". Alternatively add `NonIsog L.pp L'.pp →` to `Thm11KappaSE`. `thm11KappaSE_of_nonIsog` would be unaffected |
| 9 | OK | 3, transport | `phiFX (q, s₁, s₂) = ((s₁, s₂), (), q)` is bijective, with inverse checked. `alg ↦ algStd`. For `lam`: `exists_nsmul_mem_closure` and the closure of `lamES` lie inside the subgroup `lamLogF ⊂ Lam`, which needs `logE_add` and so all `g₂` algebraic (supplied). `per ↦ span Per`, since `genE j ω ↦ (0, 0, ω e_j) ∈ Per`. For `sub`: the torus part is trivial (`d₁ = 0`, `torusLie` on `Fin 0`); `h₀ ≠ 0` gives an algebraic `(0, a₀, a₁)` with `Ψ'' = a ≠ 0`; otherwise `t ≠ 0` and `huni` applies. `hd` holds with equality. This is the same pattern as `Bridge/SMG.lean`, made generic in `(Ls, a₁, a₂)` |
| 10 | NOTE | 2/4, `NonIsog` vs `k ≠ k'` | `NonIsog L L'` means "no `λ ≠ 0` with `λΛ ⊂ Λ'`", i.e. no isogeny `E → E'`. The referee lemma `nonIsog_iff` proves, for `CMLattice`s, `NonIsog L.pp L'.pp ↔ ¬∃ a b : ℚ, L.α = a + b·L'.α`, that is, `k ≠ k'`. `nonIsog_of_field` proves that `k ≠ k'` gives both directions. So the two hypotheses `hni`, `hni'` are exactly the paper's `k ≠ k'`, and `hni'` is redundant (it follows from `hni`). Both are needed only because `lean_lsg`'s `hni_of_pair` is phrased with the one-sided `NonIsog`. `k ≠ k'` is also necessary: for `k = k'`, `t ∈ ℚ̄` and the conclusion fails trivially |
| 11 | OK | 4, `LtildeE`, `LtildeEE` | They are finite `ℚ̄`-combinations, with `N = 0` allowed, plus a `ℚ̄` constant. `LogE P v` is `v ∈ Λ`, or `℘(v)`, `℘'(v) ∈ ℚ̄`, i.e. `exp_E(v) ∈ E(ℚ̄)` (origin included). As sets these are `ℚ̄ + ℚ̄𝓛_E` and `ℚ̄ + ℚ̄𝓛_E + ℚ̄𝓛_{E'}`. The paper's `𝓛_E` (elliptic logarithms of `E(ℚ̄)`) includes the periods, so they match |
| 12 | NOTE | 4, `Ω`, `Ω'`, curves | Lean fixes `Ω = L.ω` and `Ω' = L'.ω`, the generators with `Λ = ω(ℤ + αℤ)`. Any nonzero periods are `sω`, `s'ω'` with `s ∈ k^×`, `s' ∈ k'^×`, so `t = (cs'/s)·ω'/ω`, and independence of `Ω, y₁, y₂` is the same as independence of `ω, y₁, y₂`. The referee lemma `thmSE_paper` carries this out. Every CM curve over `ℚ̄` is `ℚ̄`-isomorphic to some `E_{L.pp}`: choose `Λ = ω(ℤ + τℤ)` with `Im τ > 0`, `τ² = p + qτ`, and `η₀` from Legendre's relation. Such an isomorphism rescales `𝓛`, `Λ` and the targets by `ℚ̄^×`. So no generality is lost |
| 13 | NOTE | 4, `CMMulLogE` | This is an extra hypothesis of `thmSE`/`thmSE_of_nonIsog` with no counterpart in the paper. It is true for every CM lattice with algebraic invariants: `Nα` is an endomorphism for some `N ≥ 1`, and `αv` is a division point of `[Nα]v`, so its coordinates are algebraic. It is proved for `latI` and `latRho` (`ELog.lean`), so the wrappers do not carry it. Suggest saying in the `thmSE_of_nonIsog` docstring that it is a true arithmetic input that is not yet proved in general |
| 14 | MINOR (docs) | 4, the `ϖ`/`Ω_ρ` instance vs the paper's Example | `thmSE_varpi_omegaRho` is Theorem 4.12(1) with `E = E_i` (`ϖℤ[i]`, the curve `y² = 4x³ − 4x`) and `E' = E_ρ` (`Ω_ρℤ[ρ]`, the curve `y² = 4x³ − 4`), which are the Example's curves. The Example's statement ("`℘_i(Ω_ρ/ϖ)` and `℘_i(Ω_ρu/ϖ)` not both algebraic for `u ∈ 𝓛_{E_i} ∖ {0}`") goes through Cor. SE4 with `(y₁, y₂) = (1, u)`. It follows from the Lean wrapper only when `ϖ, 1, u` are `ℚ̄`-independent, i.e. `u` non-torsion, by Masser. For torsion `u ≠ 0` it needs Cor. SE4's reduction and the full Lemma SE0 (`Ω_ρ ∉ 𝓛̃_{E_i}`), which Lean does not have: `transcendental_div_of_nonIsog` is only `Ω'/Ω ∉ ℚ̄`. The docstrings call the wrapper "Theorem SE (SE) for `E_i`, `E_ρ`", which is accurate. Just do not cite it as "the Example". Optional: add the `℘`-form with the independence of `ϖ, 1, u` as a hypothesis |
| 15 | OK | 4, `transcendental_div_of_nonIsog` | The statement is right: `P`, `P'` are any period pairs with algebraic invariants, non-isogenous, `ω ∈ Λ_P ∖ 0`, `ω' ∈ Λ_{P'} ∖ 0`, and the conclusion is `ω'/ω ∉ ℚ̄` (true: Schneider–Wüstholz). The proof uses §5d on `E × E'` (`gmStd 0 0 ![P, P']`) with `V = W = ℂ(1, β)`, which is `ℚ̄`-rational if `β ∈ ℚ̄`, and `Y = ℤ(ω, ω')`. Then `d − 1 − t = 0`, so the premise is `1 > 0`. `V` contains a nonzero abelian tangent, which splits by `mul_mem_of_blockConst`, and on the graph of `z ↦ βz` with `β ≠ 0` that forces it to vanish. **No circularity:** `hypStd_of_pair` takes no transcendence input (its signature is algebraic invariants plus `NonIsog`), and the whole chain has standard axioms. `thmSE_of_nonIsog` feeds this into `thmSE`'s `hT`, which is legitimate. It is the part of Lemma SE0 that the proof uses, and the docstring says so |
| 16 | OK | 5, axioms | see `AxSE.out`. `thmSE_varpi_omegaRho` (Unconditional and Bridge), `thmSE_of_nonIsog` and `transcendental_omegaRho_div_varpi` depend only on `propext`, `Classical.choice`, `Quot.sound`. So do `transcendental_div_of_nonIsog`, `uniform_SE`, `thm11KappaSE_of_nonIsog`, `hyperplaneKappa_gmES`, `AbVar.thmSE`, `frameX1_false` and `LSG.W88.hypStd_of_pair` |
| 17 | MINOR (docs) | `TRUST.md`; `Waldschmidt.lean:12–14` | `TRUST.md` has no row for Theorem SE: none for `Thm11KappaSE` and its isogenous caveat (#7), none for the unconditional status of `thmSE_of_nonIsog`, and none for the residual hypotheses (`CMMulLogE` in general, `hg₃'` for the wrapper). The instance list in `Waldschmidt.lean` omits `AbVar.Thm11KappaSE` (and still `AbVar.Thm11KappaXA`, `REFEREE_HYP_XA` #20) | Add a TRUST row: "Theorem SE(1): unconditional for non-isogenous CM lattices (with `CMMulLogE`), via `lean_lsg` `hypStd_of_pair` (6ebc17f); wrapper `E_i`, `E_ρ`: only `hg₃'`". Extend the instance list |
| 18 | COSMETIC | `Unconditional.lean:56–57` | "…(`LSG.W88.hypStd_of_pair`), so (`CM4E/Bridge/SE.lean`), assuming only…" does not parse | Reword: "…, so `CM4E/Bridge/SE.lean` proves, assuming only `g₃(Ω_ρℤ[ρ]) ∈ ℚ̄`:" |

## Details

### 1. The `d₀` question, and why it is now settled in Lean (#1, #3)

W88 Thm 1.1 with (5.4) writes `G = G_a^{d₀} × G_m^{d₁} × G₂` with `d₀`, `d₁` maximal, and requires
`m > (d₁ + 2d₂ − κ)(d − 1 − t)`, `d₂ = dim G₂`; `d₀` does not appear.
* For `G_a² × E^r × E^r × E'^r` we have `Hom(G, G_a) = ℚ̄²` and `Hom(G, G_m) = 0`. So `d₀ = 2`, `d₁ = 0`, `d₂ = 3r`.
* `gmFX1` uses exactly these values, as does `gmStd 2 0 Ls` (`d₂ = m`).
* The transport hypothesis `hd` (`G₂.d₁ + 2G₂.d₂ ≤ G₁.d₁ + 2G₁.d₂`) reads `0 + 2m ≤ 0 + 2·finrank (Fin m → ℂ)`, an
  equality. It is discharged by `simp` (`Bridge/SE.lean:181`).

The previous reports accepted this reading on the basis of W88 p. 385 and Waldschmidt's own use of `d₀ = 2`
(Cor. 2.1). It is now also a Lean theorem in this regime: `hypStd_of_pair Ls … 2 0` *is* `HyperplaneKappa (gmStd 2 0 Ls)`
with `G_a²` of weight 0, proved with standard axioms. So `hd` cannot hide an over-strong hypothesis.

### 2. The counterexample for isogenous curves (#7) [Proved modulo Masser 1975]

Take `L = L'`, `r = 1`, `γ = γ' = (1)`. `IsAdaptedFieldBasis α (1)` holds: `θ = (1, α)` is `ℚ`-independent, and
`ℚ + ℚα = k` is a field of algebraic numbers.
* The coordinates are `(z₁, z₂, z₃; s₁, s₂)`, with `μ₁ = z₁` and `μ₂ = z₂ + z₃`.
* The abelian subvariety `{(0, P, −P)}` has tangent `t = ℂ(0, 1, −1)`. Its lattice vectors `(0, ω, −ω)`, `(0, αω, −αω)`
  span `t` over `ℝ`, and `μ₁ = μ₂ = 0` on `t`. So `gmSE.sub` (an algebraic vector with `Ψ'' ≠ 0`) misses it.

To show that `HyperplaneKappa (gmSE L L (1) (1))` is actually false:
* Choose a non-torsion `u ∈ 𝓛_E` and put `σ = u/ω`. Then `σ ∉ ℚ̄`, since `ω` and `u` are `ℚ̄`-dependent only if they are
  `k`-dependent (Masser).
* Put `V = ker(Ψ''₂ − σΨ''₁)` and `W = ker Ψ''` (rational, dimension 3), so `d − 1 − t = 1`.
* Take the six generators `(ω, u, 0)`, `(αω, αu, 0)`, `(ω, 0, u)`, `(αω, 0, αu)`, `(0, ω, −ω)`, `(0, αω, −αω)` (zero `G_a`
  part).
  - All six lie in `lam` (with `αu ∈ 𝓛_E` by CM) and in `V`.
  - They are `ℚ`-independent. The first coordinate forces `c₁ = −c₃` and `c₂ = −c₄`. The second gives
    `(c₁ + c₂α)u ∈ kω`, hence `c₁ = c₂ = 0`, and then the rest vanish.
  - The last two are periods, so `κ ≥ 2`, and (5.4) reads `6 > 6 − κ`, which holds.
* A nonzero `S ∈ sub` with `S ≤ V` would contain an algebraic `x` with `Ψ''(x) = λ(1, σ)` and `λ ≠ 0`, which forces
  `σ ∈ ℚ̄`. Contradiction.

For isogenous `L ≠ L'`, compose with the isogeny. Since `hT` fails in exactly these cases (an isogeny between curves over
`ℚ̄` has an algebraic multiplier, so `ω'/ω ∈ ℚ̄`), `thmSE` stays vacuous whenever its `hW` would be false.

### 3. Referee lemmas (#10, #12)

`reviews/checks/hypse/NonIsogField.lean`, all with axioms `[propext, Classical.choice, Quot.sound]`:
```lean
theorem sameField_of_not_nonIsog (L L' : CMLattice) (h : ¬ NonIsog L.pp L'.pp) : ∃ a b : ℚ, L.α = a + b * L'.α
theorem not_nonIsog_of_field (L L' : CMLattice) (h : ∃ a b : ℚ, L.α = a + b * L'.α) : ¬ NonIsog L.pp L'.pp
theorem nonIsog_of_field (L L' : CMLattice) (h : ¬ ∃ a b : ℚ, L.α = a + b * L'.α) :
    NonIsog L.pp L'.pp ∧ NonIsog L'.pp L.pp
theorem nonIsog_iff (L L' : CMLattice) : NonIsog L.pp L'.pp ↔ ¬ ∃ a b : ℚ, L.α = a + b * L'.α
theorem thmSE_paper (L L' : CMLattice) (hg₂ hg₃ hg₂' hg₃') (hk : ¬ ∃ a b : ℚ, L.α = a + b * L'.α)
    (hCM : CMMulLogE L) (hCM' : CMMulLogE L') (Ω Ω' : ℂ) (hΩ : Ω ∈ L.pp.lattice) (hΩ0 : Ω ≠ 0)
    (hΩ' : Ω' ∈ L'.pp.lattice) (hΩ'0 : Ω' ≠ 0) (c) (hc) (hc0) (y₁ y₂) (hy₁ hy₂) (hind : …Ω, y₁, y₂ ℚ̄-independent…) :
    ¬ (c * Ω' / Ω * y₁ ∈ LtildeEE L.pp L'.pp ∧ c * Ω' / Ω * y₂ ∈ LtildeEE L.pp L'.pp)
```
* `α ∈ ℚ + ℚα'` with `α ∉ ℚ` is the same as `ℚ(α) = ℚ(α')`, i.e. `k = k'`.
* `sameField_of_not_nonIsog`: if `λΛ ⊂ Λ'`, then `α(m + nα') = m' + n'α'`. Multiply by the conjugate; the norm
  `m² + mnq' − n²p'` is nonzero.
* `thmSE_paper` is Theorem 4.12(1) verbatim: the hypothesis is `k ≠ k'`, and `Ω`, `Ω'` are arbitrary nonzero periods. The
  only hypotheses beyond the paper are `CMMulLogE` (#13) and the Weierstrass normalisation (#12).

### 4. Subgroups mixing the two `E`-blocks (#6)

The worry was a subvariety `B ⊂ E^r × E^r` (blocks 1 and 2) that is a graph, along which `μ₁` and `μ₂` cancel.
* That cannot happen: `μ₁ = Σγ_i z_{b1,i}` has no block-2 term, and `μ₂ = Σγ_i z_{b2,i} + Σγ'_i z_{b3,i}` has no block-1
  term.
* So on `T(B)` the two forms vanish separately on the block-1 and block-2 components of each lattice vector, and
  `k`-independence of `γ` kills each component.
* The only cancellation possible is inside `μ₂`, between block 2 (`E`) and block 3 (`E'`). It needs
  `Hom(E, E') ≠ 0`, which is #7.

`uniform_SE` handles this exactly. It splits a nonzero lattice vector `z ∈ t` as `Dz + (z − Dz)`, with `D` the indicator
of the `E`-blocks (`mul_mem_of_blockConst`, valid because `E ≁ E'`). Then it applies `lattice_eq_zero` to blocks 1 and 2
with `(L, γ)`, and to block 3 with `(L', γ')`.

## Suggested fixes (all documentation)

1. `Thm11KappaSE` docstring and the soundness paragraph of `AbVar/SE.lean` (l. 40–42 and 148–150): restrict the
   soundness claim to non-isogenous `E`, `E'`. State that for isogenous curves the hypothesis is false but `hT` fails too
   (#7, #8). Alternatively add `NonIsog L.pp L'.pp →` to `Thm11KappaSE`.
2. `thmSE_of_nonIsog` docstring: say that `hni ∧ hni'` is equivalent to `k ≠ k'`, and that `hni'` is redundant (#10). Say
   that `CMMulLogE` is a true arithmetic input, proved for `ϖℤ[i]` and `Ω_ρℤ[ρ]` (#13). Optionally promote
   `nonIsog_iff` and `thmSE_paper` from `reviews/checks/hypse/NonIsogField.lean` into `Bridge/SE.lean`, which would give
   the paper's statement verbatim (#12).
3. Do not cite `thmSE_varpi_omegaRho` as the paper's Example. It is Theorem 4.12(1) for the Example's curves, and the
   Example itself needs Cor. SE4 and the full Lemma SE0 (#14).
4. `TRUST.md`: add the Theorem SE row (#17). `Waldschmidt.lean`: extend the instance list (#17). `Unconditional.lean`:
   fix the sentence at l. 56–57 (#18).
