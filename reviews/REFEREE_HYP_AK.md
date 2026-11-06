# Referee report: `CM4E/AbVar/MGAK.lean` (`K`-forms of MG-A, MG♮-A; models `gmAK`, `gmAnK`) and `CM4E/AbVar/CorA2.lean` (Cor. A2)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope (commit 041b468).**
* Read in full: `CM4E/AbVar/MGAK.lean`, `CM4E/AbVar/CorA2.lean`.
* Read for context:
  - `CM4E/Gen/Frame2.lean` (`PsiG`, `gmF2`, `frame2_false_K`);
  - `CM4E/Gen/Frame.lean` (`TF`, `tor1`, `tor2`, `qv`, `algF`, `lamGen`, `perGen`, `gmF`);
  - `CM4E/Waldschmidt.lean` (`GroupModel`, `HyperplaneKappa`);
  - `CM4E/AbVar/Basis.lean` (`thetaD`, `KspanD`, `IsAdaptedBasisD`, `coordsD`);
  - `CM4E/AbVar/ThmA.lean` (`zetaN`, `thetaA`, `perAgen`, `algA`, `gmA`, `perA5`, `WuestholzA5`);
  - `CM4E/AbVar/ThmAn.lean` (`perAngen`, `algAn`, `gmAn`);
  - `CM4E/Gen/MGK.lean` (`KLog`), `CM4E/Gen/SMG.lean` (`Ltilde`), `CM4E/Gen/MG13.lean` (`mem_Ltilde_of_log`,
    `pi_mem_Ltilde`), `CM4E/Gen/ThmMCor.lean` (`alg_mem_Ltilde`);
  - TRUST.md §8 and the Lemma U paragraph.
* Paper [II] (draft [II]):
  - thm:A and cor:A2intro (l. 84–111);
  - §`sec:tool` with (S1), (P), (Ch), (W), (F1)–(F4) (l. 261–413);
  - thm:MGA with its proof (l. 415–463), thm:MGnA with its proof (l. 473–509), the proof of thm:A (l. 511–538);
  - cor:A2 with its proof (l. 550–565), rem:noChud (l. 567–573).
* Baseline:
  - `REFEREE_HYP_A.md` (`gmA`, the `y⁵`/`y⁷` instances, simplicity and CM type, `WuestholzA5`);
  - `REFEREE_HYP_AN.md` (`gmAn`, `Q''`, the second-kind period `P̄`);
  - `REFEREE_HYP_MGK.md` (`frame2_false_K`, the uniform `sub`, and the elliptic `K`-forms).

**Process.** I edited no Lean file and ran no git command. My scratch files are in `reviews/checks/hypak/`:
* `axAK.lean` / `axAK.out`: axiom audit, `#check` of the four theorems, and `#print` of `NotLtildeA`, `Thm11KappaAK`,
  `KSlotA`, `KFibA`. It also has five `example`s, all of which compile:
  1. `gmAK … ∅` has the same `per`, `d₁`, `d₂` as `gmA` (`rfl`);
  2. `lamAK … ∅ = lamGen (perAgen …)` (proved);
  3. `gmAnK … ∅` has the same `per`, `d₂` as `gmAn` (`rfl`);
  4. `NotLtildeA P → Transcendental ℚ (P/π)`;
  5. `NotLtildeA (perA5 0) → WuestholzA5`.

  Both source files are older than their oleans (`MGAK` 01:26:57 vs 01:27:19, `CorA2` 01:30:22 vs 01:31:34).
* `check_ak.py` / `check_ak.out` (mpmath):
  - `B(1/5,1/5) = Γ(1/5)²/Γ(2/5)`, and the Beta integral by quadrature;
  - the rewriting in `corA2_beta5`: `bπB = (b/(1 − ζ))πP` and `cπ²/B = c(1 − ζ)π²/P`, to 10⁻¹²⁰;
  - a PSLQ sanity check of `NotLtildeA` (see #12).

**Axioms.** `mgA_K`, `mgAn_K`, `corA2` and `corA2_beta5` depend only on `propext`, `Classical.choice`, `Quot.sound`.
`#check corA2_beta5` shows exactly three premises: `Thm11KappaAK 5 2 (s ↦ s+1) perA5 0 ∅`, `WuestholzA5` and
`NotLtildeA (perA5 0)`.

## Verdict: CORRECT WITH NOTES (no FATAL or MAJOR issue)

* **`gmAK`, `gmAnK` are sound W88 models.** This holds whenever the parameter `LA` (resp. `LAn`) consists of
  eigen-coordinate tuples of logarithms of algebraic points of `A` (resp. coherent (base tuple, `σ̄`-fibre value) pairs of
  one logarithm of an algebraic point of `A^♮`). The coordinates must be the ones in which `P` (resp. `(P, P̄)`) is
  written.
  - With `LA = ∅` (resp. `LAn = ∅`), they are `gmA` and `gmAn` with `gmF`'s product-form `sub` replaced by the uniform
    `sub`. That replacement is sound for both groups.
  - For other parameter sets the hypotheses can be false, which leaves the theorems vacuous (#5). This is the same
    situation as `LA` in X7, and it is stated only in docstrings.
* **Statement fidelity.** `mgA_K` and `mgAn_K` are exactly thm:MGA and thm:MGnA for `F = ℚ(ζ_N)` and every number field
  `K ⊇ F(i, c)`. This is the paper's own range of `K`, so no Baker reduction is missing here (#9). The proviso is that
  `LA` (`LAn`) is taken to be all such tuples (pairs).
* **Cor. A2.** `corA2` follows the paper's proof of cor:A2 step by step. `NotLtildeA` is a true consequence of Wüstholz's
  analytic subgroup theorem on `G_a × G_m^m × A`, and it holds for `P = (1 − ζ₅)B(1/5,1/5)`.
  - `corA2_beta5` is cor:A2 for `B(1/5,1/5)` (Mathlib's `betaIntegral`), with free `a, b, c ∈ ℚ̄ˣ`. This includes the
    paper's intro example (`a = b = c = 1`).
  - Its second named input `WuestholzA5` is redundant: it follows from `NotLtildeA` (proved in `axAK.lean`).

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `gmAK` with `LA = ∅` vs `gmA` | `per`, `d₁ = 2n`, `d₂ = gr` agree (`rfl`), and `lamAK … ∅ = lamGen (perAgen …)` (proved). The `PsiG` with `μ = 0` is `gmF`'s `Ψ''`. Only `sub` changes |
| 2 | OK | uniform `sub` for `G_m^{2n} × A^r` (`gmAK`) | Connected subgroups are `T_L × B_S` (by (P), (S1)). A rational `l ≠ 0` in `T_L` gives `Ψ''(l) = (θᵀl₁, θᵀl₂) ≠ 0` (θ is `ℚ`-independent). `T(B_S)` is `ℚ̄`-rational and `λ = Σ_j b_j z(s₀, j) ≢ 0` on it for `S ≠ 0` (REFEREE_HYP_A #2), so it has an algebraic vector with `Ψ'' = (0, λ) ≠ 0`. Every nonzero connected subgroup is therefore in `sub` |
| 3 | OK | uniform `sub` for `G_m^{2n} × Q''` (`gmAnK`) | Every nonzero connected `H'' ⊂ Q''` contains the fibre (REFEREE_HYP_AN #3), so `qv (0, 1)` is algebraic with `Ψ'' = (0, 1)`. The torus case is as in #2, and the products follow from Goursat |
| 4 | OK | added logarithms `[ζ^e]v` (`twistA`, `twistAn`) | For `v = (z_s(u))_s` with `u ∈ Λ(A)`: `[ζ^e]u` in copy `j` is a logarithm of `[ζ^e]exp(u) ∈ A(ℚ̄)`, and its coordinates are `ζ^{κ_s e}v_s`, which is the convention already verified for the periods (`perAgen`). For a coherent pair `(z(ũ), w(ũ))`: the image of `[ζ^e]ũ` in copy `j` under `(A^♮)^r → Q''` is `(twistA j e v, b_j ζ^{(N−1)e} w)`, which is the `perAngen` convention. `Λ` is a `ℚ`-space, so `span_ℚ lam ⊂ Λ(G'')`. `per`, `alg` and `d`-values are unchanged, so `κ` cannot be inflated |
| 5 | MINOR (latent, docs) | conditions on `LA`, `LAn` | Soundness needs three conditions: (i) each `v ∈ LA` is a full tuple `(z_s(u))_{s<g}` of one `u ∈ Λ(A)`; (ii) the `z_s` are the same `ℚ̄`-rational eigen-coordinates in which `P = (z_s(γ))_s` is written (no per-tuple rescaling, not even by a common algebraic factor ∉ ℚ, because `Λ(A)` is only a `ℚ`-space); (iii) for `LAn`, `v` and `w` come from the **same** `ũ` (base coherence). Pairs `(0, a)` with `a ∈ ℚ̄` are allowed. Incoherent or rescaled entries make the hypotheses false. Example: put tuples with `s₀`-coordinates `s·log 2` and `s·log 3` in `LA`; then `mgA_K` (with `x = (log 2, log 3)`, `y = 0`, and Baker for the `K`-independence) derives `False`. These conditions appear only in docstrings (`MGAK.lean:23–26, 132–133, 309–311`). No theorem uses a nonempty `LA`/`LAn` (`corA2` uses `∅`) |
| 6 | NOTE (latent, inherited) | generic parameters | As for `Thm11KappaA`/`Thm11KappaAn` (REFEREE_HYP_A #5, REFEREE_HYP_AN #7), the hypotheses are W88 instances only for parameters from a genuine simple CM `A` with CM by `ℚ(ζ_N)`: `φ(N) = 2g`, and for `gmAnK`, `ζ ↦ ζ^{N−1}` must be a non-`Φ` slot. `mgAn_K` has no hypothesis to that effect |
| 7 | OK | Lemma U range | `gmAK` has the same `per` and `d` as `gmA`, so it is out of range only at `κ = 2n + 2gr − 1`. There `V` contains a rational toric line, which is an algebraic vector with `Ψ'' ≠ 0`, so it lies in the uniform `sub`, and the conclusion holds outright. `gmAnK` has `2N = 4n + 2gr ≥ 2n + κ` always. In the applications `κ = n` |
| 8 | OK | `mgA_K` vs thm:MGA | `KLog K` = `K𝓛`, and `KSlotA g P s₀ LA K` = the `K`-span of `{v s₀ : v ∈ insert P LA}`, which is `K·z_σ(Λ(A))` when `LA` is the set of all tuples. `s = cP_{s₀}/π`. "No `x₁, x₂ ∈ S_K` with `2πi, x₁, x₂` `K`-independent" is equivalent to `dim_K S_K ≤ 2`, because `S_K` is a `K`-space and `2πi ∈ S_K` (`s·2πi = 2ic·P s₀` with `P s₀ ∈ KSlotA` via `insert`). `κ s₀ = 1` (identity slot) is WLOG for `F = ℚ(ζ_N)`: relabel the CM action by a Galois automorphism, which only changes the free parameter `κ` |
| 9 | NIT (docstring too conservative) | "Baker reduction not formalised" (`MGAK.lean:17–18`) | thm:MGA and thm:MGnA are stated in [II] only for `K ⊇ F^c(i, c)`. Every such number field is `KspanD` of an adapted `b` (`θ(j, e) = ζ^e b_j`, `b` an `F`-basis), and `K ⊇ ℚ(ζ_N) = F^c` is automatic. So Lean's `K`-forms are the full paper statements for `F = ℚ(ζ_N)`. MG♮-A's descent from `[K′ : ℚ] ≥ 4` is also unnecessary, since `n ≥ φ(N) ≥ 2g ≥ 4`. Baker is needed only to pass from `ℚ`-independence to `K`-independence when applying the theorem (the proof of thm:A), not for the theorems themselves |
| 10 | OK | `mgAn_K` vs thm:MGnA | `s = cP̄/π`. `KFibA` = the `K`-span of the fibre values of `insert (P, P̄) LAn`, which is `K·w_σ(Λ(A^♮))` for `LAn` the set of all coherent pairs (fibre values are second-kind integrals `+ ℚ̄`). `2πi ∈ S♮_K` via `P̄ ∈ KFibA`. `hT : P̄/π ∉ ℚ̄` is exactly the `s ∉ K` needed. Scope: `hg2 : 2 ≤ g` (the case `g = 1` is [I]'s MG♮, `Gen.mgn_K`) |
| 11 | OK | `corA2` vs proof of cor:A2 | This is the same route: `mgA_K` with `LA = ∅`, `c = 1`, `s = P/π`, `x = (π², π²/P)`, `sx₁ = πP`, `sx₂ = π` (`π ∈ KLog` via `e^{iπ} = −1`), `e = 0`. `K ∋ a⁻¹, b⁻¹, c⁻¹, i`. Independence goes by the same case split: no `π²/P` term contradicts `transcendental_pi` (proved). `a₁ = a₀ = 0` gives `a₂π = 0`. `a₁ = 0 ≠ a₀` gives `P/π ∈ ℚ̄`, against `hT`. `a₁ ≠ 0, a₀ = 0` gives `P ∈ ℚ̄`. `a₁, a₀ ≠ 0` gives `P ∈ ℚ̄πP + ℚ̄π ⊂ ℚ̄𝓛`, using `πP ∈ ℚ̄𝓛` from `e^{bπP} ∈ ℚ̄`. The last two contradict `NotLtildeA`. This is the paper's `a′P ∈ ℚ̄𝓛` step, rearranged. There is no Chudnovsky input (rem:noChud), only `transcendental_pi`, `hT` and `hNot` |
| 12 | OK | `NotLtildeA` true | Suppose `P = β₀ + Σβ_kℓ_k`. Then `u = (1, ℓ, γ) ∈ Λ(G_a × G_m^m × A)` lies in the `ℚ̄`-hyperplane `z_{s₀} = β₀t + Σβ_kx_k`. By Wüstholz there is a connected `H` with `u ∈ T_H ⊂` that hyperplane. By (P), `H = G_a × T × B`. Since `γ ≠ 0` and `A` is simple, `B = A`, and `Lie A ⊄` the hyperplane: a contradiction. This needs only that `z_{s₀}` is `ℚ̄`-rational, `γ ∈ Ω(A) ∖ 0` and `A` simple. All three hold for `perA5 0` (one cycle to 10⁻⁶⁰, simple of type `{1,2}`: REFEREE_HYP_A #6–7). It is the paper's (W) in the form "on `G_a × G_m^r × A`" (l. 364). Numerically, PSLQ at 400 digits finds no relation of `B(1/5,1/5)` with `1, π, log 2, log 3, log 5, log φ` over `ℚ(√5)` (coefficients `≤ 10¹²`). A 120-digit hit is spurious: its residual at 400 digits is `3.8·10⁻⁹⁰` |
| 13 | NIT | redundant `hT` in `corA2`, `corA2_beta5` (`CorA2.lean:37, 137`) | `NotLtildeA P → Transcendental ℚ (P/π)`, since `aπ ∈ 𝓛̃` (proved in `axAK.lean`). So `WuestholzA5` is not an extra input of `corA2_beta5`. Drop `hT`, or derive it in one line |
| 14 | OK | `corA2_beta5` statement | Exponents `a·π²`, `b·(π·B)`, `c·(π²/B)` with `B = betaIntegral (1/5) (1/5)` (complex, `= Γ(1/5)²/Γ(2/5)` by `betaG_eq_betaIntegral`). Since `B = P/(1 − ζ₅)` with `1 − ζ₅ ∈ ℚ̄ˣ`, the family over `a, b, c ∈ ℚ̄ˣ` is exactly cor:A2's family for `P` (rescaled `b`, `c`; checked to 10⁻¹²⁰). `a = b = c = 1` is the paper's intro example (l. 105–106) |
| 15 | NIT | `CorA2.lean:149` | `hP0` in `corA2_beta5` appears unused |
| 16 | MINOR (docs) | TRUST.md / README | TRUST.md l. 161 still says "✗" for the `K`-forms and Cor. A2, and that Cor. A2 "needs an abelian-variety version of Theorem SMG". That is wrong: the formalised route is the paper's MG-A route. TRUST.md l. 202 and README l. 69 list them as missing. There are no rows for `Thm11KappaAK`, `Thm11KappaAnK` (models table) or `NotLtildeA` (named inputs). The Lemma U list (l. 89–95) omits `gmAK` and `gmAnK`. There is no "parameter `LA`/`LAn`" paragraph for the `K`-forms like the one for X7 |
| 17 | TRUST NOTE | residual | Two items remain trusted. (i) W88 §5d (trust point T) for `G_m^{2n} × A^r` and `G_m^{2n} × Q''`, in the same regimes as `gmA`/`gmAn`. The uniform `sub` makes the hypothesis a *different* `Prop` from `Thm11KappaA`/`Thm11KappaAn`; neither implies the other formally, but both are sound. (ii) The soundness facts (S1), (P), (F1)–(F4) and the instance numerics of REFEREE_HYP_A/AN |

## Details

### 1–4. Soundness of `gmAK`, `gmAnK` [Proved, given (S1), (P), (F1)–(F4) and the instance numerics]

`gmF2 θ alg lamS perS 0 λ d₂` has:
* `d₁ = 2·card ι = 2n`, `d₂` as passed (`gr`, resp. `gr + 1`), `alg = algF alg`;
* `lam = span_ℚ lamS`, `per = span_ℚ perS`;
* `sub S :⇔ S = ⊥ ∨ ∃ x ∈ S, algF alg x ∧ Ψ'' x ≠ 0`, with `Ψ'' = (θᵀx, θᵀy + λ(q))` (`Frame2.lean:33–51`).

Soundness of `sub` means: every connected `ℚ̄`-subgroup `H` has `T_H ∈ sub`. Since `T_H` is spanned by algebraic vectors,
this is equivalent to "no nonzero connected `H` has `T_H ⊂ ker Ψ''`", i.e. the maximality of the paper's `U`
(REFEREE_HYP_MGK #4).
* **`G_m^{2n} × A^r`.** By (P), `H = T_L × B_S`, and `T_H ⊂ ker Ψ''` forces each summand into `ker Ψ''`.
  - A rational `(l₁, l₂)` with `θᵀl₁ = θᵀl₂ = 0` is 0 (`hb.indep`).
  - `λ|_{T(B_S)} = 0` forces `Σ_j b_j m_j = 0` for all `m ∈ S` (the `s₀`-block of `T(B_S)` is `σ_{s₀}(S) ⊗ ℂ`). By
    `F`-independence of `b`, `S = 0`.
  
  The product-form `sub` of `gmF` and the uniform one are both supersets of the true family. Neither contains the other
  as a set: a product `0 × ℂq` with `λ(q) ≠ 0` and `q` transcendental is in the first only. Soundness needs only the
  superset property, so the switch is harmless. (It also lets the conclusion be met by non-product subspaces, which
  only weakens the hypothesis.)
* **`G_m^{2n} × Q''`.** Every nonzero connected subgroup of `Q''` contains the fibre `G_a` (REFEREE_HYP_AN #3, via
  F3/F4 and `F`-independence of `b`). So `qv (0, 1)` is an algebraic tangent vector with `Ψ'' = (0, 1)`.
* **The added logarithms.**
  - **`LA`.** `lamAK` = toric logarithms ∪ `{qv (twistA j e v) : v ∈ insert P LA}`, with `twistA j e v` =
    `ζ^{κ_s e}v_s` in copy `j`. For `v = P` these are the period generators (example 2). For `v = (z_s(u))_s`,
    `u ∈ Λ(A)`, `[ζ^e]` is an endomorphism defined over `ℚ̄`. So `[ζ^e]u ∈ Λ(A)`, with `z_s([ζ^e]u) = ζ^{κ_s e}z_s(u)`
    (the pull-back convention verified numerically for `γ` in REFEREE_HYP_A).
  - **`LAn`.** For `ũ ∈ Λ(A^♮)` with `v = z(π(ũ))` and `w = w_σ̄(ũ)`: `[ζ^e]ũ` in copy `j` maps to `Q''` with base
    `twistA j e v` and fibre `f = Σ_{j′} b_{j′} w_{j′} = b_j ζ^{(N−1)e} w` (REFEREE_HYP_AN #2). This is `twistAn`.
* **What the parameters must satisfy (#5).**
  - The tuples must be in the coordinates of `P` (`P̄`). An entry `a·(z_s(u))_s` with `a ∈ ℚ̄ ∖ ℚ` is not in `Λ(A)` in
    general, since only `[m]u` (`m ∈ O_F`, coordinates `σ_s(m)z_s(u)`) is.
  - For `LAn`, an incoherent pair `(z(u), w(ũ′))` with `π(ũ′) ≠ u` is not a logarithm. This includes `ũ′` over `u` plus
    a period, since then the pair differs from a logarithm by `(z(γ′), 0)`, which is not a logarithm of `Q''`.
  - Lean cannot express any of this, because there are no abelian logarithms. The docstrings state the intended
    reading, and the theorem is vacuous for bad parameters.
  - Fix: add to TRUST.md §8 a paragraph like the X7 "parameter `LA`" one: "`mgA_K` (`mgAn_K`) is proved for every `LA`
    (`LAn`). The intended instantiation is `LA_A = {(z_s(u))_s : u ∈ Λ(A)}` (resp. the coherent pairs
    `{(z(π ũ), w_σ̄(ũ)) : ũ ∈ Λ(A^♮)}`) in the coordinates of `P` (`(P, P̄)`). For other sets the hypothesis can be false."

### 8–10. Statement fidelity of the `K`-forms [Proved by Lean; reading checked]

* **`mgA_K`.** The premises are `hW`, `2g ≤ φ(N)`, `κ s₀ = 1`, `P_{s₀}/π ∉ ℚ̄`, an adapted `b`, `c ∈ K ∖ 0`, `i ∈ K`.
  The conclusion is that there are no `x₀, x₁ ∈ KLog K` with `s·x_k ∈ KLog K + KSlotA` and `2πi, x₀, x₁` `K`-independent,
  where `s = cP_{s₀}/π`.
  - **`S_K` is a `K`-space.** `KLog K` and `KSlotA` are closed under `K`-combinations, by concatenating the finite sums.
  - **`2πi ∈ S_K`.** `2πi ∈ KLog` (`e^{2πi} = 1`), and `s·2πi = 2ic·P_{s₀}` with `2ic ∈ K` and `P_{s₀} ∈ KSlotA` by
    `insert`.
  - So the conclusion is `dim_K S_K ≤ 2`, the paper's statement, for `LA = LA_A`.
  - **The data lifts.** `aLiftA` lifts `θ_h·Σβ_k v_k(s₀)` by `Σ_p coordsD(θ_hβ_k)_p · [ζ^{p.2}]v_k` in copy `p.1`. Its
    `λ` is `Σ_p coords_p θ_p v(s₀) = θ_hβ_k v(s₀)` (`lam_twistA` with `κ s₀ = 1`). This is right.
* **`mgAn_K`.** The structure is the same, with `KFibA` and fibre exponent `(N − 1)p.2`. `zetaN_pow_sq` makes the fibre
  value `θ_{(j,e)}w`.
* **Range of `K` (#9).** The paper's theorems quantify over number fields `K ⊇ F^c(i, c)`. Lean's do the same for
  `F = ℚ(ζ_N)`. `ζ ∈ K` is automatic: `ζ·θ(j, e) = θ(j, e+1)`, and `ζ^{φ(N)}b_j` is a `ℚ`-combination of the
  `θ(j, e)`. So the Lean `K`-forms are not a "post-reduction case" (unlike `Gen.mg_K`, where [I]'s Theorem MG quantifies
  over all `K ⊇ k`).
* **What is not covered.** CM fields other than cyclotomic `ℚ(ζ_N)`, the reduction to the simple, primitive case, and
  `g = 1` in MG♮-A (that is [I]). The slot restriction `κ s₀ = 1` (identity slot) and the second-kind slot `ζ ↦ ζ^{N−1}`
  are WLOG by relabelling the CM action, since `κ` is a free parameter.

### 11–14. Cor. A2 [Proved by Lean; inputs checked]

* **Proof route.** As in #11, this is the paper's proof (l. 558–565) with the case split organised by `(a₀, a₁, a₂)`
  rather than by `(a₁, b₁)`. The uses of (W) are: `P/π ∉ ℚ̄`, `P ∉ ℚ̄` and `a′P ∈ ℚ̄𝓛 ⇒ a′ = 0`. `NotLtildeA` packages the
  last two, and in fact implies the first (#13).
* **`NotLtildeA` (#12).** True as stated for every nonzero period `z_σ(γ)` of a simple abelian variety over `ℚ̄`, of
  either kind (for the second kind, use `A^♮`, F3). In particular it is true for `(1 − ζ₅)B(1/5,1/5)`. Wüstholz on
  `G_a × G_m^m × A` is the right citation, and it is the paper's (W) as derived at l. 364. Note that `ℚ̄ + ℚ̄𝓛` is
  slightly more than the paper's separate statements "`∉ ℚ̄`" and "`∉ ℚ̄𝓛`", but it follows from the same theorem.
* **`corA2_beta5`.** `hB : B = perA5 0/(1 − ζ₅)` is the `ThmA` identity, and the exponents are rewritten with
  `b/(1 − ζ₅)` and `c(1 − ζ₅)`, both in `ℚ̄ˣ`. The statement is about Mathlib's `betaIntegral (1/5) (1/5)`, which is the
  real Beta value 9.5015013898843674150….

## Suggested fixes

1. TRUST.md §8 (#16).
   * Replace row l. 161 by rows for `AbVar.mgA_K`, `AbVar.mgAn_K` (generic, every `K ⊇ ℚ(ζ_N)(i, c)`), `AbVar.corA2`
     and `AbVar.corA2_beta5`.
   * Add `Thm11KappaAK`/`Thm11KappaAnK` to the models table (uniform `sub`; cite this report).
   * Add `NotLtildeA (perA5 0)` to the named inputs ("Wüstholz on `G_a × G_m^m × A`; implies `WuestholzA5`").
   * Add the `LA`/`LAn` paragraph (#5).
   * Add `gmAK` and `gmAnK` to the Lemma U list (#7).
   * Update l. 202 and README l. 69.
2. `CorA2.lean`: drop `hT` from `corA2` and `WuestholzA5` from `corA2_beta5`, deriving it from `hNot` (#13, two lines,
   as in `axAK.lean`). Remove the unused `hP0` (l. 149).
3. `MGAK.lean:17–18`: replace "the paper's reduction from arbitrary `K` uses Baker's theorem and is not formalised" by
   "this is the paper's range of `K` (`K ⊇ F^c(i, c)`, `F = ℚ(ζ_N)`); Baker is used only when applying the theorem to
   `ℚ`-independent logarithms" (#9).

## Falsification attempts (none succeeded)

* **A connected subgroup in `ker Ψ''`.** Excluded for both groups (#2, #3). A diagonal between a torus and `A^r` (or
  `Q''`) would need a common subquotient, and there is none.
* **A non-logarithm in `lam`.** None for genuine `LA`/`LAn`. Bad parameter sets give non-logarithms, but no theorem
  instantiates them (#5).
* **A wrong slot for the lifts.** `lam_twistA` reads `b_j ζ^{κ s₀·e}v(s₀)`, and with `κ s₀ = 1` that is `θ(j, e)v(s₀)`.
  `aLiftAn` uses exponent `(N − 1)e`, which gives `θ(j, e)w` by `(N − 1)² ≡ 1`.
* **Inflated `κ`, undercounted `d₂`.** `per`, `d₂` are identical to `gmA`/`gmAn` (`rfl`).
* **A hidden premise in Cor. A2.** `#check` shows only `hW` (with `LA = ∅`), `WuestholzA5` (redundant) and `NotLtildeA`.
* **`NotLtildeA` false?** Proof sketch in #12. The PSLQ check is consistent with it.
* **A mis-stated Beta corollary.** The exponents and rescalings were checked to 10⁻¹²⁰, and `betaIntegral` is the
  intended `B`.

## Verdict lines

* Item 1 (`gmAK`, `gmAnK`, `Thm11KappaAK`, `Thm11KappaAnK`, `mgA_K`, `mgAn_K`): **CORRECT WITH NOTES**.
  - The models are sound for genuine `LA` (full tuples in the coordinates of `P`) and `LAn` (coherent base/fibre pairs
    of one `ũ ∈ Λ(A^♮)`, in the coordinates of `(P, P̄)`), and for `∅`.
  - The switch to the uniform `sub` is sound for both groups.
  - The statements are exactly thm:MGA and thm:MGnA for `F = ℚ(ζ_N)` and every `K ⊇ F(i, c)`.
  - Notes: the parameter conditions are docstring-only (MINOR, latent); the generic-parameter caveat is inherited; the
    "Baker reduction not formalised" docstring is over-conservative.
* Item 2 (`corA2`, `corA2_beta5`, `NotLtildeA`): **CORRECT WITH NOTES**.
  - The proof route is the paper's.
  - `NotLtildeA` is true (Wüstholz on `G_a × G_m^m × A`), including at `(1 − ζ₅)B(1/5,1/5)`.
  - The `corA2_beta5` statement is right (`aπ²`, `bπB`, `cπ²/B`, `B = betaIntegral (1/5) (1/5)`).
  - Notes: `hT`/`WuestholzA5` is redundant given `NotLtildeA`; TRUST.md and README are stale.
* Overall: **CORRECT WITH NOTES**. No FATAL or MAJOR issue. Residual trust is W88 §5d (trust point T) for the two
  groups, and Wüstholz 1989 for `NotLtildeA`.
