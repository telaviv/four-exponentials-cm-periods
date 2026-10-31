# Referee report: `CM4E/AbVar/ThmA.lean` (Theorem MG-A, the model `gmA`, the Beta instances)

Referee: adversarial AI reviewer (Claude), 2026-10-31.

**Scope (commit 5d35b5a).**
* Read in full: `CM4E/AbVar/ThmA.lean`, `CM4E/AbVar/Basis.lean`, `CM4E/Gen/Frame.lean`, `CM4E/Waldschmidt.lean`,
  `CM4E/Defs.lean`.
* Read for context: `CM4E/AbVar/X7.lean` (docstring, `perT`, `gmX7`); `CM4E/AbVar/Fermat7.lean` (`zeta7`, `betaG`, `perA`);
  TRUST.md (Theorem A row).
* Paper [II] (`schanuel/five_exp/paper2/paper2.tex`): abstract (l. 37–56); thm:A and its examples (l. 84–98);
  §`sec:setting` with (S1), (P), (Ch), (W) (l. 309–367); Lemma K′; thm:MGA and its proof (l. 423–463); thm:MGnA (l. 473–509);
  the proof of thm:A (l. 511–538).
* Baseline: `REFEREE_HYP_GEN.md` (the frame `gmF` and `frame_false`; Lemma U range analysis) and REFEREE_HYP_X7 (the model
  of `A = Jac(y⁷ = x(1 − x))`).

**Process.** I edited no Lean file and ran no git command. My scratch files are in `reviews/checks/hypa/`:
* `axA.lean` / `axA.out`: axiom audit, and `#check` of `two_three_beta5` and `Thm11KappaA`. The olean of `ThmA` is newer
  than its source (00:58:18 vs 00:57:19). Every theorem of the file depends only on `propext`, `Classical.choice`,
  `Quot.sound`: `fourExpAt_A`, `fourExpAt_beta5`, `fourExpAt_beta7`, `two_three_beta5`, `fourExpAt_pi_div_beta5`,
  `fourExpAt_inv` [Proved by Lean].
* `check_a.py` / `check_a.out` (mpmath, 60 digits): periods by integration on the curves, the `[ζ]`-action, CM types,
  simplicity, real rank of the period lattice, and side identities. Runtime 13 s.

## Verdict: CORRECT WITH NOTES (no soundness or fidelity defect; cosmetic and scope notes)

* `gmA N g κ P s₀ b` is a sound W88 model of `G_m^{2n} × A^r` for both instances and every `F`-basis `b`, so
  `Thm11KappaA` for the two instances follows from W88 §5d (the project's reading), and is not false.
* The instances are right: for `y⁵ = x(1 − x)` and `y⁷ = x(1 − x)` the `P s` are the integrals of `dx/y^{N−s−1}` over one
  closed cycle `γ`, to 10⁻⁶⁰, and `[ζ^e]γ` has coordinates `ζ^{(s+1)e} P s`. The Jacobians are simple with CM by `ℚ(ζ_N)`
  of type `{1, 2}` resp. `{1, 2, 3}`, and slot `0` is the identity embedding (`κ = 1`).
* `WuestholzA5`, `WuestholzA7` are true (Wüstholz's analytic subgroup theorem, the paper's own derivation of (W)).
* The statements are exactly the direct family `t ∈ ℚ̄^× P/π` of Theorem A for `P = B(1/5,1/5)` and `B(1/7,1/7)`, plus the
  inverted family `ℚ̄^× π/B(1/5,1/5)`. The paper's headline example `t = Γ(1/5)²/Γ(2/5)` is **not** covered (it is in the
  `cP` family, which the paper gets from MG♮-A).

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `gmA`: `lam`, `per`, `alg`, `d₁`, `d₂` | sound for `G_m^{2n} × A^r`: periods `[ζ^e]γ` lie in `Ker exp`, coordinates are dual to `ℚ`-rational differentials, `d₁ = 2n`, `d₂ = gr = dim A^r` |
| 2 | OK | `gmF` product-form `sub` on `G_m^{2n} × A^r` | every nonzero abelian subvariety `B_S ⊂ A^r` has `λ ≢ 0` on `T(B_S)`: its `s₀`-block is `σ_{s₀}(S) ⊗ ℂ` and `b` is `F`-independent |
| 3 | OK | `d₂ = gr < n` | `2g = φ(N)` in both instances (in fact forced for any genuine `A`), so `d₂ = gr = n/2`, the paper's `dim A″`; Lean uses only `g < φ(N)` |
| 4 | OK | `Thm11KappaA` quantifier | soundness holds for every `b` with `θ` ℚ-independent; no condition on `b` beyond `F`-independence enters `sub` |
| 5 | NOTE | generic `fourExpAt_A` | `Thm11KappaA N g κ P s₀` is a W88 instance only when `(N, g, κ, P)` come from a real `A` (the docstring says "per instance"). For arbitrary `P` it can be false, making the generic theorem vacuous; only the instances carry content |
| 6 | OK (verified) | `perA5`, `perT`, `κ s = s + 1`, `s₀ = 0` | integrals on the curve over one dumbbell cycle match `(1 − ζ^m)B(m/N, m/N)` to < 6·10⁻⁶⁰; `[ζ^e]γ` gives `ζ^{me}P` for all `e < N` |
| 7 | OK (verified) | CM type, simplicity | holomorphic forms `dx/y^k`, `k = (N+1)/2 … N−1`; `[ζ]^*` eigencharacters `{1,2}`, `{1,2,3}` = Koblitz–Ogus `Φ_{1,1}`; stabiliser trivial, so primitive, so `A` simple with `End⁰ = ℚ(ζ_N)` |
| 8 | OK | `WuestholzA5`, `WuestholzA7` | `P/π ∉ ℚ̄` from the analytic subgroup theorem on `G_m × A` (paper l. 365–367); true as stated (`P ≠ 0` is included) |
| 9 | OK | `fourExpAt_A`, `fourExpAt_beta5/7`, `fourExpAt_pi_div_beta5`, `two_three_beta5` | match thm:A (direct family `cP/π`, and for β(1/5,1/5) the inverted `cπ/P`) with any fixed logarithms; `FourExpAt` is the right notion |
| 10 | OK | `fourExpAt_inv` | correct; this is the paper's `t ↔ 1/t` argument (l. 523–525) |
| 11 | NOTE (scope) | paper examples | Lean covers `Γ(1/5)²/(πΓ(2/5))` explicitly, and `Γ(4/5)²/Γ(3/5) = (sin(2π/5)/sin²(π/5))·π/B(1/5,1/5)` only implicitly. Not covered: `Γ(1/5)²/Γ(2/5)` (abstract, l. 44, and l. 96) and `Γ(1/7)²/Γ(2/7)` (MG♮-A, inverted). Also not covered: Cor. A2 and MG-A for other `F`, other slots, or second-kind `P` |
| 12 | NOTE | dependent case | Lean needs no "`t·2πi ∉ ℚ̄𝓛`" input (paper l. 518–521): `frame_false` needs only `Y₁, Y₂` ℚ-independent, and a larger κ only helps (5.4). Legitimate under the project's reading of §5d |
| 13 | COSMETIC | docstring, `ThmA.lean:30` | names `two_three_A5`; the theorem is `two_three_beta5` |
| 14 | COSMETIC | docstring, `ThmA.lean:19, 22–23, 92` | "here `g ≤ d/2`": for a CM abelian variety with CM by `F`, `2g = d` exactly. "`fourExpAt_inv` then gives `FourExpAt (cπ/P_{s₀})`": instantiated only for β(1/5,1/5) (no `fourExpAt_pi_div_beta7`, no generic `fourExpAt_A_inv`) |
| 15 | COSMETIC | TRUST.md / README / Defs.lean | TRUST.md l. 159 still says "Theorem A … ✗ not formalised". There are no rows for `Thm11KappaA`/`gmA` soundness, `WuestholzA5/A7` or the five theorems. The Defs.lean docstring (l. 21–23) is out of date (pre-existing) |
| 16 | TRUST NOTE | residual | W88 §5d (trust point T: `W ≠ 0`, `κ > 0`) for `G_m^{2n} × A^r` with `A` a simple CM abelian variety of dimension 2 or 3. This is the same regime as `gmF`/`gmMG` with `d₂ = n/2`, and the Lemma U range holds except in trivially-true instances (#4 detail) |

## Details

### 1–4. Soundness of `gmA` [Proved, given (S1), (P)]

`gmA N g κ P s₀ b = gmF (algA g) (perAgen N g κ P) (dotL (thetaA g s₀ b))` on `TF (Fin r × Fin φ(N)) (Fin g × Fin r → ℂ)`.
So `G₂ = A^r` with coordinates `q(s, j)`: copy `j`, eigen-coordinate `s`.

* **Coordinates and `alg`.** For `A = Jac(C)`, `C : y^N = x(1 − x)` over `ℚ`, the eigen-coordinates `z_s = ∫ dx/y^{N−s−1}`
  are dual to invariant differentials defined over `ℚ`, so they are `ℚ̄`-rational, and `algA` (all coordinates algebraic)
  is the `ℚ̄`-structure of `T(A^r)`. The `P s` are these integrals over `γ` with no transcendental normalisation (#6).
  Algebraic rescalings per `s` would also be harmless.
* **`per`.** The generators are `[ζ^e]γ` in copy `j`, with coordinates `ζ^{κ s · e} P s` (#6). They are periods of `A^r`, so
  `per ⊂ ℚ ⊗ Ker exp`. They span `H₁(A^r, ℚ)`, because `H₁(A, ℚ) = Fγ` for any `γ ≠ 0`. The real rank of the
  `[ζ^e]γ`, `e < N`, is `2g` (singular values in `check_a.out`), so `per` is the full `ℚ ⊗ Ker exp`.
* **`lam`.** Toric single-slot logarithms and the periods. All are in `Λ(G″)`, and the ℚ-span is fine (REFEREE_HYP_GEN #2).
* **`d₁`, `d₂`.** `A^r` has no `G_a` or `G_m` quotient, so `d₀ = 0`, `d₁ = 2n` is maximal, and `d₂ = gr = dim A^r`.
* **`sub` (product form and λ).** By (P), connected subgroups of `G_m^{2n} × A^r` are `T_L × B`. By (S1), with `A` simple
  and `End⁰(A) = F` (#7), abelian subvarieties of `A^r` are the `B_S`, `S ⊂ F^r` an `F`-subspace. `T(B_S)` is the
  ℂ-span of the period vectors of `Sγ`, which is `⊕_s P_s·σ_s(S) ⊗ ℂ` (the `σ_s` are distinct, so the blocks separate; this
  is the paper's (Ch)). Its `s₀`-block is `σ_{s₀}(S) ⊗ ℂ = S ⊗_F ℂ` since `σ_{s₀} = id` (`κ s₀ = 1`). On it,
  `λ = Σ_j b_j q(s₀, j)` vanishes iff `Σ_j b_j m_j = 0` for all `m ∈ S`.
  - `b` is `F`-independent: if `Σ_j m_j b_j = 0` with `m_j = Σ_{e<φ(N)} q_{je}ζ^e`, then `Σ q_{je} θ(j, e) = 0`, so `q = 0`
    by `hb.indep`.
  - So `λ ≢ 0` on `T(B_S)` for `S ≠ 0`, and the `gmF` family `T_L × h`, with `h = ⊥` or `λ ≠ 0` on `h`, contains every
    connected subgroup.
  - (The argument would work for any `σ_{s₀}`; `κ s₀ = 1` is needed only for the period lifts, `hpv`.)
* **Relation to the paper's `A″`.** The `ℤ[ζ]`-matrix `m ↦ (Σ_e ζ^e m_{(j,e)})_j` gives a surjection `A^n → A^r`. Its
  kernel has identity component `B_{ker ψ_σ}`, because `ψ_σ(m) = Σ_j b_j Σ_e ζ^e m_{(j,e)}` and `b` is `F`-independent. So
  `A″ = A^n/B_{ker ψ_σ}` is isogenous to `A^r`, and `λ` pulls back to `θᵀz_σ`. Lean's model is self-contained anyway:
  it is a sound model of the honest group `G_m^{2n} × A^r`, so nothing depends on the identification.
* **`d₂ = gr < n` (#3).** A CM abelian variety with CM by `F` has `[F : ℚ] = 2g`, since `F` acts faithfully on
  `H₁(A, ℚ) ≅ ℚ^{2g}` and CM means degree `2g`. So `2g = φ(N)` in every genuine instance (`5: 2·2 = 4`, `7: 2·3 = 6`), and
  `d₂ = gr = φ(N)r/2 = n/2`. This is exactly the paper's `dim A″ = n/2` (l. 442), not undercounted. `hfin` needs only
  `g < φ(N)`, which `hg` gives.
* **(5.4) count.** `frame_false` gives `m = 3n`, `κ ≥ n` and `d − 1 − t ∈ {0, 1}`. (5.4) is then `3n > 2n + 2gr − κ`,
  which follows from `gr < n`. The margin is `n`, matching the paper's minimum margin `n`.
* **Lemma U range (`2N ≥ d₁ + κ`, `N = d − 1`, `d = 2n + gr`).** The condition is `κ ≤ 2n + 2gr − 2`, and `κ ≤ dim(V ∩ Ω_ℚ)`
  is at most `2n + 2gr − 1`.
  - At equality, `V ∩ Ω_ℚ` meets `2πiℚ^{2n}` in dimension `≥ 2n − 1 ≥ 1`, so `V` contains a rational toric line and the
    conclusion holds without W88 (as in REFEREE_HYP_GEN #11).
  - In the application, `κ = n` and `5n − 2 ≥ 3n`, which is the paper's (NR) line.
* **Quantifier (#4).** `sub` depends on `b` only through `F`-independence, and nothing else in the model depends on `b`.
  So `HyperplaneKappa (gmA … b)` follows from W88 for every adapted `b` and every `r ≥ 1`. (`r = 0` is excluded by
  `one_mem`.)
* **Generic theorem (#5).** `Thm11KappaA` is a `Prop` about arbitrary `(N, g, κ, P, s₀)`. It is a W88 consequence only
  when these come from a simple CM `A` with those eigen-periods. For example, with random `P` the "periods" are not
  periods, and the hypothesis may be false. This is the usual per-instance soundness, and the docstring (l. 25) says so.
  The two instances are sound by #6–#7.

### 6–7. The instances [Numerical] + [Proved]

All of this is in `check_a.out`.

* **Holomorphic forms.** On `y^N = x(1 − x)` (`N` odd), `dx/y^k` has order `N − 1 − k` at `x = 0, 1` and `2k − N − 1` at
  `∞`. So the holomorphic ones are exactly `k = (N+1)/2, …, N−1`, which is `g = (N−1)/2` forms, matching Riemann–Hurwitz.
  Write `m = N − k`. Then `[ζ]^*(dx/y^k) = ζ^{−k} dx/y^k = ζ^m dx/y^k`, so the coordinate `z_m` transforms by `ζ^m`, and
  `κ(s) = m = s + 1`.
* **One cycle.** `γ` is the dumbbell loop: start at `x = 1/2` on the sheet `y = ρ(x) > 0`, go around `1` counterclockwise
  (radius ¼), return along `[¼, ¾]` on the sheet `ζρ`, go around `0` clockwise, and close up.
  - `y` was continued by nearest-root tracking: 3000 steps per piece, with an assertion that the nearest root is
    unambiguous. The loop closes exactly.
  - Integrating `dx/y^{N−m}` with the tracked branch (jumps of the principal branch located by bisection) gives
    `(1 − ζ^m)B(m/N, m/N)` to < 2·10⁻⁶⁰ for `N = 5`, `m = 1, 2` and `N = 7`, `m = 1, 2, 3`, simultaneously on the same `γ`.
  - So `perA5 s` and `perT s` are `z_s(γ)` for one `γ`.
* **The action.** The integrals over `[ζ^e]γ` (sheet shifted by `ζ^e`) equal `ζ^{me}P_s` for every `e = 1, …, N−1`, to
  < 6·10⁻⁶⁰. This is the `perAgen` formula `ζ^{κ s·e} P s`.
* **CM type and simplicity.** The eigencharacters on holomorphic forms are `Φ = {1, 2}` (`N = 5`) and `{1, 2, 3}` (`N = 7`),
  with `Φ ⊔ −Φ = (ℤ/N)^×`. They agree with the Koblitz–Ogus label `Φ_{1,1}` of `B(1/N, 1/N)`.
  - The stabiliser `{a : aΦ = Φ}` is trivial in both cases, so `Φ` is primitive, and `A` is simple with `End⁰(A) = ℚ(ζ_N)`
    (Shimura).
  - For `N = 7` this is the point to check: the type is not the induced type `{1, 2, 4}` from `ℚ(√−7)`, which would give
    `E³` (the Klein-quartic situation).
* **Slot `s₀ = 0`.** This is `m = 1`, the form `dx/y^{N−1}`, with character `ζ ↦ ζ`: the identity embedding of
  `ℚ(ζ_N) ⊂ ℂ` (with `ζ = e^{2πi/N}`, the same as `zetaN`, `zeta7`). The conjugate `ζ ↦ ζ^{−1}` is not in `Φ`. So
  `κ s₀ = 1` is right, and `P s₀ = (1 − ζ)B(1/N, 1/N)` is a first-kind period.
* **Side checks.**
  - `B(1/5,1/5) = Γ(1/5)²/Γ(2/5)` and `B(1/7,1/7) = Γ(1/7)²/Γ(2/7)` to 10⁻⁶⁰.
  - `P_1·P_{N−1}/π = 4 sin(2π/N)/(1 − 2/N)`, Riemann bilinear, to 10⁻⁶⁰.
  - `Γ(4/5)²/Γ(3/5) · B(1/5,1/5)/π = sin(2π/5)/sin²(π/5)` to 10⁻⁶⁰.
  - `findpoly(B(1/N,1/N)/π, 8, 10⁶)` finds no relation (as expected).

### 8. `WuestholzA5`, `WuestholzA7` [Lit + Proved derivation]

Suppose `P_{s₀}/π = a ∈ ℚ̄`. Put `u = (2πi, γ) ∈ Lie(G_m × A)`; then `exp u = 0 ∈ (G_m × A)(ℚ̄)`. Also `u` lies in the
`ℚ̄`-hyperplane `z_{s₀} = (a/2i)·x`.

By Wüstholz's analytic subgroup theorem there is a connected algebraic subgroup `H` with `u ∈ Lie(H) ⊂` that hyperplane.
By (P), `H = T × B`:
* `T = G_m`, since the toric component `2πi ≠ 0`;
* `B ⊇` the smallest abelian subvariety with `γ ∈ Lie(B)`, which is `A`, since `γ ≠ 0` and `A` is simple.

So `Lie(H)` is everything, which is not inside a hyperplane: a contradiction.

`Transcendental ℚ (P/π)` also excludes `P = 0`, and `P ≠ 0` holds (numerically, and because `γ ≠ 0`). So both named
inputs are true as stated. They are equivalent to `B(1/N, 1/N)/π ∉ ℚ̄`, since `1 − ζ ∈ ℚ̄^×`.

### 9–12. Statement fidelity [Proved, reading checked]

* **`FourExpAt t`** (Defs.lean:43): for all ℚ-independent `a, b ∈ 𝓛`, `e^{ta}` and `e^{tb}` are not both algebraic. This is
  Theorem A's statement with arbitrary fixed logarithms (REFEREE_HYP_GEN #14).
* **`fourExpAt_A`.** `FourExpAt (c·P s₀/π)` for all algebraic `c ≠ 0`. This is thm:A's direct family `t = cP⁺/π` (via
  thm:MGA with `s = t`), for `F = ℚ(ζ_N)` and the slot `σ = id`.
  - The proof builds `K ∋ c, i` (and `K ⊇ F` automatically, since `span_ℚ θ` is closed under `ζ`), as the paper's
    `K ⊇ F^c(i, c)` requires.
  - The period lifts `qh h = Σ m_p [ζ^{e_p}]γ_{j_p}` satisfy `λ(qh h) = 2icθ_h P = s·2πiθ_h`, which is the paper's
    `w = (2πi, 2icP)`.
  - The data lifts are toric (`Y_k = s x_k ∈ 𝓛`).
* **`fourExpAt_beta5`, `fourExpAt_beta7`.** `ℚ̄^× P/π = ℚ̄^× B(1/N,1/N)/π`, since `P = (1 − ζ)B` with
  `1 − ζ ∈ ℚ̄^×` (`hB`, `hcalg`). So these are `FourExpAt (c·B(1/5,1/5)/π)` and `FourExpAt (c·B(1/7,1/7)/π)` for all
  algebraic `c ≠ 0`.
* **`fourExpAt_pi_div_beta5`.** `FourExpAt (cπ/B(1/5,1/5))`, via `fourExpAt_inv` applied to `c⁻¹B/π`. This is the inverted
  family. By the side identity it contains the paper's third example `Γ(4/5)²/Γ(3/5)`, but Lean does not state that.
* **`two_three_beta5`.** `t = B(1/5,1/5)/π = Γ(1/5)²/(πΓ(2/5))` with the principal `log 2`, `log 3`: the second of the
  paper's four examples (l. 96). `fourExpAt_beta5` gives it for every choice of logarithms.
* **Not covered (#11).**
  - `t = Γ(1/5)²/Γ(2/5) = B(1/5,1/5)` is the abstract's example (l. 44) and the first example at l. 96. It is in the `cP`
    family. The paper obtains it from MG♮-A, inverted (`π/P⁻ ∈ ℚ̄^×P⁺`; l. 536–537), and MG♮-A is not formalised. The
    same applies to `Γ(1/7)²/Γ(2/7)`.
  - Lean covers `t = Γ(1/5)²/(πΓ(2/5))` instead. Any summary must say "at `B(1/5,1/5)/π`", not "at `Γ(1/5)²/Γ(2/5)`".
  - Also not formalised: Cor. A2 (`e^{π²}`, `e^{πP}`, `e^{π²/P}`), MG-A for CM fields other than `ℚ(ζ_N)` or slots
    `σ ≠ id`, and the reduction to the simple case.
* **`fourExpAt_inv` (#10).** If `e^{t⁻¹a}, e^{t⁻¹b} ∈ ℚ̄`, then `t⁻¹a, t⁻¹b ∈ 𝓛` are ℚ-independent, and
  `e^{t·t⁻¹a} = e^a ∈ ℚ̄`. This is the paper's l. 523–525 argument, and it is correct.
* **#12 (observation).** The paper treats separately the case where `2πi, log α, log β` are ℚ-dependent, using (W) in the
  form "`t·2πi ∉ ℚ̄𝓛`". Lean does not need this.
  - `genF_linearIndependent` uses only the `y`-block, where the period lifts vanish, so rank 3n needs only `Y₁, Y₂`
    independent.
  - Extra periods in `Y` only raise κ.
  - The subgroup exclusion uses only `s ∉ ℚ̄` and `λ ≠ 0`.
  
  This is consistent with the Thm 1.1-type conclusion of `HyperplaneKappa` (the project's reading, as in gmMG/gmMGn).
  The resulting special case, that `e^{2πi s}` is transcendental, is true by (W), so nothing implausible is derived.

### 13–15. Cosmetic

* `ThmA.lean:30`: `two_three_A5` should be `two_three_beta5`.
* `ThmA.lean:19`: "here `g ≤ d/2`" should read "here `2g = d`, so `d₂ = gr = n/2`, the paper's `dim A″`". The hypothesis
  `hg : 2 * g ≤ N.totient` (l. 93) is harmless; `g < φ(N)` is what is used.
* `ThmA.lean:22–23`: the inverted family is proved only for `B(1/5,1/5)`. Either add a generic `fourExpAt_A_inv` and
  `fourExpAt_pi_div_beta7` (one line each, as in `fourExpAt_pi_div_beta5`), or reword.
* TRUST.md:159 still lists Theorem A as "✗ not formalised". It needs rows for:
  - the hypothesis `AbVar.Thm11KappaA` with the soundness of `gmA` (pointing to this report and REFEREE_HYP_X7);
  - the named inputs `WuestholzA5`, `WuestholzA7`;
  - the five theorems, with the scope note of #11.
  
  README has no `AbVar/ThmA` entry. The Defs.lean module docstring (l. 21–23, "`c ∈ ℚ(i)ˣ`") is out of date; this is
  pre-existing.

## Falsification attempts (none succeeded)

* **Wrong eigen-slot or conjugate embedding.** If slot 0 had been `ζ ↦ ζ^{−1}`, then `hpv` would give `θ̄`-type values and
  the lifts would fail. The numerics confirm `[ζ]` acts on `z_0` by `ζ¹` with `ζ = e^{2πi/N}`, the same `ζ` as `zetaN`.
* **Periods from different cycles per slot.** All `g` integrals were taken over the same tracked loop. A per-slot choice
  of path would have shown up as a mismatch of the factor `1 − ζ^m` for some `m`. None did.
* **Non-simple Jacobian** (the Klein-quartic trap for `N = 7`). The type `{1, 2, 3}` has trivial stabiliser. A non-simple
  `A` would add abelian subvarieties of `A^r` beyond the `B_S`, and some of them could lie in `ker λ`.
* **Undercounted `d₂`.** `d₂ = finrank (Fin g × Fin r → ℂ) = gr = dim A^r`, which is exact for `G₂ = A^r`.
* **Spurious κ.** `per` is exactly `ℚ ⊗ Ker exp` (toric `2πi` and `Fγ` in each copy). The period lifts are honest
  ℚ-combinations of `[ζ^e]γ` (`hqh`).
* **Missing subgroups.** Every `T_L × B_S` (over ℂ) is in `sub` (#2). Goursat holds because no subquotient of `A^r` is a
  torus.
* **Encoding traps.**
  - `perAgen` and `pv` both index copy `j = p.2` and exponent `e`. `thetaA` reads coordinate `(s₀, j)` with weight `b_j`.
  - The `Fin r × Fin φ(N)` index of `θ(j, e) = ζ^e b_j` is consistent between `thetaD`, `pv`, `hpv` and `coordsD`.
  - `betaIntegral (1/5) (1/5)` is Mathlib's complex Beta integral, and `betaG_eq_betaIntegral` (proved) identifies it with
    `Γ(1/5)²/Γ(2/5)`.
  - `#check two_three_beta5` shows only the premises `Thm11KappaA 5 2 (s ↦ s+1) perA5 0` and `WuestholzA5`.

## Verdict lines

* Item 1 (soundness of `gmA`; `gmF` product-form `sub` for `G_m^{2n} × A^r`; `d₂ = gr < n`; truth of `Thm11KappaA`):
  **CORRECT WITH NOTES**. The model is sound for every adapted `b` in both instances, and `d₂ = gr = n/2` is the paper's
  `dim A″`, using `2g = φ(N)`. The generic `Thm11KappaA` is a W88 instance only for genuine `(N, g, κ, P)` (per-instance,
  as the docstring says).
* Item 2 (instances `y⁵ = x(1 − x)`, `y⁷ = x(1 − x)`): **CORRECT** [Numerical, 60 digits, + Proved CM-type facts]. The
  `P s` are periods of one cycle with `κ s = s + 1`; the Jacobians are simple with CM by `ℚ(ζ_N)`, types `{1,2}` and
  `{1,2,3}`; and `s₀ = 0` is the identity embedding.
* Item 3 (`WuestholzA5`, `WuestholzA7`): **CORRECT**. True as stated, by the analytic subgroup theorem on `G_m × A`.
* Item 4 (statement fidelity of `fourExpAt_A`, `fourExpAt_beta5/7`, `fourExpAt_pi_div_beta5`, `two_three_beta5`;
  `fourExpAt_inv`; `FourExpAt`): **CORRECT WITH NOTES**.
  - Covered: exactly thm:A's `cP/π` family for these `P`, plus `cπ/B(1/5,1/5)`.
  - The headline example `t = Γ(1/5)²/Γ(2/5)` (`cP` family, MG♮-A) is **not** covered, and neither is `Γ(1/7)²/Γ(2/7)`.
    Lean covers `t = Γ(1/5)²/(πΓ(2/5))`.
  - Cosmetic: docstring name `two_three_A5`; the "`g ≤ d/2`" wording; the inverted family only for β(1/5,1/5); TRUST.md
    not updated.
