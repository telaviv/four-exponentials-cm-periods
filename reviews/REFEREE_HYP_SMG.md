# Referee report: Theorem S in Lean (`gmF2`, `gmSMG`, `gmSMGn`, `frame2_false`, `smg_false`, `smgn_false`, `NotLtilde`, `thmS`, `Final.thmS_*`)

Referee: adversarial AI reviewer (Claude), 2026-10-30. This report is the only project file I edited, apart from my
check script and its output in `checks/hypsmg/` (`check_smg.py`, `check_smg.out`). I ran no git command. Scratch work
(a copy of `Frame2.lean` with one hypothesis deleted) is in my session temp folder, outside the project.

Files reviewed:
* In full: `CM4E/Gen/Frame2.lean`, `CM4E/Gen/SMG.lean`, and the Theorem S section of `CM4E/Final.lean`.
* For context: `CM4E/Waldschmidt.lean`, `Gen/Frame.lean` (`TF`, `tor1/2`, `qv`, `algF`), `Gen/MG.lean`, `Gen/MGn.lean`
  (`Wpsi`, `Qm`, `lamM`, `algQm`, `perQm`, `Wphi`, `Qn`, `algQn`, `perQn`, `finrank_Q*_lt`), `Gen/Basis.lean`,
  `Gen/CMLattice.lean`, `Gen/Instances.lean`, the statement of `exists_adapted_basis`, TRUST.md, and the reviews
  REFEREE_HYP_GEN and REFEREE_HYP_MXG.
* From `schanuel/five_exp/paper2/paper2.tex`: thm:S, thm:W88 and the trust-point discussion after it, §sec:S
  (lem:notLt, thm:SMG and its proof, lem:SMGnsub, lem:N2, the proof of Theorem S), and cor:S.

Out of scope: `Gen/MG13.lean` and `Final.mg1_varpi` / `Final.mg3_varpi`. They appeared during the review (another
session) and consume `Thm11KappaSMG`. The soundness findings below for `gmSMG` apply to them, but I did not review their
proofs.

## Verdict: CORRECT (cosmetic items and one inherited trust note)

* `gmSMG L b` and `gmSMGn L b` are sound W88 models for every adapted basis θ. Sound means:
  - `lam` ⊂ Λ(G″);
  - `per` ⊂ ℚ ⊗ Ker exp (in fact equal to it);
  - every connected algebraic subgroup satisfies `sub`;
  - d₂ = dim A″, resp. dim Q″, with d₀ = 2, resp. 1, and d₁ = 2n maximal.

  The uniform subgroup condition is **true** for both groups, including the diagonal lines {(αu, βu)} in G_a × G_a^fib
  of Lemma SMGnsub.
* The §5d route is valid. Given `HyperplaneKappa`, `frame2_false` is a correct, complete argument. It uses no case table
  because the §5d conclusion puts the subgroup *inside* V″, and the uniform exclusion then forces s ∈ ℚ̄. The paper's
  Thm 4.1 case table is not needed in Lean. At the one instance Lean uses, it gives an independent derivation of the
  same contradiction.
* `NotLtilde latI` (ϖ, π/ϖ ∉ 𝓛̃) and `NotLtilde latRho` (Ω_ρ, 2π/(√3Ω_ρ) ∉ 𝓛̃) are **true**. They follow from
  Wüstholz's analytic subgroup theorem exactly as in Lemma notLt [Lit]. The final theorems are not vacuous.
* `thmS` and the two wrappers state Theorem S faithfully, for the CM fields ℚ(i) and ℚ(√−3): all four t-classes, with
  ℚ̄-independent y₁, y₂ and 𝓛̃ = ℚ̄ + ℚ̄𝓛. The reductions (t ↦ 1/t, and Legendre between 1/ω and η₀/π) are right.
* Axiom audit passes. All nine new declarations use only `propext`, `Classical.choice` and `Quot.sound`.

| # | severity | item | finding |
|---|---|---|---|
| 1 | OK | `gmSMG`: tangent space, Ψ″ | `T(G_a² × G_m^{2n} × A″) = ℂ² × ℂ^{2n} × ℂⁿ/ℂ·ker ψ`. μ = a₁ and λ = a₂ + θᵀz give Ψ″ = (a₁ + θᵀx, a₂ + θᵀy + θᵀz), which is the map induced by Φ = Ψ∘p_θ of the paper |
| 2 | OK | `gmSMG`: alg, lam, per | `algQS` is the ℚ̄-structure. `lamSS` = toric logs, algebraic G_a vectors (a, a′, 0) and A″-periods, all in Λ(G″). `perSS` = 2πi slots and A″-periods = ℚ ⊗ Ker exp |
| 3 | OK | `gmSMG`: d-values | d₀ = 2, d₁ = 2n maximal (Hom(A″, G_a) = 0, no torus in A″). d₂ = `finrank Qm` = dim A″ = n/2 exactly |
| 4 | OK | `gmSMGn`: tangent space, Ψ″ | `T(G_a × G_m^{2n} × Q″) = ℂ × ℂ^{2n} × (ℂⁿ/ℂ·ker φ × ℂ)`. μ = a and λ = fibre θᵀw give Ψ″ = (a + θᵀx, θᵀy + θᵀw), as in the paper's (b) |
| 5 | OK | `gmSMGn`: lam, per | as #2, plus fibre vectors ([0], f) with f ∈ ℚ̄. Their exponentials are the points f of the fibre G_a ⊂ Q″, which are algebraic. `perSSn` = 2πi slots and Q″-periods (`perQn`, REFEREE_HYP_GEN #5) |
| 6 | OK | `gmSMGn`: d-values | d₀ = 1 maximal (Q″ is a quotient of the anti-affine (E^♮)ⁿ, so Hom(Q″, G_a) = 0). d₁ = 2n. d₂ = `finrank Qn` = n/2 + 1 |
| 7 | OK | uniform `sub`, SMG | true. Every connected subgroup is H × T_L × B (Goursat). Ψ″ ≠ 0 on T_H (H ≠ 0, including diagonal G_a lines), on T_L (L ≠ 0, θ ℚ-independent), and on T_B (B ≠ 0, as S′ ⊋ ker ψ) |
| 8 | OK | uniform `sub`, SMG♮ | true. Lemma SMGnsub's list is complete and correct (proof checked below, including the non-splitting of Q″ over every B ≠ 0). Every nonzero member has Ψ″ ≠ 0. The diagonal line (α, ([0], β)) has Ψ″ = (α, β) ≠ 0 |
| 9 | OK | algebraic part of s·y in the fibre (Q2) | legitimate: ℚ̄ = η*(0) + ℚ̄ ⊂ 𝓕ib, and (b) has no second G_a. Same as the paper's 𝓛̃ + ℚ̄𝓕ib. Lean proves only the special case s·y ∈ 𝓛̃ of SMG/SMG♮, which is all Theorem S needs |
| 10 | OK | Lemma U range (Q3) | SMG♮: 2N = 5n + 2 ≥ 2n + 2 + κ for every κ ≤ 3n, so it **holds in every instance**. SMG: 2N = 5n + 2 ≥ 2n + 4 + κ fails only for κ ∈ {3n − 1, 3n}. Those instances contain a rational toric period line, so their conclusion holds outright. At the applications (κ = n): 5n + 2 ≥ 3n + 4 and 5n + 2 ≥ 3n + 2 |
| 11 | OK | `frame2_false` count (Q4) | m = 3n, κ ≥ n, d₁ = 2n, d − 1 − t ∈ {0, 1} (ker Ψ″ = W ⊂ V″). Then (5.4) ⟸ d₂ < n. That gives margin n for SMG and n − 2 for SMG♮, the same as the paper's types Z/F |
| 12 | COSMETIC | `frame2_false (hfin)` | unused. A copy of the file with `hfin` deleted compiles, with the same three axioms [Proved by Lean]. It is true in both instances, so nothing is lost |
| 13 | OK | final exclusion (Q4) | x algebraic ⇒ Ψ″x ∈ ℚ̄². x ∈ V″ ⇒ P₂ = sP₁. Ψ″x ≠ 0 ⇒ P₁ ≠ 0 ⇒ s ∈ ℚ̄, against s transcendental. Correct |
| 14 | TRUST NOTE | §5d route at d₀ = 2 | valid given `HyperplaneKappa`. The hypothesis is W88 Thm 1.1 + (5.4), now with d₀ = 2 (SMG) and d₀ = 1 (SMG♮; d₀ = 1 was already used by MX). The paper vouches for d₀ = 2 only for Thm 4.1 + Lemma U. Waldschmidt himself uses Thm 1.1 with d₀ = 2 (Cor. 2.1). Inherited caveat: the second application inside §5d (REFEREE_HYP_GEN #16) |
| 15 | OK | `NotLtilde` (Q5) | true for `latI` and `latRho` [Lit: Wüstholz 1989]. The paper's proof of Lemma notLt is correct (re-derived below). η₀ is the conjugate-eigen quasi-period for both lattices (verified to 60 digits) |
| 16 | OK | `thmS` reductions (Q6) | t = cω/π: SMG. t = cπ/ω: 1/t = c⁻¹ω/π, data ty. t = c/ω = c′η₀/π with c′ = c(α − ᾱ)/(2i): SMG♮. t = cω: 1/t = c″η₀/π with c″ = (α − ᾱ)/(2ic), data ty. `thmS_core` is the paper's "2πi ∈ ℚ̄y₁ + ℚ̄y₂ ⇒ P ∈ 𝓛̃" step |
| 17 | COSMETIC | scope of the wrappers | `thmS` holds for any `CMLattice`. The wrappers instantiate ℚ(i) and ℚ(√−3) only, and so cover every CM curve with those CM fields (periods in ℚ̄^×ϖ, resp. ℚ̄^×Ω_ρ). The paper states Theorem S for every CM E |
| 18 | COSMETIC | docstrings of `Frame2` / `gmF2` | "d₂ = dim G₂ − d₀" uses G₂ for the whole non-toric factor (G_a's included). In W88's notation the instance's d₂ is just dim G₂ (= dim A″, dim Q″). Correct, but confusing |
| 19 | OK | transcendence of s | `smg_false` uses Schneider (ω/π ∉ ℚ̄) and `smgn_false` uses Schneider (ω ∉ ℚ̄) plus Legendre. The paper uses Lemma notLt for (a). Both are fine |

## Details

### 1–3. `gmSMG`: OK [Proved, modulo standard facts on CM abelian varieties]

**The group.** In the paper's (a), G = G_a × G_m × G_a × G_m × E and Φ = Ψ ∘ p_θ on Gⁿ.
* Connected subgroups of Gⁿ = G_a^{2n} × G_m^{2n} × Eⁿ are products H × T_L × B_S. The reason is that vector groups,
  tori and abelian varieties have no common nonzero subquotients (Goursat).
* A product lies in ker Φ iff each factor does:
  - H ⊂ {θ·a₁ = θ·a₂ = 0};
  - L = 0, since θ is ℚ-independent;
  - S ⊂ ker ψ, since T(B_S) = ℂS and ψ is k-linear as a map to ℂ.
* So U = {θ·a₁ = θ·a₂ = 0} × 1 × B_{ker ψ}, and G″ = G_a² × G_m^{2n} × A″. The G_a² coordinates are θ·a₁ and θ·a₂.
  This quotient is ℚ̄-rational because θ is algebraic.
* The induced Ψ″ is (a₁″ + θᵀx, a₂″ + θᵀy + θᵀz). Lean's μ = a₁ and λ = a₂ + `lamM` give exactly this.

**The Lean model.**
* Tangent space and A″-part: `Qm = ℂⁿ/Wpsi`, where `Wpsi` = ℂ·{v ∈ kⁿ : Σθ_j v_j = 0} = T(B_{ker ψ}).
* ℚ̄-structure: `algQS` = (ℚ̄, ℚ̄, image of ℚ̄ⁿ).
* `lamSS`:
  - toric single-slot logarithms;
  - `qv (a, a′, 0)` with a, a′ ∈ ℚ̄, whose exponential is the algebraic point (a, a′) of G_a² (Λ(G_a) = ℚ̄);
  - the A″-periods [ωe_j], [αωe_j].

  All three lie in Λ(G″). Their ℚ-span does too, since Λ is a ℚ-space (division points of algebraic points are
  algebraic).
* `perSS`: the 2πi slots and the A″-periods. Its ℚ-span is ℚ ⊗ Ker exp. G_a has no periods.

**The d-values.**
* Hom(A″, G_a) = 0 and A″ contains no torus. So d₀ = 2 and d₁ = 2n are maximal, and d₂ = dim A″ = `finrank Qm`.
* dim_k ker ψ = n/2: ψ maps kⁿ k-linearly onto K, and dim_k K = r = n/2. So d₂ = n/2. This is exact for the three
  fields in `check_smg.out` [2] [Proved, checked exactly].
* Lean only needs d₂ < n (`finrank_Qm_lt`), and d₂ is the true dimension, not a bound.
* As noted in `Waldschmidt.lean`, a non-maximal d₀ would only enlarge d₂ and weaken the hypothesis. A non-maximal d₁ is
  not possible here.

**Uniform `sub` (#7).** Let H″ ≠ 0 be a connected subgroup of G″. It is H′ × T_L × B′.
* H′ ≠ 0 (any ℚ̄-subspace of G_a², including diagonal lines): Ψ″ = (a₁, a₂) ≠ 0 on it.
* L ≠ 0: Ψ″(l) = (θ·l₁, θ·l₂) ≠ 0.
* B′ = B_{S′}/B_{ker ψ} with S′ ⊋ ker ψ: λ = θᵀ ≠ 0 on ℂS′.

T_{H″} is ℚ̄-rational. So it contains an algebraic x with Ψ″x ≠ 0, which is exactly `sub`. The same conclusion also
follows abstractly: G″ = Gⁿ/U with U maximal, so any connected H″ with T ⊂ ker Ψ″ has a preimage inside U.

### 4–6, 8. `gmSMGn` and Lemma SMGnsub: OK [Proved, modulo the T(Q″) coordinates of REFEREE_HYP_GEN #4]

**Coordinates.**
* T(Q″) = (ℂⁿ × ℂⁿ)/T(U_Q), with U_Q = B^♮_{ker φ} + {θᵀw = 0}. The map (z, w) ↦ ([z], θᵀw) is well defined:
  - in conjugate-eigen coordinates the w-part of T(B^♮_S) is ℂS̄;
  - θᵀ(ℂ\overline{ker φ}) = 0.
* Its kernel is exactly T(U_Q) = {z ∈ ℂ·ker φ, θᵀw = 0}. So `Qn = ℂⁿ/Wphi × ℂ` is T(Q″), and ([0], f) is the fibre
  direction.
* The G_a factor is G_aⁿ/{θ·a = 0}, with coordinate θ·a. So μ = a and λ = fibre, and Ψ″ = (a + θᵀx, θᵀy + θᵀw) is what
  Φ induces.

**lam and per.**
* `qv (a, (0, f))` with a, f ∈ ℚ̄ has exponential (a, the fibre point f). It is algebraic, because the fibre
  G_a ⊂ Q″ is defined over ℚ̄ with ℚ̄-rational coordinate θᵀw.
* The periods `perQn` were checked in REFEREE_HYP_GEN #5.

**The d-values.** d₂ = n/2 + 1 (dim_k ker φ = n/2; ker φ = conj(ker ψ); exact checks in [2]). d₀ = 1 is maximal
because Q″ is anti-affine.

**Lemma SMGnsub, checked.**
* *Torus splits off.* There are no nonzero homomorphisms between subquotients of a torus and of G_a × Q″.
* *Non-splitting of Q″.* Let H ⊂ Q″ map onto B = B_{S′}/B_{ker φ} ≠ 0, and let H̃ be its preimage in (E^♮)ⁿ.
  1. H̃ ⊃ B^♮_{S′}, by the universal property. The induced map B^♮_{S′} → H̃ ⊂ (E^♮)ⁿ differs from the canonical lift
     by a homomorphism B^♮_{S′} → G_aⁿ, and that homomorphism is 0 because B^♮_{S′} is anti-affine.
  2. The fibre of B^♮_{S′} is ℂS̄′, where θᵀ ≠ 0, because S′ ⊄ ker φ.
  3. So H contains the fibre, i.e. Q″ has no splitting over any B ≠ 0.
* *Subgroups of Q″.* They are 0, the fibre, and Q″_B.
* *R ⊂ G_a × Q″ over B ≠ 0.* The image of R in Q″ is Q″_B, and R ∩ (G_a × 0) is G_a or 0. In the second case R is
  the graph of a homomorphism f: Q″_B → G_a, and f = 0:
  - if f is nonzero on the fibre, ker f splits Q″_B over B;
  - if f vanishes on the fibre, it factors through Hom(B, G_a) = 0.
* *B = 0.* R is a ℚ̄-subspace of G_a × G_a^fib: 0, a line {(αu, βu)}, or everything.

**Uniform `sub`.** Every nonzero entry of the list has Ψ″ ≠ 0 on its tangent space:
* the line (α, ([0], β)) maps to (α, β);
* Q″_B contains (0, ([0], 1)), which maps to (0, 1);
* T_L maps to (θ·l₁, θ·l₂).

The diagonal lines are the only non-product subgroups, and they are not in ker Ψ″. They could lie in V″ only if
β/α = s ∈ ℚ̄, which is precisely what the uniform exclusion rules out. This is also why the paper's types VK/VQ need no
treatment in Lean.

### 9. Fibre placement (Q2): OK

* `lamSSn` puts θ_hβ₀^Y (the algebraic part of y) in the G_a slot (μ) and θ_hβ₀^S (the algebraic part of sy) in the
  fibre slot (λ).
* The paper's group (b) has a single G_a factor feeding the first row, and the second row is y + w. So the algebraic part
  of sy has to sit in the fibre, and that is legitimate because ℚ̄ ⊂ 𝓕ib (𝓕ib contains η*(0) + ℚ̄).
* This matches 𝓛̃ + ℚ̄𝓕ib. Lean's `smgn_false` (and `smg_false`) assume s·y ∈ 𝓛̃ only, a special case of the paper's
  SMG♮ (SMG). It suffices for Theorem S.

### 10. Lemma U range (Q3): OK [Proved; `check_smg.out` [3]]

The condition is 2N ≥ d₁ + 2d₀ + κ with N = d − 1. Here dim_ℚ Ω_ℚ(G″) = 2n + n = 3n, so κ ≤ 3n.

* **SMG♮.** d = 5n/2 + 2 and 2N = 5n + 2 ≥ 2n + 2 + 3n. The condition **holds in every instance**.
* **SMG.** 2N = 5n + 2. The condition is κ ≤ 3n − 2, so it fails only for κ = 3n − 1 and κ = 3n. G_a² has no periods,
  so ℂΩ_ℚ has codimension 2 and V can contain all of Ω_ℚ.
  - For such κ, dim(V ∩ Ω_ℚ) ≥ 3n − 1 while the A″-periods have dimension n. So V meets 2πiℚ^{2n} in dimension
    ≥ 2n − 1 ≥ 1.
  - Then V contains a rational vector l ≠ 0 with Ψ″(l) ≠ 0, and the conclusion of `HyperplaneKappa` holds outright.
  - Every other instance has κ ≤ n, where 5n + 2 ≥ 3n + 4 holds.
* **Applications.** κ = n. The condition holds there: 5n + 2 ≥ 3n + 4 and 5n + 2 ≥ 3n + 2, the paper's numbers.

### 11–13. `frame2_false` (Q4): OK [Proved by Lean; reading checked]

**The count.**
* m = 3n: `hli` uses the first coordinate of Ψ″ and `hind3`, with the K-coefficients θᵀ(rational) ∈ ℚ̄.
* κ ≥ n: the n period lifts lie in `per`.
* d − 1 − t ∈ {0, 1}:
  - `wGen2` spans exactly ker Ψ″ (`wGen2_le_ker`, `ker_PsiG_le_W`, using that T spans Q);
  - it is ℚ̄-rational (uses `hμ`, `hlamA` on T);
  - it lies in V″.
* (5.4) then reads 3n > (2n + 2d₂ − κ)·{0, 1}, which follows from κ ≥ n and d₂ < n.
* The bound d₂ < n comes from `finrank_Qm_lt` (r ≥ 1) and `finrank_Qn_lt` (r ≥ 2); `exists_adapted_basis` returns
  r ≥ 2.
* This is the paper's type-Z inequality, with margin n (SMG) and n − 2 (SMG♮). For n = 2 the SMG♮ count fails, as the
  paper says.

**`hfin` (#12).** `finrank TF ≤ 2n + d₂ + 2` is never used. I compiled a copy of `Frame2.lean` with that hypothesis
line deleted (namespace renamed, in my temp folder). It has no errors, and `#print axioms` gives the same three axioms
[Proved by Lean].

**Exclusion (#13).** S ≠ ⊥ and `sub` give an algebraic x ∈ S ⊂ V″ with Ψ″x = (P₁, P₂) ≠ 0.
* P₁ and P₂ are algebraic: θ, μ(q), λ(q) are algebraic on algebraic vectors.
* x ∈ V″ means P₂ = sP₁. If P₁ = 0, then P₂ = 0, a contradiction. Otherwise s = P₂/P₁ ∈ ℚ̄, against `hs`.

**The §5d route versus Thm 4.1 (#14).**
* In Thm 4.1 the obstruction subgroup G′ need not satisfy T_{G′} ⊂ V″. Hence the paper's types F, VF, T0, VK, VQ, TK,
  with ℓ = Ψ″(T_{G′}) ≠ ℂ(1, s).
* Thm 1.1 + (5.4) puts T_{G′} inside V″. So ℓ ⊂ ℂ(1, s), and the uniform exclusion finishes. The route is logically
  valid.
* The hypothesis it needs is W88 §5d for G″ with d₀ = 2 (SMG) and d₀ = 1 (SMG♮). The paper's §sec:tool justifies
  d₀ = 2 for Thm 4.1 + Lemma U. Waldschmidt applies Thm 1.1 with d₀ = 2 himself (Cor. 2.1, κ = 0). The Lemma U range is
  checked in #10.
* The residual risk is the inherited one: the second application inside §5d (REFEREE_HYP_GEN #16, REFEREE_HYP_MXG #18).
* `frame2_false` uses `HyperplaneKappa` at one instance only (V″, W″ = ker Ψ″, the 3n lifts). At that instance the
  paper's Thm 4.1 case table independently yields the same contradiction. So the Lean theorem has a second line of
  support that does not go through §5d.

### 15. `NotLtilde` (Q5): TRUE [Lit: Wüstholz 1989; Baker–Wüstholz Ch. 6]

**ω ∉ 𝓛̃.**
1. Suppose ω = β₀ + Σβ_kℓ_k. Then u = (1, (ℓ_k), ω) ∈ Λ(G_a × G_m^N × E) lies in the ℚ̄-hyperplane
   z − β₀a − Σβ_kx_k = 0.
2. By the analytic subgroup theorem, the smallest ℚ̄-subspace containing u is T_H, and T_H lies in the hyperplane.
3. H is a product (Goursat), and its E-factor is E because ω ≠ 0. So (0, 0, 1) ∈ T_H, but (0, 0, 1) is not in the
   hyperplane.

**η₀ ∉ 𝓛̃.**
1. Take u = (1, (ℓ_k), (ω, η₀)) on G_a × G_m^N × E^♮. Here exp(ω, η₀) = 0, because η₀ = η*(ω) and the fibre coordinate
   is the ℚ̄-rational conjugate-eigen coordinate.
2. The torus splits off. The smallest R ⊂ G_a × E^♮ maps onto E.
3. Its image in E^♮ is E^♮, because E^♮ is non-split.
4. R ∩ (G_a × 0) cannot be 0. Otherwise R would be the graph of a homomorphism E^♮ → G_a, which is 0, contradicting
   the G_a-coordinate 1.
5. So R = G_a × E^♮. It contains the fibre direction, which is not in the hyperplane w − β₀a − Σβ_kx_k = 0.

**The instances.**
* `latI`: ω = ϖ and η₀ = π/ϖ, with E: y² = 4x³ − 4x.
* `latRho`: ω = Ω_ρ and η₀ = 2π/(√3Ω_ρ), with E: y² = 4x³ − 4.
* In both cases η₀ = η(ω) = π²E₂(τ)/(3ω) to 60 digits (`check_smg.out` [1]) [Numerical]. Also η(αλ) = ᾱη(λ)
  (g₃ = 0, resp. g₂ = 0), so η₀ is the conjugate-eigen quasi-period, and Lemma notLt applies verbatim.
* The hypothesis is true, so `thmS_varpi` and `thmS_omegaRho` are not vacuous through it.
* Weak sanity check [Numerical]: PSLQ finds no relation (coefficients ≤ 10³, 220-digit tolerance) between any of the
  four numbers and ℚ(√2, √3)·{1, π, log 2, log 3, log 5} (`check_smg.out` [4]). A first run at 80 digits with the
  default tolerance returned spurious 21-term relations. That was a tolerance artefact, and the script now sets
  tol = 10⁻²²⁰.

### 16–17. `thmS` and the wrappers (Q6): OK

* **Statement.** For c ∈ ℚ̄^×, t is one of cω, c/ω, cω/π, cπ/ω, and y₁, y₂ are ℚ̄-independent. The conclusion is
  ¬(y₁, y₂, ty₁, ty₂ ∈ 𝓛̃), and `Ltilde` = ℚ̄ + ℚ̄·{ℓ : e^ℓ ∈ ℚ̄}. This is the paper's Theorem S, for Ω = L.ω.
* **Wrappers.** `thmS_varpi` and `thmS_omegaRho` take Ω = ϖ and Ω_ρ. They discharge Schneider through
  `Bridge.transcendental_varpi_div_pi` and `Schneider.period_*_transcendental`, and g₂, g₃ for `latI`.
* **Reductions** (each identity is closed by `field_simp` / `linear_combination` with `L.legendre`):
  - η₀/π = 2i/(ω(α − ᾱ)), so c/ω = (c(α − ᾱ)/(2i))·η₀/π, and 1/(cω) = ((α − ᾱ)/(2ic))·η₀/π;
  - inversion replaces y by ty, which is ℚ̄-independent because t ≠ 0 (`hindt`).
* **The 2πi step.** `thmS_core` handles the case 2πi ∈ ℚ̄y₁ + ℚ̄y₂. Then s·2πi = dP ∈ 𝓛̃ with P = ω (case A,
  d = 2ic′) or P = η₀ (case B), which contradicts `NotLtilde`. Otherwise 2πi, z₁, z₂ are ℚ̄-independent and
  SMG/SMG♮ applies.
* **Scope (#17).** The wrappers cover every CM curve whose CM field is ℚ(i) or ℚ(√−3). Those curves are all isogenous,
  so their periods lie in ℚ̄^×ϖ, resp. ℚ̄^×Ω_ρ, and t-classes with c ∈ ℚ̄^× absorb this. Other CM fields need a
  `CMLattice` instance; the general `thmS` already covers them.

## Axiom audit

I ran `export PATH="$HOME/.elan/bin:$PATH"; lake env lean Axioms.lean` from the project root. It passes, and the oleans
of Frame2, SMG and Final are newer than their sources. Each of the following depends only on
`[propext, Classical.choice, Quot.sound]`:
* `Gen.frame2_false`, `Gen.smg_false`, `Gen.smgn_false`, `Gen.thmS`;
* `Final.thmS_varpi`, `Final.thmS_omegaRho`;
* all earlier declarations in the file, and the new `Gen.mg1`, `Gen.mg3`, `Final.mg1_varpi`, `Final.mg3_varpi`.

There is no `sorry`, `native_decide`, `axiom` or `admit` in Frame2.lean, SMG.lean or Final.lean.

## Recommendations (optional, none blocking)

1. Drop `hfin` from `frame2_false`, along with its two discharging goals in SMG.lean (#12).
2. In the `Frame2` / `gmF2` docstrings, say "d₂ = dim of the non-toric, non-additive factor" instead of
   "dim G₂ − d₀" (#18).
3. In the SMG.lean module docstring, add the one-line reason for SMG♮'s `sub`. Q″ does not split over any B ≠ 0 (by
   the canonical lift), so every subgroup over B ≠ 0 contains the fibre, and the diagonal lines have Ψ″ = (α, β) ≠ 0.
4. TRUST.md row for `Thm11KappaSMG(n)`: note that this is the first use of W88 §5d with d₀ = 2 (#14).
