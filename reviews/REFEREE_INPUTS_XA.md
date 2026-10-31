# Referee report: the named classical inputs of generic Theorem X (`XGen.lean`, `XThm.lean`)

Scope:
* `WuestholzXA S` (`CM4E/AbVar/XGen.lean`).
* `WuestholzSplitXA S` and `zQbar` (`CM4E/AbVar/XThm.lean`).
* The data model `CMAV` / `FKSlot` (`XGen.lean`) and `XSetup` (`XThm.lean`).
* The level-seven instance `X7S` (`CM4E/AbVar/X7Gen.lean`), compared with `WuestholzBeta7` and `WuestholzX7`
  (`CM4E/AbVar/X7.lean`).

The paper source is `schanuel/five_exp/paper2/paper2.tex`: (S1), (P), (W) (lines 346–367), the set-up of §`sec:X`
(lines 592–612) and the proof of Theorem X, "slot splitting" (lines 705–720). This report builds on
`reviews/REFEREE_INPUTS_X7.md`, which refereed the level-seven versions. The W88 hypothesis `Thm11KappaXA` is not in
scope. No project file was edited and git was not run.

Scratch files are in `reviews/checks/inputsxa/`. `check_x7.lean` holds four Lean checks against the current oleans. Run
it with `lake env lean reviews/checks/inputsxa/check_x7.lean`. It compiles with no errors or warnings; `check_x7.out`
is empty.

Labels: [Lit] = published theorem; [Proved] = derived here from [Lit] with a complete argument; [Lean] = checked by the
Lean kernel in the scratch file.

**Verdicts**
* `WuestholzXA S`: **CORRECT.** It is a special case of the paper's (W), without π and with first-kind slots only. Under
  the soundness conditions it follows from Wüstholz 1989 on `G_a × ∏_A A`. The only note concerns the docstring: it
  should say what "distinct" means (up to isogeny).
* `WuestholzSplitXA S`: **CORRECT WITH NOTES.**
  * It holds under the soundness conditions, by Wüstholz 1989 on `G_a × ∏_A A^m`. This covers ℚ̄-combinations, x or
    x′ = 0, slots on one variety, slots on isogenous varieties with non-corresponding embeddings, and logarithms that are
    periods.
  * It is no stronger than the literature gives.
  * The notes concern documentation only. The docstring states no soundness conditions, the input is false (so the
    theorem is vacuous) for a bad `LA`, and only the pairs a ≠ d and c ≠ b are used.
* Level seven [Lean]:
  * `WuestholzXA (X7S LA).slot = WuestholzBeta7` holds by `rfl`, as an equality of propositions.
  * `WuestholzSplitXA (X7S LA).slot → WuestholzX7 LA` is proved.
  * The new input is therefore at least as strong as the old one. As a Lean proposition it is stronger, since it allows
    ℚ̄-combinations. Mathematically both hold for the intended `LA`.

---

## 0. Facts used (all [Lit] or elementary)

**(AST) Wüstholz's analytic subgroup theorem** [Lit] (Wüstholz, Ann. of Math. 129 (1989) 471–500; Baker–Wüstholz,
*Logarithmic Forms and Diophantine Geometry*, CUP 2007, Thm 6.1, cited from memory as in the X7 report).
* Setting: `G/ℚ̄` is a commutative algebraic group, `W ⊂ Lie G` is a ℚ̄-subspace, and `ξ ∈ W` with `exp_G ξ ∈ G(ℚ̄)`.
* Conclusion: there is a connected algebraic subgroup `H/ℚ̄` with `ξ ∈ Lie H ⊂ W`.
* Equivalently, the smallest algebraic subgroup `G_ξ` whose Lie algebra contains `ξ` satisfies `Lie G_ξ ⊂ W` for every
  ℚ̄-subspace `W ∋ ξ`.

**(P) Products** [Proved; paper (P)]. A connected algebraic subgroup of `G_a × B` (B an abelian variety) is `L × B'`,
with `L ∈ {0, G_a}` and `B' ⊂ B` an abelian subvariety. Proof: the image `B'` in `B` is an abelian subvariety. If
`H ∩ G_a = 0`, then `H` is complete, so its projection to `G_a` is constant.

**(S1′) Subvarieties of a product of simple CM varieties** [Lit: Shimura; Poincaré reducibility]. Let `A_1, …, A_k` be
pairwise non-isogenous simple CM abelian varieties over ℚ̄, with CM fields `F_i = End⁰ A_i` and `[F_i : ℚ] = 2g_i`.
1. **Product over isogeny classes.** Every abelian subvariety `B ⊂ ∏_i A_i^{m_i}` is `∏_i B_i` with `B_i ⊂ A_i^{m_i}`.
   Write `B = Σ_i B^{(i)}`, where `B^{(i)}` is the `A_i`-isotypic part. The projection of `B^{(i)}` to `A_{i'}^{m_{i'}}`
   for `i' ≠ i` is a homomorphism between non-isogenous isotypic varieties, hence 0.
2. **Eigen-splitting on one class.** Every abelian subvariety `B ⊂ A^m` is stable under the diagonal action of `F`.
   Indeed `F` is the centre of `End⁰(A^m) = M_m(F)`, and `B` is the image of an element of `End⁰(A^m)`. So
   `T(B) = ⊕_{σ∈Φ} T(B)_σ`, where `T(B)_σ` is the part on which `F` acts by `σ`. This splitting is the component
   decomposition in the eigen-coordinates `z_σ^{(i)}`. The embeddings σ ∈ Φ are pairwise distinct characters of F.
3. **Cycles.** `H_1(A, ℚ) = F·γ` for any `γ ≠ 0`. So `z_σ(Ω(A)) ⊂ σ(F)·z_σ(γ)`, and `z_σ(γ) ≠ 0`. If `z_σ(γ)` were 0,
   then `z_σ` would vanish on `Fγ ⊗ ℝ = Lie A`. **In particular, the soundness condition `P_j ≠ 0` is automatic for
   any nonzero cycle γ_j.**

**(R) ℚ̄-structure.** The eigen-differentials `ω_σ` of a CM abelian variety over ℚ̄ are defined over ℚ̄, because all
endomorphisms are. So the eigen-coordinates `z_σ` are ℚ̄-rational linear forms on `Lie A`. A ℚ̄-isogeny `A → A'` that
intertwines the F-actions (up to an automorphism τ of F) carries `z'_{σ'}` to `λ·z_σ` with `λ ∈ ℚ̄ˣ`, where σ
corresponds to σ′ under τ.

**Soundness conditions** (from the brief, made precise by the paper, lines 592–596):
* **(C1)** Each slot `j` is `(A_j, σ_{s_j})`, with `A_j/ℚ̄` a simple CM abelian variety and `σ_{s_j} ∈ Φ_j`. The record
  `(S j).A.κ` gives the conjugates and `(S j).A.P` gives the eigen-coordinate vector of one nonzero cycle `γ_j`.
* **(C2)** The four slots are pairwise distinct **up to isogeny**: "Two slots are equal iff the abelian varieties are
  isogenous and the embeddings correspond" (paper, line 594). Slots on one variety have distinct `s`.
* **(C3)** Each `(S j).A.LA` consists of eigen-coordinate vectors `(z_0(v), …, z_{g−1}(v))` of `v ∈ Lie A_j` with
  `exp v ∈ A_j(ℚ̄)`, in the same ℚ̄-model as the one used for `P`. The normalisation may differ by a factor in ℚ̄ˣ in
  each coordinate; see §2.4.

---

## 1. `WuestholzXA S`: CORRECT

Statement: for algebraic `a₀, …, a₄`, `a₀ + a₁P_a + a₂P_b + a₃P_c + a₄P_d = 0` implies that every `aᵢ` is 0. Here
`P_j = (S j).per = (S j).A.P (S j).s`.

**Derivation** [Proved from (AST), (P), (S1′), (R)]:
1. Let `A_1, …, A_k` be the isogeny classes among `A_a, …, A_d`, each taken once. By (R), transport any slot on an
   isogenous record to the representative; this changes `P_j` by a factor in `ℚ̄ˣ·σ(F)ˣ ⊂ ℚ̄ˣ`, which does not affect
   ℚ̄-linear independence.
2. Let `G = G_a × ∏_i A_i` and `ξ = (1, γ_1, …, γ_k)`. Then `exp ξ = (1, 0, …, 0) ∈ G(ℚ̄)`.
3. Let `ℓ = a₀t + Σ_j a_j z_{s_j}^{(cls j)}`. By (C2) the five forms `t` and `z_{s_j}^{(cls j)}` are distinct members
   of a ℚ̄-basis of `(Lie G)^∨`. So `ℓ` is ℚ̄-rational, `ℓ ≠ 0` unless every `aᵢ = 0`, and `ℓ(ξ) = 0`.
4. Suppose `ℓ ≠ 0`. (AST) with `W = ker ℓ` gives `H = L × ∏_i B_i` by (P) and (S1′.1).
   * `t(ξ) = 1` forces `L = G_a`.
   * `γ_i ≠ 0` and `A_i` simple force `B_i = A_i`.

   So `Lie H = Lie G ⊄ ker ℓ`, a contradiction.

**Edge cases.**
* *Slots on one variety* (for example a, b, c on `A` at level seven): one copy of `A` suffices. Step 3 needs only that
  the `s_j` are distinct.
* *Isogenous records, non-corresponding embeddings*: covered by step 1. Without transporting, take
  `G_a × A × A′` with `A′ ~ A`. Then `G_ξ` can be the graph of an element of `Hom⁰(A, A′)`. On that graph `ℓ` becomes
  `a z_s + a′λ z_{s″}` with `s″ ≠ s`, which vanishes only for `a = a′ = 0`. Same conclusion.
* *Isogenous records, corresponding embeddings* (forbidden by (C2)): `P_d ∈ ℚ̄ˣP_a`, so the statement is **false**. This
  is why "distinct" must mean "distinct up to isogeny". The Lean `Distinct` predicate of `XSetup` covers only slots on
  one record. Distinctness across records rests on the convention that `XSetup.AV` lists each isogeny class once, and
  `XGen` states the same convention in its soundness paragraph. Neither can be checked in Lean. A violation makes the
  input false and the theorem vacuous, not wrong.
* *Non-isogenous varieties with the same CM field and a shared embedding σ* (CM types Φ ≠ Φ′ up to Aut F): these are
  distinct slots. The periods `P_{A,σ}` and `P_{A′,σ}` are ℚ̄-independent by step 4, since `Hom(A, A′) = 0`. This is
  consistent with Shimura's period symbol `p_F(σ, Φ)`, whose known relations are multiplicative in Φ.
* *`P_j ≠ 0`*: automatic by (S1′.3).

**Not stronger than the literature.** The paper's (W) asserts independence of `1`, `π` and the periods of distinct
eigen-slots of first or second kind. `WuestholzXA` drops `π` and keeps four first-kind slots, so it is a strict special
case.

**Issues:** none affecting truth.
* (Cosmetic) The docstring says "periods of pairwise distinct slots". It could add "(distinct up to isogeny: on
  non-isogenous varieties or with different embeddings; simple CM varieties; `P` the eigen-coordinates of a nonzero
  cycle)".

---

## 2. `WuestholzSplitXA S`: CORRECT WITH NOTES

Statement (clause 1). Let `x ∈ zQbar(S a)` and `x′ ∈ zQbar(S d)`, where
`zQbar(S) = {Σ_k c_k ℓ_k(s) : c_k ∈ ℚ̄, ℓ_k ∈ insert P LA}`. Let `q, c, c′ ∈ ℚ̄` with `x + x′ + q = cP_a + c′P_d`. Then
`q = 0`, `x = cP_a` and `x′ = c′P_d`. Clause 2 is the same statement for the pair `(c, b)`.

### 2.1 Derivation [Proved from (AST), (P), (S1′), (R)]

Write `x = Σ_{k≤N} c_k z_{s_a}(v_k)` and `x′ = Σ_{k≤N′} c′_k z_{s_d}(v′_k)`. By (C1) and (C3), each `v_k` is a
logarithm of a ℚ̄-point of `A_a` or the cycle `γ_a`, and each `v′_k` is one of `A_d` or `γ_d`.
1. **Group and point.** Let `G = G_a × A_a^{N+1} × A_d^{N′+1}`. If `A_a` and `A_d` are one isogeny class, transport by
   (R); then `G = G_a × A^{N+N′+2}`. Let `ξ = (1; v_1, …, v_N, γ_a; v′_1, …, v′_{N′}, γ_d)`. Every component
   exponentiates to a ℚ̄-point (periods go to 0), so `exp ξ ∈ G(ℚ̄)`.
2. **Hyperplane.** Let
   `Λ = q·t + [Σ_k c_k z_{s_a}^{(k)} − c·z_{s_a}^{(γ_a)}] + [Σ_k c′_k z_{s_d}^{(k)} − c′·z_{s_d}^{(γ_d)}] =: q·t + Λ_a + Λ_d`.
   It is ℚ̄-rational by (R), and `Λ(ξ) = x + x′ + q − cP_a − c′P_d = 0`. (If `Λ = 0`, the argument below still
   applies, with `W = Lie G`.)
3. **AST.** There is a connected `H` with `ξ ∈ Lie H ⊂ ker Λ`. By (P), `H = L × B`.
4. **`q = 0`.** `t(ξ) = 1` forces `L = G_a`. So `(1, 0) ∈ Lie H`, and `Λ(1, 0) = q = 0`. Then `Λ_a + Λ_d` vanishes on
   `Lie B`, and `ξ_ab ∈ Lie B`.
5. **Separation.**
   * *a and d on non-isogenous varieties:* `B = B_a × B_d` by (S1′.1). So `ξ_a ∈ Lie B_a` and `ξ_d ∈ Lie B_d`.
     `Λ_d` vanishes on `Lie(A_a^{N+1})` and `Λ_a` vanishes on `Lie(A_d^{N′+1})`. Hence `Λ_a(ξ_a) = 0` and
     `Λ_d(ξ_d) = 0`.
   * *a and d on one class, `s_a ≠ s_d`:* by (S1′.2), the σ_{s_a}-projection `π_{s_a}(ξ_ab)` lies in `Lie B`.
     `Λ_a` reads only `z_{s_a}`-coordinates and `Λ_d` reads only `z_{s_d}`-coordinates. So
     `Λ_a(ξ) = Λ_a(π_{s_a}ξ) = (Λ_a + Λ_d)(π_{s_a}ξ) = 0`, and likewise `Λ_d(ξ) = 0`.

   In both cases `x − cP_a = 0` and `x′ − c′P_d = 0`, **with the given `c, c′`**.

The second clause is identical with `(c, b)` in place of `(a, d)`.

### 2.2 Edge cases

| case | outcome |
|---|---|
| `x = 0` and/or `x′ = 0` (`N = 0` is allowed in `zQbar`) | Covered: the γ-copies stay in ξ. For example `x′ + q = cP_a + c′P_d` gives `q = 0`, `cP_a = 0` (so `c = 0`), and `x′ = c′P_d`. This agrees with `WuestholzXA`. |
| a, d on one variety (different points or the same point) | Covered by step 5 (one class), using separate copies of `A` for each `v_k`. It needs only `σ_{s_a} ≠ σ_{s_d}`. |
| a, d on isogenous varieties, embeddings not corresponding | Covered after transport by (R). Even without transport, `End⁰(A^m × A′^{m′}) ≅ M_{m+m′}(F)` gives the eigen-splitting. |
| a, d on isogenous varieties, corresponding embeddings (excluded by (C2)) | **False.** If `P_d = λP_a` with `λ ∈ ℚ̄ˣ`, take `x = P_a` (ℓ = P), `x′ = q = c = 0`, `c′ = 1/λ`. The conclusion `x = 0·P_a` fails. |
| a logarithm in `LA` that is a period ω | Covered. Its exponential is 0, which is algebraic. The conclusion `z_{s_a}(ω) ∈ ℚ̄P_a` is consistent with (S1′.3), since `z_s(ω) ∈ σ_s(F)P_s`. |
| ℚ̄-combinations rather than single logarithms | Covered by using one copy per summand. This is exactly the paper's "K-combinations of `u_1, …, u_m` … in `G_a × ∏_A A^m`" (line 714). |
| `P_a = 0` (excluded, and impossible for γ ≠ 0) | The derivation still gives `x = 0`. The clause does not use `P ≠ 0`. |

### 2.3 Not stronger than the literature

* The conclusion `x = cP_a` with the **given** `c` comes out of step 5 exactly (`Λ_a(ξ_a) = x − cP_a`). It is not an
  existence statement upgraded to an equation.
* `q = 0` comes from `L = G_a` alone.
* Each clause uses only distinctness of its own pair (a ≠ d, resp. c ≠ b), up to isogeny. It does not need the four slots
  to be pairwise distinct, nor the first-kind relation (R), nor simplicity of the varieties of the other pair.
* It is a ℚ̄-linear statement about one point of a product of copies of `G_a` and simple CM varieties. That is the
  standard Baker–Wüstholz shape (compare the paper's "slot splitting" and Baker–Wüstholz Ch. 6).

### 2.4 Robustness, and what makes it false [Proved; one case Lean]

1. **Downward closed** in each `LA`. It also holds when `LA` is replaced by its ℚ̄-span, since `zQbar` is already a
   ℚ̄-span.
2. **Only slot coordinates matter.** `zQbar(S)` uses only coordinate `S.s` of each `ℓ`. So the input holds even for
   "incoherent" vectors whose coordinates are `z_s` of different logarithms. It is also invariant under rescaling, by
   any factor in ℚ̄ˣ, the `s`-coordinate of `LA` and the `s`-coordinate of `P`, independently. So a mismatch of
   eigen-differential normalisation between `LA` and `P` is harmless. A transcendental mismatch is not; (C3) excludes it.
3. **Bad `LA` makes it false.** [Lean, `check_x7.lean`] `¬ WuestholzSplitXA (X7S {fun _ => 1}).slot`: take `x = 1`,
   `x′ = 0`, `q = −1`, `c = c′ = 0`. As in the X7 report, this makes `thmXA` vacuous, not wrong.
4. As for `WuestholzX7` (X7 report §2), points 1–2 do **not** carry over to `Thm11KappaXA`. Its generators
   `genA S j i e v` apply `[α^e]` to a whole vector, through `κ_s^e v_s`. So the W88 input needs coherent vectors of one
   logarithm, in one ℚ̄-model, with `[α]` acting on `z_s` by `κ_s`. That belongs to the `Thm11KappaXA` review
   (`reviews/REFEREE_HYP_XA.md`), not here.

### 2.5 Comparison with the paper (proof of Theorem X, lines 705–720)

* **Same statement.** The paper derives `z_a(v_a − xγ_a) + z_d(v_d − yγ_d) + q₁ = 0` with `x, y ∈ K`. That is
  `z_a(v_a) + z_d(v_d) + q₁ = xP_a + yP_d`, with `z_a(v_a) ∈ ℚ̄ z_a(Λ(A_a))` because `v_a ∈ ℚ̄Λ(A_a)`. Its conclusion
  is `q₁ = 0`, `z_a(v_a) = xP_a`, `z_d(v_d) = yP_d`. This is clause 1 of `WuestholzSplitXA` with `c = x` and `c′ = y`.
  `thmXA` calls it in exactly this way (`hSp.1 _ _ q₁ x y …`), and calls clause 2 with `c = xβ`, `c′ = yβ/μ`.
* **Same derivation.** The paper uses one copy per `u_i`, the point `(1, (u_i))`, `L = G_a` from the `G_a`-coordinate,
  and separation by "independent `u_σ` (S1)".
* **Wording (minor, optional).** The X7 report's point X3 is now mostly met: the text writes `H = L × ∏_A B_{S_A}`.
  However, it attributes the product over isogeny classes to (P). (P) gives only `L × B`. The splitting of `B` over
  classes is the `Hom = 0` part of (S1). Suggested: "By (P) and (S1) (Hom = 0 between classes), `H = L × ∏_A B_{S_A}`."
* **(W) at line 359** is stated with "pairwise distinct eigen-slots". The definition of equality of slots (isogenous with
  corresponding embeddings) appears only at line 594. A forward reference "(distinct in the sense of §`sec:X`)" already
  exists. No change is needed.

### 2.6 Data model check

* In `XSetup`, slot `j` is `⟨AV (cls j), sl j⟩`, so slots on one class share `P` and `LA`. This matches the paper's
  "`G = ∏_A A × G_a²` over the isogeny classes, each taken once" (line 601). `thmXA` builds the `zQbar` witnesses
  from `v j k (cls j) ∈ insert P LA` (`hzQ`), which is the paper's `v_j ∈ ℚ̄Λ(A_j)`.
* `zQbar` includes `ℓ = P`, the cycle γ. That is correct: `Λ(A) ⊃ Ω(A)`, and the paper's `v_a − xγ_a` needs it.
* `CMAV.Good` (distinct algebraic conjugates, `2g ≤ [F : ℚ]`) cannot express simplicity, primitivity of the type or the
  ℚ̄-model. Those remain soundness conditions (C1)–(C3).

### Issues for input 2

| # | severity | issue | fix |
|---|---|---|---|
| XA1 | Minor (documentation) | The docstring of `WuestholzSplitXA` states no soundness conditions. | Add: "Sound when slots `a ≠ d` and `c ≠ b` are distinct up to isogeny (non-isogenous varieties, or one simple CM variety with different embeddings); each `A` is a simple CM abelian variety over ℚ̄; `P` is the eigen-coordinate vector of a nonzero cycle; `LA` consists of eigen-coordinate vectors of logarithms of ℚ̄-points of the same ℚ̄-model (any subset, any ℚ̄ˣ-rescaling of each coordinate). False for other `LA`, e.g. `LA ∋ (1, …, 1)`, which makes `thmXA` vacuous." |
| XA2 | Minor (documentation) | "Pairwise distinct" is not defined at the point of use. In Lean, `XSetup.Distinct` covers one record only, and the across-record part is the "each isogeny class once" convention. | State in TRUST.md (and in the `XSetup` docstring) that `AV i` and `AV i′` must be non-isogenous for `i ≠ i′`, and that this is not checked by Lean. |
| XA3 | Info (paper) | Line 717 attributes `H = L × ∏_A B_{S_A}` to (P) alone. | "By (P) and (S1)". |

---

## 3. The level-seven instance [Lean]

`X7S LA` has two classes, `A7 LA = ⟨3, ζ^{s+1}, perT, LA⟩` and `E7AV = ⟨1, α7, Ω, {w | LogE E7 (w 0)}⟩`. Its slots are
`a, b, c = z₁, z₂, z₃` on `A` and `d = z_E`. (Here `perT s = perA (s+1)` and `Ω = omega7`.) The following are checked
in `reviews/checks/inputsxa/check_x7.lean`; the file compiles with no output.

1. `example : WuestholzXA (X7S LA).slot = WuestholzBeta7 := rfl`, together with the `Iff.rfl` form. The slot periods
   unfold to `perT 0 = perA 1`, `perA 2`, `perA 3` and `(fun _ => omega7) 0 = omega7`. So the two propositions are
   **definitionally equal**: the same expression up to δ/β/ι-reduction, though not syntactically identical. This
   matches the one-line proof of `wuestholzXA_X7` and `X7S_per` (`rfl`).
2. `example (h : WuestholzSplitXA (X7S LA).slot) : WuestholzX7 LA`. The witnesses use `N = 1` and `c = 1`.
   * Clause 1: `ℓ = v ∈ insert perT LA`, coordinate `0`; and `ℓ = fun _ => u ∈ insert (fun _ => Ω) {w | LogE E7 (w 0)}`.
   * Clause 2: `v′` at coordinate 2 (slot c, `perA 3`) and `v` at coordinate 1 (slot b, `perA 2`).

   The premises and conclusions match term for term. So the new input is **at least as strong** as the old one.
3. The converse is not available as a Lean implication. `WuestholzX7` quantifies over single vectors, while `zQbar`
   allows ℚ̄-combinations. Mathematically the X7 report already showed that the old clause holds for the ℚ̄-span (its
   §2, robustness 2), which is what `WuestholzSplitXA (X7S LA_A).slot` asserts. So nothing new is assumed at level
   seven beyond what that report established.
4. `¬ WuestholzSplitXA (X7S {fun _ => 1}).slot` (the bad-`LA` example of §2.4).

The E-slot inherits the X7 report's facts (G2): the lattice `Ωℤ[α]` has algebraic `g₂, g₃` (`j = −3375`), so
`{u | LogE E7 u}` is the set of logarithms of ℚ̄-points of a curve over ℚ̄, and `Ω` is a nonzero period of it. Slot d
(E) and slots a, b, c (A, simple of dimension 3) lie in different isogeny classes. Slots a, b, c have distinct
embeddings `ζ, ζ², ζ³`. So (C1)–(C3) hold for `X7S LA_A`, with `LA_A` as in the X7 report.

---

## 4. Suggested docstring / TRUST.md wording

For `WuestholzSplitXA` (docstring), append:

> Sound (Wüstholz 1989 on `G_a × ∏_A A^m`, one copy per logarithm) when, for each of the pairs `(a, d)` and `(c, b)`,
> the two slots are distinct up to isogeny (non-isogenous varieties, or different embeddings of one simple CM variety);
> each `A` is a simple CM abelian variety over `ℚ̄`; `A.P` is the eigen-coordinate vector of a nonzero cycle; and `A.LA`
> consists of eigen-coordinate vectors of logarithms of `ℚ̄`-points of the same model (any subset; each coordinate may
> be rescaled by `ℚ̄ˣ`). For other `LA` it can be false (e.g. `LA ∋ (1, …, 1)`), and then `thmXA` is vacuous.

For `WuestholzXA`, replace "(periods of pairwise distinct slots)" with:

> (periods of pairwise distinct slots of simple CM abelian varieties over `ℚ̄`: two slots are equal iff the varieties
> are isogenous and the embeddings correspond; Wüstholz 1989 on `G_a × ∏_A A` at `(1, (γ_A))`).

TRUST.md rows (§3), in the style of the X7 report:

> | `AbVar.WuestholzXA S` | `1, P_a, P_b, P_c, P_d` are `ℚ̄`-linearly independent | `CM4E/AbVar/XGen.lean` | Wüstholz 1989 on `G_a × ∏_A A` at `(1, (γ_A))`; paper (W) without π. Sound for pairwise distinct (up to isogeny) first-kind slots of simple CM varieties. At level seven it is `WuestholzBeta7` by `rfl`. Review: `reviews/REFEREE_INPUTS_XA.md` (CORRECT). |
> | `AbVar.WuestholzSplitXA S` | slot splitting: `x + x′ + q = cP_a + c′P_d` with `x ∈ ℚ̄z_a(Λ(A_a))`, `x′ ∈ ℚ̄z_d(Λ(A_d))`, `q, c, c′ ∈ ℚ̄` ⇒ `q = 0`, `x = cP_a`, `x′ = c′P_d`; same for `(c, b)` | `CM4E/AbVar/XThm.lean` | Wüstholz 1989 on `G_a × ∏_A A^m`, (P), (S1). Sound for `LA` ⊂ logarithms of ℚ̄-points in eigen-coordinates. At level seven it implies `WuestholzX7 LA` (checked in Lean). Review: `reviews/REFEREE_INPUTS_XA.md` (CORRECT WITH NOTES). |

Add one sentence to the `XSetup` paragraph: "`AV i`, `AV i′` (`i ≠ i′`) must be non-isogenous; `XSetup.Distinct`
checks only slots on one record."

---

## Verdicts

- `WuestholzXA S`: **CORRECT.**
  * It follows from Wüstholz 1989 on `G_a × ∏_A A` at `(1, (γ_A))`, using (P), simplicity, and Hom = 0 between classes.
  * It is a strict special case of the paper's (W).
  * `P_j ≠ 0` is automatic for a nonzero cycle.
  * It is false if two records are isogenous with corresponding embeddings, so "distinct" must be read up to isogeny.
    The docstring should say so (cosmetic).
  * At level seven it is `WuestholzBeta7` by `rfl` [Lean].
- `WuestholzSplitXA S`: **CORRECT WITH NOTES.**
  * It follows from Wüstholz 1989 on `G_a × ∏_A A^m` (one copy per logarithm), with `q = 0` from `L = G_a` and
    separation by the product over isogeny classes and the F-eigen-splitting of `T(B)` (S1).
  * It holds for ℚ̄-combinations, x or x′ = 0, slots on one variety, isogenous records with non-corresponding
    embeddings, logarithms that are periods, and incoherent or ℚ̄ˣ-rescaled `LA`. It needs only a ≠ d and c ≠ b.
  * It is not stronger than the literature: the given `c, c′` come out exactly.
  * Notes (documentation only):
    * XA1: state the soundness conditions in the docstring.
    * XA2: document in TRUST.md that classes in `XSetup` must be non-isogenous.
    * XA3: a paper wording fix at line 717.
  * It is false for a bad `LA` [Lean], which makes `thmXA` vacuous, not wrong.
  * At level seven it implies `WuestholzX7 LA` [Lean], so it is at least as strong as the old input.
