# Paper snapshot

`paper.tex` / `paper.pdf`: *Four exponentials at periods of CM abelian varieties* (draft), snapshot of 2026-10-31 of
`schanuel/five_exp/paper_cm/`. It merges the earlier drafts [I] (*Four exponentials at CM periods, and a bilinear statement
for two CM elliptic curves*) and [II] (CM abelian varieties). `TRUST.md` and the README cite this numbering; Lean
docstrings may still cite the old drafts by LaTeX label (`thm:MGn`, `prop:X`, ...), which survive in the merged source
(except [I] `thm:A`, now `thm:one`). The paper is not posted.

## Numbering map (copied from paper_cm/STATUS.md) (from the compiled `.aux` files of [I], [II] and paper_cm)

Old numbers are those of the frozen drafts ([I] after its Revision 7; [II] after referee P2-2). Unlabelled remarks were
matched by position.

| old [I] | new |
|---|---|
| Theorem 1 (thm:A) | Theorem 1.1 (thm:one) |
| Corollary 2 (MG1intro) | Corollary 1.3 |
| Theorem 3 (MX) | Theorem 1.6 |
| Corollary 4 (MX1) | Corollary 1.7 |
| Corollary 5 (Γ) | Corollary 1.8 |
| Theorem 6 (M) | Theorem 1.9 |
| Corollary 7 (Cor M: M1–M3′, Mη) | Corollary 1.10 |
| Theorem 8 (RW93) | Theorem 2.4 |
| Theorem 9 (W88 Thm 4.1) | Theorem 2.1 |
| Lemma 10 (Lemma K) | Lemma 2.3 (g = 1 case of Lemma K′ = 2.2) |
| Theorem 11 (W88 Thm 1.1 under (5.4); Lean's `Thm11Kappa`) | Theorem 2.5 |
| Lemma 12 (α_K(E^♮)) | Lemma 2.6 |
| Theorem 13 (MG) | Theorem 3.1 |
| Corollary 14 (MG2) | Corollary 3.2 |
| Remark 15 (MG via §5d) | Remark 3.3 |
| Corollary 16 (MG1) | Corollary 7.1 |
| Corollary 17 (MG3) | Corollary 7.2 |
| Theorem 18 (MG♮) | Theorem 3.4 |
| Corollary 19 (MG♮2) | Corollary 3.5 |
| Remark 20 (MG♮ via §5d) | Remark 3.6 |
| Theorem 21 (affine MG) | Theorem 7.6 |
| Corollary 22 (affine corollaries) | Corollary 7.7 |
| Theorem 23 (general form) | Theorem 3.13 |
| Corollary 24 (elliptic 4E) | Corollary 3.14 |
| Proposition 25 (Prop D) | Proposition 5.1 |
| Remark 26 (the count; MX via §5d) | Remark 5.2 |
| Remark 27 (other pairs) | Remark 5.3 |
| Remark 28 (Γ) | Remark 5.4 |
| Prop D′ (inside the proof of Theorem 29) | Proposition 5.5 (prop:Dp; **new number**, merge-referee revision) |
| Theorem 29 (MX′) | Theorem 5.6 (was 5.5 in the first merged version) |
| Corollary 30 (MX′ corollary) | Corollary 5.7 (was 5.6 in the first merged version) |
| Corollary 31 (deg2) | Corollary 7.5 |
| Lemma 32 (Lemma U) | Lemma A.1 |
| Remark 33 (addition laws) | Remark A.2 |
| §1 Introduction | §1 |
| §2 subgroup theorem and RW count | §2 (W88 part §2.1, RW part §2.4) |
| §3 four exponentials at CM periods | §3.1–3.2 (overlap paragraph → §8.1; MG1, MG3 → §7.1) |
| §3.1 fibre twin | §3.2 |
| §3.2 affine version | §7.4 |
| §3.3 general form | §3.4 |
| §4 Theorem M (4.1 first proof, 4.2 second proof, 4.3 corollaries) | §5.1, §5.2, §5.3 |
| §5 Theorem MX: §5.1 set-up | §2.3 |
| §5.2 proof of MX | §5.4 |
| §5.3 controls | §5.5 |
| §5.4 twisted variant (MX′) | §5.6 |
| §5.5 degree-two statements | §7.3 |
| §5.6 abelian-surface analogue | §5.7 |
| §6 single-partner limits for e^{π²} | §5.8 |
| §7 consistency checks | §9.1 |
| §8 status, sources not consulted, formal verification | §9.2, §9.3 (novelty text → §8) |
| App. A (Lemma U) | App. A |
| eq. (1) Laurent's identity, (2) eq:split, (3) eq:star | eq. (4), (3), (5) |

| old [II] | new |
|---|---|
| Theorem 1 (Theorem A) | Theorem 1.2 |
| Corollary 2 (A2intro) | Corollary 1.4 |
| Corollary 3 (X7intro) | Corollary 1.11 |
| Theorem 4 (Theorem S) | Theorem 1.5 |
| Theorem 5 (W88 Thm 4.1) | Theorem 2.1 |
| Lemma 6 (Lemma K′) | Lemma 2.2 |
| Theorem 7 (MG-A) | Theorem 3.7 |
| Remark 8 (RW count) | Remark 3.8 |
| Theorem 9 (MG♮-A) | Theorem 3.9 |
| Remark 10 (new instances?) | Remark 3.10 |
| Corollary 11 (A2) | Corollary 7.3 |
| Remark 12 (no Chudnovsky) | Remark 7.4 |
| Remark 13 (not a linearisation) | Remark 3.11 |
| Remark 14 (strong form, not checked) | Remark 3.12 |
| Proposition 15 (prop:X) | Proposition 6.1 |
| Theorem 16 (Theorem X) | Theorem 6.2 |
| Lemma 17 (Lemma S′) | Lemma 6.3 |
| Lemma 18 (Lemma L′) | Lemma 6.4 |
| Remark 19 (second derivation) | Remark 6.5 |
| Theorem 20 (X7) | Theorem 6.6 |
| Corollary 21 (Cor X7 (a)–(c)) | Corollary 6.7 |
| Remark 22 (not linearisations) | Remark 6.8 |
| Remark 23 (where relations occur) | Remark 6.9 |
| Remark 24 (several pairs) | Remark 6.10 |
| Remark 25 (e^{π²}) | Remark 6.11 |
| Lemma 26 (Ω, η ∉ 𝓛̃; Lean's `NotLtilde`) | Lemma 4.1 |
| Theorem 27 (SMG, SMG♮) | Theorem 4.2 |
| Lemma 28 (subgroups for SMG♮) | Lemma 4.3 |
| Lemma 29 (Lemma N2) | Lemma 4.4 |
| Corollary 30 (Cor S) | Corollary 4.5 |
| Remark 31 (remarks on S) | Remark 4.6 |
| Remark 32 (strong six does not give S) | Remark 4.7 |
| §1 Introduction | §1 (overlap/literature → §8) |
| §2 the tool | §2.1 |
| §2.1 CM abelian varieties | §2.2 |
| §3 four exponentials at abelian eigen-periods | §3.3 (Cor A2 → §7.2) |
| §4 Theorem X (§4.1–4.5) | §6 (§6.1–6.5) |
| §5 strong four exponentials | §4 |
| §6 consistency checks | §9.1 |
| §7 status and dependencies | §9.2, §9.3 |
| eq. (1) eq:41, (2) eq:NR, (3) eq:R, (4) eq:X, (5) eq:Xineq | eq. (1), (2), (6), (7), (8) |

Labels kept: every `\label` key of [I] and [II] survives except [I] `thm:A` → `thm:one` (collision with [II]'s Theorem A)
and [II] `sec:tool` (merged into `sec:W88`). New keys: `sec:intro`, `sec:method`, `sec:W88`, `sec:Euniv`, `sec:A4E`,
`sec:fibre`, `sec:two`, `sec:cor`, `sec:MG13`, `sec:A2`, `sec:overlap`, `sec:conj`, `sec:hyd`, `sec:novM`, `sec:novA`,
`sec:deps`, `sec:formal`, `rem:X5d`, `rem:strongsix`. Added in the merge-referee revision: `prop:Dp` (Prop 5.5),
`rem:notlinA` (Remark 3.11), `rem:notlin` (Remark 6.8). The numbering map above was regenerated from `paper.aux` after
that revision; the only numbering change is in §5.6 (Prop D′ = 5.5 new; MX′ 5.5 → 5.6; its corollary 5.6 → 5.7).
Everything else (in particular Theorem A = 1.2, Cor 1.3 = MG1intro) is unchanged.

**For the Lean side (not edited):** `lean_mstar/TRUST.md` and README cite "Theorem 11", "Remarks 15, 20, 26", "Lemma notLt",
"[II]" etc.; with this map these become Thm 2.5, Rem 3.3, 3.6, 5.2, Lemma 4.1 and "this paper". TRUST.md's snapshot title
is that of [I]. Lean-side references to "Theorem 5.5 (MX′)" / "Cor 5.6" now mean Theorem 5.6 / Cor 5.7; Prop D′ is 5.5.
