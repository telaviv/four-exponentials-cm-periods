# Paper snapshot

`paper.tex` / `paper.pdf`: *A proof of the Roy–Waldschmidt theorem with period term, with explicit consequences at CM and
Beta periods* (draft), snapshot of 2026-10-31 of `schanuel/five_exp/paper_cm/`. `TRUST.md` and the README cite this
numbering. Two maps follow: (1) the merged draft (*Four exponentials at periods of CM abelian varieties*, archived as
`paper_cm/archive/paper_merged.tex`) to this version; (2) the original drafts [I], [II] to the merged draft. Lean
docstrings may cite results by LaTeX label, which survive. The paper is not posted.

## (1) Numbering map, merged draft (old → new), regenerated from the `.aux` files

**REFEREE_R response (2026-10-31): numbering unchanged.** The 178 `\newlabel` entries of `paper.aux` after the response
build were compared by script with the `.aux` from before it: none removed, none added, none renumbered. No theorem-like
environment, section or equation was added or removed (only text, two footnotes and an item (e) inside Remark A.3), so
the unlabelled environments are unchanged as well and the map below stands as is.

Old = `archive/paper_merged.aux` (the 61-page version); new = `paper.aux` after the final build. A script compared every
`\newlabel` (129 old keys, 178 new keys): **no old label was removed or renamed**; 121 numbers changed, 8 stayed (`sec:intro`
1, `eq:41` (1), `sec:method` 2, `eq:NR` (2), **`thm:W88k` 2.5**, `app:U` A, `lem:U` A.1, `rem:addition` A.2). Note that
`thm:RW` (old Theorem 2.4) is now **Corollary 2.2**. Equations: new (3) = `eq:NRstar`, (5) = `eq:splitL`; old (3)–(8) →
(4), (6)–(10).

**Unlabelled environments** (matched by position): old Remark 3.12 (strong form) → 5.12; old Remark 3.18 (after Cor QL) →
5.18; old Example 4.15 → 6.15 (now labelled `ex:SE`); old Example 4.17 → 6.17; old Remark 6.11 → 8.11; old Remark 6.16 →
8.16; old Example 6.17 → 8.17. Item labels inside statements ((a), (b), (1)–(3), (i)–(v), (M1) …) are unchanged.

**For the Lean side (not edited; `lean_mstar/TRUST.md` and README cite numbers):** Theorem 1.1(a)/(b) → **1.2(a)/(b)**;
Theorem 1.2 (Theorem A) → **1.3**; Cor 1.3 → 1.4; Cor 1.4 → 1.5; Thm 1.5 (Theorem S) → **1.6**; Thm 1.6 MX → 1.7; Cor 1.7 →
1.8; Cor 1.8 Γ → 1.9; Thm 1.9 M → 1.10; Cor 1.10 → 1.11; Cor 1.11 X7 → 1.12; **Theorem 2.5 unchanged**; Thm 2.4 (RW93) → Cor
2.2; Thm 2.1 (W88 Thm 4.1) → Thm 2.3; Lemma 2.6 → 4.3; Thms 3.1, 3.4, 3.7, 3.9 → 5.1, 5.4, 5.7, 5.9; Remarks 3.3, 3.6, 5.2 →
5.3, 5.6, 7.2; Lemma 4.1 (notLt) → 6.1; Thm 4.2 (SMG) → 6.2; Thm 4.12 (SE) → **6.12**; Cor 4.13 → 6.13; Prop 5.1 D → 7.1; Prop
5.5 D′ → 7.5; Thm 5.6 MX′ → 7.6; Cor 5.7 → 7.7; Prop 6.1 → 8.1; Thm 6.2 X → 8.2; Thm 6.6 X7 → 8.6; Cor 6.7 → 8.7; Cor 7.1 MG1
→ 9.1; Cor 7.2 MG3 → 9.2; Cor 7.3 A2 → 9.3; Cor 7.5 deg2 → 9.5; sections §§3.3, 6, 7.2 → §§5.3, 8, 9.2; §9.3 → §12.3; App.
A unchanged. TRUST.md's snapshot title is now stale as well.

| label | kind | old number | new number |
|---|---|---|---|
| `sec:intro` | § | 1 | 1 |
| `eq:41` | eq. | 1 | 1 |
| `thm:one` | Theorem | 1.1 | 1.2 |
| `thm:A` | Theorem | 1.2 | 1.3 |
| `cor:MG1intro` | Corollary | 1.3 | 1.4 |
| `cor:A2intro` | Corollary | 1.4 | 1.5 |
| `thm:S` | Theorem | 1.5 | 1.6 |
| `thm:MX` | Theorem | 1.6 | 1.7 |
| `cor:MX1` | Corollary | 1.7 | 1.8 |
| `cor:gamma` | Corollary | 1.8 | 1.9 |
| `thm:M` | Theorem | 1.9 | 1.10 |
| `cor:M` | Corollary | 1.10 | 1.11 |
| `cor:X7intro` | Corollary | 1.11 | 1.12 |
| `sec:method` | § | 2 | 2 |
| `eq:NR` | eq. | 2 | 2 |
| `sec:W88` | § | 2.1 | 2.2 |
| `thm:W88` | Theorem | 2.1 | 2.3 |
| `sec:setting` | § | 2.2 | 4.1 |
| `lem:Kprime` | Lemma | 2.2 | 4.1 |
| `lem:K` | Lemma | 2.3 | 4.2 |
| `sec:Euniv` | § | 2.3 | 4.2 |
| `sec:RW` | § | 2.4 | 2.1 |
| `thm:RW` | Theorem | 2.4 | 2.2 |
| `thm:W88k` | Theorem | 2.5 | 2.5 |
| `lem:natural` | Lemma | 2.6 | 4.3 |
| `eq:split` | eq. | 3 | 4 |
| `sec:A4E` | § | 3 | 5 |
| `sec:MG` | § | 3.1 | 5.1 |
| `thm:MG` | Theorem | 3.1 | 5.1 |
| `cor:MG2` | Corollary | 3.2 | 5.2 |
| `sec:fibre` | § | 3.2 | 5.2 |
| `rem:MG5d` | Remark | 3.3 | 5.3 |
| `sec:A` | § | 3.3 | 5.3 |
| `thm:MGn` | Theorem | 3.4 | 5.4 |
| `sec:MGgen` | § | 3.4 | 5.4 |
| `cor:MGn2` | Corollary | 3.5 | 5.5 |
| `rem:MGn5d` | Remark | 3.6 | 5.6 |
| `thm:MGA` | Theorem | 3.7 | 5.7 |
| `rem:RW` | Remark | 3.8 | 5.8 |
| `thm:MGnA` | Theorem | 3.9 | 5.9 |
| `rem:newinst` | Remark | 3.10 | 5.10 |
| `rem:notlinA` | Remark | 3.11 | 5.11 |
| `thm:MGgen` | Theorem | 3.13 | 5.13 |
| `cor:ell4E` | Corollary | 3.14 | 5.14 |
| `lem:F` | Lemma | 3.15 | 5.15 |
| `thm:QL` | Theorem | 3.16 | 5.16 |
| `cor:QL` | Corollary | 3.17 | 5.17 |
| `sec:S` | § | 4 | 6 |
| `eq:laurent` | eq. | 4 | 6 |
| `sec:Sell` | § | 4.1 | 6.1 |
| `lem:notLt` | Lemma | 4.1 | 6.1 |
| `thm:SMG` | Theorem | 4.2 | 6.2 |
| `sec:SA` | § | 4.2 | 6.2 |
| `lem:SMGnsub` | Lemma | 4.3 | 6.3 |
| `sec:SE` | § | 4.3 | 6.3 |
| `lem:N2` | Lemma | 4.4 | 6.4 |
| `cor:S` | Corollary | 4.5 | 6.5 |
| `rem:Sremarks` | Remark | 4.6 | 6.6 |
| `rem:strongsix` | Remark | 4.7 | 6.7 |
| `thm:SA` | Theorem | 4.8 | 6.8 |
| `thm:SMGA` | Theorem | 4.9 | 6.9 |
| `lem:PnotinL` | Lemma | 4.10 | 6.10 |
| `cor:SA` | Corollary | 4.11 | 6.11 |
| `thm:SE` | Theorem | 4.12 | 6.12 |
| `cor:SE4` | Corollary | 4.13 | 6.13 |
| `lem:SE0` | Lemma | 4.14 | 6.14 |
| `thm:EA` | Theorem | 4.16 | 6.16 |
| `sec:two` | § | 5 | 7 |
| `eq:star` | eq. | 5 | 7 |
| `sec:M` | § | 5.1 | 7.1 |
| `prop:D` | Proposition | 5.1 | 7.1 |
| `sec:M2` | § | 5.2 | 7.2 |
| `rem:count` | Remark | 5.2 | 7.2 |
| `rem:general` | Remark | 5.3 | 7.3 |
| `sec:MX` | § | 5.4 | 7.4 |
| `rem:gamma` | Remark | 5.4 | 7.4 |
| `prop:Dp` | Proposition | 5.5 | 7.5 |
| `sec:MXP` | § | 5.6 | 7.6 |
| `thm:MXP` | Theorem | 5.6 | 7.6 |
| `cor:MXP` | Corollary | 5.7 | 7.7 |
| `sec:MXA` | § | 5.7 | 7.7 |
| `sec:3E` | § | 5.8 | 7.8 |
| `sec:X` | § | 6 | 8 |
| `eq:R` | eq. | 6 | 8 |
| `prop:X` | Proposition | 6.1 | 8.1 |
| `thm:X` | Theorem | 6.2 | 8.2 |
| `lem:Sprime` | Lemma | 6.3 | 8.3 |
| `sec:XfromP` | § | 6.3 | 8.3 |
| `lem:Lprime` | Lemma | 6.4 | 8.4 |
| `sec:X7` | § | 6.4 | 8.4 |
| `rem:X5d` | Remark | 6.5 | 8.5 |
| `sec:Xlin` | § | 6.5 | 8.5 |
| `thm:X7` | Theorem | 6.6 | 8.6 |
| `sec:X924` | § | 6.6 | 8.6 |
| `cor:X7` | Corollary | 6.7 | 8.7 |
| `rem:notlin` | Remark | 6.8 | 8.8 |
| `rem:where` | Remark | 6.9 | 8.9 |
| `rem:several` | Remark | 6.10 | 8.10 |
| `lem:rel924` | Lemma | 6.12 | 8.12 |
| `thm:X924` | Theorem | 6.13 | 8.13 |
| `cor:X924` | Corollary | 6.14 | 8.14 |
| `thm:Xk` | Theorem | 6.15 | 8.15 |
| `eq:X` | eq. | 7 | 9 |
| `sec:cor` | § | 7 | 9 |
| `sec:MG13` | § | 7.1 | 9.1 |
| `cor:MG1` | Corollary | 7.1 | 9.1 |
| `cor:MG3` | Corollary | 7.2 | 9.2 |
| `sec:A2` | § | 7.2 | 9.2 |
| `cor:A2` | Corollary | 7.3 | 9.3 |
| `sec:deg2` | § | 7.3 | 9.3 |
| `rem:noChud` | Remark | 7.4 | 9.4 |
| `sec:MGaff` | § | 7.4 | 9.4 |
| `cor:deg2` | Corollary | 7.5 | 9.5 |
| `thm:MGaff` | Theorem | 7.6 | 9.6 |
| `cor:MGaff` | Corollary | 7.7 | 9.7 |
| `eq:Xineq` | eq. | 8 | 10 |
| `sec:overlap` | § | 8 | 11 |
| `sec:conj` | § | 8.1 | 11.2 |
| `sec:hyd` | § | 8.2 | 11.3 |
| `sec:novM` | § | 8.3 | 11.4 |
| `sec:novA` | § | 8.4 | 11.5 |
| `sec:novH1` | § | 8.5 | 11.6 |
| `sec:status` | § | 9 | 12 |
| `sec:checks` | § | 9.1 | 12.1 |
| `sec:deps` | § | 9.2 | 12.2 |
| `sec:formal` | § | 9.3 | 12.3 |
| `app:U` | App. | A | A |
| `lem:U` | Lemma | A.1 | A.1 |
| `rem:addition` | Remark | A.2 | A.2 |

**New labels (no old number):** `cor:C42` = Corollary 10.2, `cor:CL4` = Corollary 10.6, `eq:NRstar` = eq. 3, `eq:splitL` = eq. 5, `ex:SE` = Example 6.15, `lem:NRintr` = Lemma 3.3, `lem:U0` = Lemma 3.8, `lem:Uper` = Lemma 10.7, `lem:bakercorner` = Lemma 3.7, `lem:corner` = Lemma 3.6, `lem:reducedNR` = Lemma 3.10, `lem:struct` = Lemma 3.1, `lem:subadd` = Lemma 3.2, `prop:C42line` = Proposition 10.3, `prop:codim` = Proposition 3.11, `prop:hyp` = Proposition 3.9, `prop:stepb` = Proposition 3.4, `prop:wue` = Proposition 3.5, `rem:G3` = Remark 3.12, `rem:Ugen` = Remark A.3, `rem:explicit` = Remark 11.1, `rem:inner` = Remark 2.1, `sec:C42` = § 10.1, `sec:CL4` = § 10.3, `sec:CMsetting` = § 4, `sec:H2` = § 10, `sec:P` = § 10.2, `sec:RtoApp` = § 4.4, `sec:U` = § 10.4, `sec:codim` = § 3.7, `sec:corner` = § 3.4, `sec:credit` = § 2.4, `sec:hyp` = § 3.6, `sec:linear` = § 3.5, `sec:novH2` = § 11.7, `sec:novR` = § 11.1, `sec:proofR` = § 3, `sec:proofRfin` = § 3.8, `sec:stepb` = § 3.2, `sec:stmtR` = § 2.3, `sec:struct` = § 3.1, `sec:weights` = § 4.3, `sec:wue` = § 3.3, `stmt:R` = Statement 2.4, `thm:C42` = Theorem 10.1, `thm:CL4` = Theorem 10.5, `thm:P` = Theorem 10.4, `thm:R` = Theorem 1.1, `thm:U` = Theorem 10.8


## (2) Numbering map, drafts [I]/[II] to the merged draft (copied from paper_cm/STATUS.md) (from the compiled `.aux` files of [I], [II] and paper_cm)

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
