# lean_mstar: four exponentials at CM periods, in Lean 4

Lean 4 + Mathlib certificate for the applications in the paper *A proof of the Roy–Waldschmidt theorem with period
term, with explicit consequences at CM and Beta periods* (draft; snapshot in [`paper/`](paper/); results are cited by its numbering).

## Results

**Unconditional** (W88 proved in `lean_lsg`, the project's one dependency besides Mathlib):
`CM4E.Unconditional.fourExpAt_varpi_div_pi_all` (**the four exponentials statement at `t = cϖ/π` for every algebraic
`c ≠ 0`**; e.g. `2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic, `CM4E.Unconditional.two_three`); **Theorem M for
`Ω = cϖ`** (`CM4E.Unconditional.thmM_varpi`) with (M1), (M3) and the `K`-form of Theorem MG; the same at `Ω_ρ` given that
`g₃(Ω_ρℤ[ρ])` is algebraic (`g₂ = 0` is proved); Cor. MG1, MG3, (M3′), (Mη) given only the named classical inputs
(Wüstholz, Baker, Hermite–Lindemann, Masser). With `lean_lsg`'s vector-extension theorem also **Theorem 1.2(a)**
(`CM4E.Unconditional.fourExpAt_varpi_all`: `FourExpAt (cϖ)` for every algebraic `c ≠ 0`; `2^ϖ, 3^ϖ` not both algebraic,
`CM4E.Unconditional.two_three_varpi`), the `K`-form of MG♮, and Theorem MX, Cor. MX1, deg2 (ii) with their named
inputs, and Theorem S (Theorem 1.6) (`CM4E.Unconditional.thmS_varpi`, given only Wüstholz's `NotLtilde`). Also Theorem MX′ and deg2 (i)
(`CM4E.Unconditional.mxP_K`, `deg2_i`). Still conditional: the abelian-variety results (including the
generic Theorem X, `CM4E.AbVar.XSetup.thmXA`). Everything below is conditional on W88 for the stated groups; the tiers are in
[TRUST.md](TRUST.md) §1a.

With `ϖ = Γ(1/4)²/(2√(2π))` and `Ω_ρ = Γ(1/3)³/(2^{4/3}π)`, the real periods of `y² = 4x³ − 4x` and `y² = 4x³ − 4`
(library `CM4E`, standard axioms only):

* `CM4E.Final.fourExpAt_varpi_all`, `CM4E.Final.fourExpAt_varpi_div_pi_all`: the four exponentials statement
  `FourExpAt t` at **`t = cϖ` and `t = cϖ/π` for every algebraic `c ≠ 0`** (the paper's Theorem 1.2 for `Ω = ϖ`).
  `CM4E.Final.fourExpAt_omegaRho_all`, `…_div_pi_all`: the same for `Ω_ρ`.
* `CM4E.Final.two_three_varpi`, `two_three`, `two_three_omegaRho`: **`2^t` and `3^t` are not both algebraic** for
  `t = ϖ`, `ϖ/π`, `Ω_ρ`.
* `CM4E.Final.mx_K`, `mx`, `mx1`: **Theorem MX** for the two curves and every algebraic `β ≠ 0`, and Corollary MX1.
* `CM4E.Final.mxP_K`, `deg2_i`, `deg2_ii`: Proposition D′ (Theorem MX′) and **`π, ϖ, Ω_ρ, ϖΩ_ρ` and `1, ϖ, Ω_ρ, ϖΩ_ρ/π`
  are linearly independent over `ℚ̄`**.
* `CM4E.Final.thmM_varpi`, `m1_varpi`, `m3_varpi`, `m3'_varpi`, `meta_varpi`: **Theorem M** and Corollary M, e.g.
  `℘(cϖ/π) ∉ ℚ̄` for algebraic `c ≠ 0`.
* `CM4E.Final.mg_K_varpi`, `mgn_K_varpi`: the `K`-dimension forms of Theorems MG and MG♮ (`dim_K S_K ≤ 2`).
* `CM4E.Final.thmS_varpi`, `mg1_varpi`, `mg3_varpi`: Theorem S (Theorem 1.6), Corollaries MG1, MG3.
* CM abelian varieties (`CM4E/AbVar/`): `AbVar.x7c` (**`1, B(2/7,2/7), B(3/7,3/7),
  B(3/7,3/7)/B(1/7,1/7)` are `ℚ̄`-linearly independent**), `AbVar.thmX7` (Theorem X at level seven),
  `AbVar.two_three_beta5'` (**`2^t, 3^t` are not both algebraic at `t = Γ(1/5)²/Γ(2/5)`**), Theorem A for `B(1/5,1/5)`,
  `B(1/7,1/7)`, the `K`-forms of MG-A, MG♮-A, Cor. A2, Theorem X7 with its torsion step, Cor. X7 (a), (b) for Abel–Jacobi
  integrals.
* Unconditional at `y⁵ = x(1 − x)` (W88 for `G_m^{2n} × A^r` and its vector extension proved in `lean_lsg`;
  `CM4E/Bridge/AbVar.lean`): `Bridge.two_three_beta5'_uncond` (**`2^t, 3^t` are not both algebraic at
  `t = Γ(1/5)²/Γ(2/5)`**, with no hypothesis), `Bridge.two_three_beta5_uncond` (the same at `t = Γ(1/5)²/(πΓ(2/5))`),
  `Bridge.fourExpAt_beta5'_uncond`, `Bridge.fourExpAt_div_beta5_uncond`, `Bridge.fourExpAt_beta5_uncond`,
  `Bridge.fourExpAt_pi_div_beta5_uncond`, and `Bridge.corA2_beta5_uncond` (only the named input `NotLtildeA`).

Each theorem assumes **one published theorem**: Waldschmidt's κ-refined hyperplane theorem (W88, Thm 1.1 with (5.4)),
for the algebraic groups of the relevant proof. It is stated as an explicit hypothesis, never as an axiom. The `Ω_ρ`
and MX results also assume that `g₃` of `Ω_ρℤ[ρ]` is algebraic (`g₂ = 0` is proved), and some corollaries use named classical inputs
(Wüstholz, Masser, Laurent, Baker, Hermite–Lindemann). Everything else is proved, including `g₂(ϖℤ[i]) = 4` and Schneider's theorem. What
is assumed, why it is believed, and which paper results are covered: [TRUST.md](TRUST.md).

## Layout

| path | content |
|---|---|
| `CM4E/Defs.lean` | elementary definitions used in the statements (`FourExpAt`, `logAlg`, `varpi`, `omegaRho`); read first |
| `CM4E/Waldschmidt.lean` | the hypothesis form `HyperplaneKappa` (W88 §5d) and the model of `G_m^{d₁} × E` |
| `CM4E/Lattice.lean`, `CM4E/Common.lean` | the lattice `ϖℤ[i]`, `g₃ = 0`, quasi-periods; shared small lemmas |
| `CM4E/MainQi.lean`, `CM4E/TwoThree.lean` | Theorem 1.2(b) for `c ∈ ℚ(i)`; `2^{ϖ/π}, 3^{ϖ/π}` |
| `CM4E/MainNat.lean` | Theorem 1.2(a) for `c ∈ ℚ(i)`; `2^ϖ, 3^ϖ` |
| `CM4E/MX.lean` | the curve `y² = 4x³ − 4`, quasi-periods, `Λ(E^♮)` (`LogNat`) |
| `CM4E/Gen/` | the general proofs: Theorem 1 for every algebraic `c` (`Frame`, `MG`, `MGn`, `Instances`), adapted number-field bases, Theorem MX (`MXGen`), MX′ and deg2 (`MXP`, `Deg2`), Theorem S and MG1/MG3 (`Frame2`, `SMG`, `MG13`), Theorem M (`FrameM`, `ThmM`, `ThmMCor`), `K`-forms of MG, MG♮ (`MGK`, `MGnK`) |
| `CM4E/Final.lean` | the final statements, with all inputs except W88 discharged |
| `CM4E/CaseCheck.lean`, `CM4E/LemmaL.lean` | arithmetic of the paper's Theorem 2.3 case tables; Step 1 of Proposition 7.1 (Prop. D) |
| `CM4E/AbVar/` | CM abelian varieties: adapted bases over `ℚ(ζ_N)`, Beta values at level 7, Theorem X7 (`FrameX`, `X7`), Theorem A (`ThmA`, `ThmAn`) |
| `Axioms.lean` | axiom audit of the main declarations |
| `reviews/` | fidelity reviews of the hypothesis models, with their check scripts |
| `paper/` | snapshot of the paper |

## Build

The project depends on Mathlib and on `lean_lsg` (with `lean_lsg`'s own dependency `StrongSix`), both declared in
`lakefile.toml`; `lean_lsg` must be checked out next to this folder.

```bash
lake exe cache get
lake build
lake env lean Axioms.lean
```

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

## Next steps

* Discharge the remaining hypotheses `hW` (the abelian-variety and level-seven groups) in `lean_lsg`.
* Theorem 1 for every CM curve (more `CMLattice` instances); `g₃(Ω_ρℤ[ρ]) = 4` (the real-period computation of
  `LSG.LemniscateIndep` redone for the hexagonal lattice); a bridge for SMG♮ (Theorem S); (M2) via Gel'fond–Schneider; Hermite–Lindemann from the
  Schneider–Lang criterion of `lean_lsg`.

## License and provenance

Apache 2.0 ([LICENSE](LICENSE)). Written by AI models (Claude, Anthropic) under the direction of the author. All review
so far is by AI referees ([`reviews/`](reviews/)); no human expert has reviewed the definitions or proofs.
