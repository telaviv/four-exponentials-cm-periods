# lean_mstar: four exponentials at CM periods, in Lean 4

Lean 4 + Mathlib certificate for parts of the paper *Four exponentials at CM periods, and a bilinear statement for two
CM elliptic curves* (draft; snapshot in [`paper/`](paper/)).

## Results

With `ϖ = Γ(1/4)²/(2√(2π))` and `Ω_ρ = Γ(1/3)³/(2^{4/3}π)`, the real periods of `y² = 4x³ − 4x` and `y² = 4x³ − 4`
(library `CM4E`, standard axioms only):

* `CM4E.Final.fourExpAt_varpi_all`, `CM4E.Final.fourExpAt_varpi_div_pi_all`: the four exponentials statement
  `FourExpAt t` at **`t = cϖ` and `t = cϖ/π` for every algebraic `c ≠ 0`** (the paper's Theorem 1 for `Ω = ϖ`).
  `CM4E.Final.fourExpAt_omegaRho_all`, `…_div_pi_all`: the same for `Ω_ρ`.
* `CM4E.Final.two_three_varpi`, `two_three`, `two_three_omegaRho`: **`2^t` and `3^t` are not both algebraic** for
  `t = ϖ`, `ϖ/π`, `Ω_ρ`.
* `CM4E.Final.mx_K`, `mx`, `mx1`: **Theorem MX** for the two curves and every algebraic `β ≠ 0`, and Corollary MX1.
* `CM4E.Final.mxP_K`, `deg2_i`, `deg2_ii`: Proposition D′ (Theorem MX′) and **`π, ϖ, Ω_ρ, ϖΩ_ρ` and `1, ϖ, Ω_ρ, ϖΩ_ρ/π`
  are linearly independent over `ℚ̄`**.
* `CM4E.Final.thmM_varpi`, `m1_varpi`, `m3_varpi`, `m3'_varpi`, `meta_varpi`: **Theorem M** and Corollary M, e.g.
  `℘(cϖ/π) ∉ ℚ̄` for algebraic `c ≠ 0`.
* `CM4E.Final.mg_K_varpi`, `mgn_K_varpi`: the `K`-dimension forms of Theorems MG and MG♮ (`dim_K S_K ≤ 2`).
* `CM4E.Final.thmS_varpi`, `mg1_varpi`, `mg3_varpi`: Theorem S of the companion paper, Corollaries MG1, MG3.

Each theorem assumes **one published theorem**: Waldschmidt's κ-refined hyperplane theorem (W88, Thm 1.1 with (5.4)),
for the algebraic groups of the relevant proof. It is stated as an explicit hypothesis, never as an axiom. The `Ω_ρ`
and MX results also assume that `g₂, g₃` of `Ω_ρℤ[ρ]` are algebraic, and some corollaries use named classical inputs
(Wüstholz, Masser, Laurent, Baker, Hermite–Lindemann). Everything else is proved, including `g₂(ϖℤ[i]) = 4` and Schneider's theorem. What
is assumed, why it is believed, and which paper results are covered: [TRUST.md](TRUST.md).

## Layout

| path | content |
|---|---|
| `CM4E/Defs.lean` | elementary definitions used in the statements (`FourExpAt`, `logAlg`, `varpi`, `omegaRho`); read first |
| `CM4E/Waldschmidt.lean` | the hypothesis form `HyperplaneKappa` (W88 §5d) and the model of `G_m^{d₁} × E` |
| `CM4E/Lattice.lean`, `CM4E/Common.lean` | the lattice `ϖℤ[i]`, `g₃ = 0`, quasi-periods; shared small lemmas |
| `CM4E/MainQi.lean`, `CM4E/TwoThree.lean` | Theorem 1(b) for `c ∈ ℚ(i)`; `2^{ϖ/π}, 3^{ϖ/π}` |
| `CM4E/MainNat.lean` | Theorem 1(a) for `c ∈ ℚ(i)`; `2^ϖ, 3^ϖ` |
| `CM4E/MX.lean` | the curve `y² = 4x³ − 4`, quasi-periods, `Λ(E^♮)` (`LogNat`) |
| `CM4E/Gen/` | the general proofs: Theorem 1 for every algebraic `c` (`Frame`, `MG`, `MGn`, `Instances`), adapted number-field bases, Theorem MX (`MXGen`), MX′ and deg2 (`MXP`, `Deg2`), Theorem S and MG1/MG3 (`Frame2`, `SMG`, `MG13`), Theorem M (`FrameM`, `ThmM`, `ThmMCor`), `K`-forms of MG, MG♮ (`MGK`, `MGnK`) |
| `CM4E/Final.lean` | the final statements, with all inputs except W88 discharged |
| `CM4E/CaseCheck.lean`, `CM4E/LemmaL.lean` | arithmetic of the paper's Theorem 4.1 case tables; Step 1 of Prop. D |
| `CM4E/Ext/` | Weierstrass `ζ`/`σ`, `g₂(ϖℤ[i]) = 4`, Schneider's theorem (vendored; see `CM4E/Ext/PROVENANCE.md`) |
| `Axioms.lean` | axiom audit of the main declarations |
| `reviews/` | fidelity reviews of the hypothesis models, with their check scripts |
| `paper/` | snapshot of the paper |

## Build

```bash
lake exe cache get
lake build
lake env lean Axioms.lean
```

Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`.

## Next steps

* Discharge `hW`: formalise W88 Thm 4.1 / §5d (in progress in the sibling project `lean_lsg`) and prove the soundness
  of the group models.
* Theorem 1 for every CM curve (more `CMLattice` instances); Baker's reduction for the `K`-forms; (M2) via
  Gel'fond–Schneider; Hermite–Lindemann from the vendored Schneider–Lang criterion; the companion paper's Theorems A
  and X (they need a modelled CM abelian variety, see `TRUST.md` §8).

## License and provenance

Apache 2.0 ([LICENSE](LICENSE)). Written by AI models (Claude, Anthropic) under the direction of the author. All review
so far is by AI referees ([`reviews/`](reviews/)); no human expert has reviewed the definitions or proofs.
