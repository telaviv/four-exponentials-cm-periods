# lean_mstar: four exponentials at CM periods, in Lean 4

Lean 4 + Mathlib certificate for parts of the paper *Four exponentials at CM periods, and a bilinear statement for two
CM elliptic curves* (draft; snapshot in [`paper/`](paper/)).

## Results

With `ϖ = Γ(1/4)²/(2√(2π))`, the real period of `y² = 4x³ − 4x` (library `CM4E`, standard axioms only):

* `CM4E.Final.two_three_varpi`: **`2^ϖ` and `3^ϖ` are not both algebraic.**
* `CM4E.Final.two_three`: **`2^{ϖ/π}` and `3^{ϖ/π}` are not both algebraic.**
* `CM4E.Final.fourExpAt_varpi`, `CM4E.Final.fourExpAt_Qi`: the four exponentials statement `FourExpAt t` at `t = cϖ`
  and `t = cϖ/π` for every `c ∈ ℚ(i)ˣ` (the paper's Theorem 1 for these `c`).
* `CM4E.Final.mx`: Theorem MX in `K`-form for the curves `y² = 4x³ − 4x` and `y² = 4x³ − 4`, with `K = ℚ(i, √3)`.

Each theorem assumes **one published theorem**: Waldschmidt's κ-refined hyperplane theorem (W88, Thm 1.1 with (5.4)),
for the algebraic group of the relevant proof. It is stated as an explicit hypothesis, never as an axiom.
`CM4E.Final.mx` also assumes Wüstholz-type inputs about the second curve. Everything else is proved, including
`g₂(ϖℤ[i]) = 4` and Schneider's theorem on the transcendence of `ϖ` and `ϖ/π`. What is assumed, why it is believed,
and which paper results are covered: [TRUST.md](TRUST.md).

## Layout

| path | content |
|---|---|
| `CM4E/Defs.lean` | elementary definitions used in the statements (`FourExpAt`, `logAlg`, `varpi`, `omegaRho`); read first |
| `CM4E/Waldschmidt.lean` | the hypothesis form `HyperplaneKappa` (W88 §5d) and the model of `G_m^{d₁} × E` |
| `CM4E/Lattice.lean`, `CM4E/Common.lean` | the lattice `ϖℤ[i]`, `g₃ = 0`, quasi-periods; shared small lemmas |
| `CM4E/MainQi.lean`, `CM4E/TwoThree.lean` | Theorem 1(b) for `c ∈ ℚ(i)`; `2^{ϖ/π}, 3^{ϖ/π}` |
| `CM4E/MainNat.lean` | Theorem 1(a) for `c ∈ ℚ(i)`; `2^ϖ, 3^ϖ` |
| `CM4E/MX.lean` | Theorem MX (`K`-form) |
| `CM4E/Final.lean` | the final statements, with all inputs except W88 discharged |
| `CM4E/CaseCheck.lean`, `CM4E/LemmaL.lean` | arithmetic of the paper's Theorem 4.1 case tables; Step 1 of Prop. D |
| `CM4E/Ext/` | Weierstrass `ζ`/`σ`, `g₂(ϖℤ[i]) = 4`, Schneider's theorem (vendored; see `CM4E/Ext/PROVENANCE.md`) |
| `Axioms.lean` | axiom audit of the main declarations |
| `reviews/` | fidelity reviews of the three hypothesis models, with their check scripts |
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
  of the three group models.
* Extend Theorem 1 to all algebraic `c` (larger `K`) and to `Ω_ρ`; the `K`-version of Theorem MG and Cor. MG1, MG3.
* Theorem MX for general `β ∈ ℚ̄ˣ`, the step to `a = 0`, `z(X) ∈ ℚ(i)ϖ`, and Cor. MX1.

## License and provenance

Apache 2.0 ([LICENSE](LICENSE)). Written by AI models (Claude, Anthropic) under the direction of the author. All review
so far is by AI referees ([`reviews/`](reviews/)); no human expert has reviewed the definitions or proofs.
