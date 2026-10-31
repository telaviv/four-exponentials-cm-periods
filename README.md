# lean_mstar: the M* results (four exponentials at CM periods and relatives), in Lean 4

Formalisation project for the paper *Four exponentials at CM periods, and a bilinear statement for two CM elliptic
curves* (draft, `../schanuel/five_exp/pilot_thmM/paper/`).

**Target.** For the real period ϖ = Γ(1/4)²/(2√(2π)) of y² = 4x³ − 4x and any algebraic c ≠ 0, the four exponentials
conjecture holds at t = cϖ and at t = cϖ/π. For example, 2^ϖ and 3^ϖ are not both algebraic. The precise statements
are in [`CM4E/Defs.lean`](CM4E/Defs.lean); read that file first.

**Status (2026-10-30): conditional headline proved.**

`CM4E.TwoThree.two_three` (standard axioms only) says that **2^{ϖ/π} and 3^{ϖ/π} are not both algebraic**, assuming:
* (H1) Waldschmidt's κ-refined hyperplane theorem (W88 §5d) for G_m⁴ × E, stated in
  [`CM4E/Waldschmidt.lean`](CM4E/Waldschmidt.lean);
* (H2) g₂ of the lattice ϖℤ[i] is algebraic (g₃ = 0 is proved);
* (H3) ϖ/π is irrational.

`CM4E.MainQi.fourExpAt_Qi` is the general version: `FourExpAt (cϖ/π)` for every c ∈ ℚ(i)^× (four exponentials at
t = cϖ/π, only ℚ-independence of the logarithms assumed). What is assumed and what is covered: [TRUST.md](TRUST.md).

`CM4E.MainNat.two_three_varpi` says that **2^ϖ and 3^ϖ are not both algebraic** (Theorem 1(a); general form
`CM4E.MainNat.main`: `FourExpAt (cϖ)` for c ∈ ℚ(i)^×), assuming (H1′) W88 §5d for G_m⁸ × Q″, where Q″ is a quotient of
(E^♮)⁴ (same form as H1, model `gmQ` in [`CM4E/MainNat.lean`](CM4E/MainNat.lean)), (H2), and (H3′) ϖ is transcendental.

`CM4E.MX.main` is **Theorem MX in K-form** (Proposition D) for K = ℚ(i, √3): for X ∈ Λ(E_i^♮), Y ∈ Λ(E_ρ^♮),
a, t ∈ ℚ̄ and β ∈ K^×, the relation (z(X) + z(Y) + a)·βη(Ω_ρ) = (w(X) + w(Y) + t)·ϖ forces
z(X) + z(Y) + a ∈ Kϖ + KΩ_ρ. It assumes W88 §5d for G_a × G_ℓ (model `gmX` in [`CM4E/MX.lean`](CM4E/MX.lean)), that
g₂, g₃ of both lattices are algebraic, and Wüstholz's ϖΩ_ρ/π ∉ ℚ̄ and Ω_ρ/ϖ ∉ ℚ̄. The Weierstrass ζ function (not in
Mathlib) is defined there, with a proof that its series converges locally uniformly.

Also proved, with standard axioms only:
* the arithmetic of the paper's case checks against Waldschmidt's Theorem 4.1, for every n
  (`CM4E/CaseCheck.lean`);
* the algebra of the two parallel periods, Lemma L (`CM4E/LemmaL.lean`).

The targets are **not** proved yet. The plan, dependency graph and reuse map are in [BLUEPRINT.md](BLUEPRINT.md).

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake env lean Axioms.lean
```

Toolchain and Mathlib: v4.35.0, as in `../schanuel/six_exp/lean` (StrongSix). During development `.lake/packages` is a
directory junction to StrongSix's packages, so Mathlib is not downloaded twice. A fresh clone should run
`lake exe cache get` instead.

## Provenance

Written by AI models (Claude, Anthropic) under the direction of the author. No human expert has reviewed the
definitions or proofs yet.
