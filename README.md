# CM4E: four exponentials at CM periods, in Lean 4

Formalisation project for the paper *Four exponentials at CM periods, and a bilinear statement for two CM elliptic
curves* (draft, `../schanuel/five_exp/pilot_thmM/paper/`).

**Target.** For the real period ϖ = Γ(1/4)²/(2√(2π)) of y² = 4x³ − 4x and any algebraic c ≠ 0, the four exponentials
conjecture holds at t = cϖ and at t = cϖ/π. For example, 2^ϖ and 3^ϖ are not both algebraic. The precise statements
are in [`CM4E/Defs.lean`](CM4E/Defs.lean); read that file first.

**Status (2026-10-30): scaffolding.** Proved so far, with standard axioms only:
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
