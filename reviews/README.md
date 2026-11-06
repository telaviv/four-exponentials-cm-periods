# Fidelity reviews

Reports by AI referees (Claude) of the hypothesis models and named inputs, kept as written at the time of each review.
`TRUST.md` says which results and models each one covers.

* The reports cite earlier drafts of the paper ("draft [I]", "draft [II]", "the merged draft") and line numbers in them.
  Those drafts are not part of this repository; the LaTeX labels they name (`thm:MGA`, `sec:X7`, …) survive in
  `paper/paper.tex`.
* `checks/` holds the numerical scripts and their outputs (Python, GP). The reports also name Lean scratch files in
  `checks/` (axiom audits and referee lemmas); those have been removed. `Axioms.lean` now does the axiom audit, and the
  `CM4E.Ext` names in older reports are now `LSG`.
* `HypStdCM` in `REFEREE_BRIDGE_STD.md` is the former all-`d` form of `Bridge.HypStdCMAt`.
