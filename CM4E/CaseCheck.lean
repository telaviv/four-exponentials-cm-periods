/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# The case checks against Waldschmidt's Theorem 4.1 (arithmetic layer)

Waldschmidt 1988, Thm 4.1 asserts the existence of a connected algebraic subgroup `G' ≠ G` with
`δ > τ` and `(λ + δ₁ + 2δ₂)(d − N) ≤ (δ − τ)(d₁ + 2d₂ − κ)` (an *obstruction*). In each
application the paper lists all connected subgroups of an explicit group `G''` by a few numerical
invariants and shows that none is an obstruction. This file formalises **that arithmetic**, for
every `n`, exactly as tabulated in the paper:

* `MX`  : `G'' = G_a × G_ℓ` (paper, proof of Proposition D, Steps 3–4), `κ = 2n`;
* `MG`  : `G'' = G_m^{2n} × A''` (paper §3, Theorem MG), `κ = n`, `n = 2m`;
* `MGn` : `G'' = G_m^{2n} × Q''` (paper §3, Theorem MG♮), `κ = n`, `n = 2m`.

What is **not** formalised here: that the listed types exhaust the connected subgroups (the paper's subgroup
classifications), the bounds `b ≤ n` (Lemma K), the lower bounds for `λ` (Step 1 of Proposition D and its MG
analogues), and Theorem 4.1 itself. The main theorems of this project do not use this file: they go through
W88 §5d instead (`TRUST.md`). It certifies the arithmetic of the paper's Theorem 4.1 route. Each type below records only the invariants
`(dim G', whether π₀(G') = G_a, r = dim Ψ''(T_{G'}), λ-lower bound)` that those lemmas supply.
-/

namespace CM4E.CaseCheck

/-- Waldschmidt's obstruction inequality, with `τ = δ + r − 2` already substituted
(`W'' = ker Ψ''` of codimension 2), so `δ > τ ↔ r ≤ 1` and `δ − τ = 2 − r`.
`lhs = λ + δ₁ + 2δ₂`, `codimV = d − N`, `weight = d₁ + 2d₂ − κ`. -/
def Obstruction (lhs codimV weight r : ℕ) : Prop :=
  r ≤ 1 ∧ lhs * codimV ≤ (2 - r) * weight

/-! ## Theorem MX: `G'' = G_a × G_ℓ`, `d = 2n+2`, `d₀ = 1`, `d₁ = 0`, `d₂ = 2n+1`, `κ = 2n` -/

/-- The connected subgroups of `G_a × G_ℓ` by type (the paper's table in Step 3, with types C and E split by
subcase). `b = dim B`. -/
inductive MXType
  | A (b : ℕ)          -- `G_a × π⁻¹(B)`, image `ℂ²`
  | B (b : ℕ)          -- `G_a × s(B)`, needs `φ(S) = 0` (so `b ≤ n`), image `ℂ(1,0)`
  | C1 (b : ℕ)         -- `0 × π⁻¹(B)` with `ψ(S) = 0` (so `b ≤ n`), image `ℂ(0,1)`
  | C2 (b : ℕ)         -- `0 × π⁻¹(B)` with `ψ(S) ≠ 0`, image `ℂ²`
  | D (b : ℕ)          -- `0 × s(B)`, needs `φ(S) = 0`; `b = 0` is `G' = 0`
  | E0                 -- graph `{(μσ, σ)}` over the fibre, image `ℂ(μ,1)`
  | E (b : ℕ)          -- graph over `s(B) × G_a`, `b ≥ 1`, image `ℂ²`

namespace MXType

/-- Admissibility: the constraints supplied by Lemma K and `G' ≠ G''`. -/
def Valid (n : ℕ) : MXType → Prop
  | A b => b + 2 < 2 * n + 2
  | B b => b ≤ n
  | C1 b => b ≤ n
  | C2 b => b + 1 < 2 * n + 2
  | D b => b ≤ n
  | E0 => True
  | E b => 1 ≤ b ∧ b ≤ n

def dim : MXType → ℕ
  | A b => b + 2 | B b => b + 1 | C1 b => b + 1 | C2 b => b + 1 | D b => b | E0 => 1 | E b => b + 1

/-- `δ₀ = 0` iff `π₀(G') = G_a` (types A, B, E). -/
def delta0 : MXType → ℕ
  | A _ => 0 | B _ => 0 | C1 _ => 1 | C2 _ => 1 | D _ => 1 | E0 => 0 | E _ => 0

/-- `r = dim Ψ''(T_{G'})`. -/
def r : MXType → ℕ
  | A _ => 2 | B _ => 1 | C1 _ => 1 | C2 _ => 2 | D b => if b = 0 then 0 else 1 | E0 => 1 | E _ => 2

/-- Lower bound for `λ` (Lemma L gives `λ = n` when the image is `0`, `ℂ(1,0)` or `ℂ(0,1)`;
no bound is used otherwise). -/
def lam (n : ℕ) : MXType → ℕ
  | B _ => n | C1 _ => n | D _ => n | _ => 0

/-- `λ + δ₁ + 2δ₂` with `δ₁ = 0`, `δ₂ = δ − δ₀`, `δ = 2n + 2 − dim G'`. -/
def lhs (n : ℕ) (g : MXType) : ℕ := lam n g + 2 * ((2 * n + 2 - dim g) - delta0 g)

end MXType

/-- **No obstruction for Theorem MX once `n ≥ 3`** (`d − N = 1`, weight `2(2n+1) − 2n = 2n+2`). -/
theorem mx_no_obstruction (n : ℕ) (hn : 3 ≤ n) (g : MXType) (hg : g.Valid n) :
    ¬ Obstruction (g.lhs n) 1 (2 * n + 2) g.r := by
  rintro ⟨hr, hle⟩
  cases g with
  | A b => simp [MXType.r] at hr
  | B b => simp only [MXType.Valid] at hg; simp only [MXType.lhs, MXType.lam, MXType.dim,
      MXType.delta0, MXType.r] at hle; omega
  | C1 b => simp only [MXType.Valid] at hg; simp only [MXType.lhs, MXType.lam, MXType.dim,
      MXType.delta0, MXType.r] at hle; omega
  | C2 b => simp [MXType.r] at hr
  | D b =>
    simp only [MXType.Valid] at hg
    by_cases hb : b = 0
    · subst hb; simp only [MXType.lhs, MXType.lam, MXType.dim, MXType.delta0, MXType.r] at hle
      simp at hle; omega
    · simp only [MXType.lhs, MXType.lam, MXType.dim, MXType.delta0, MXType.r, hb] at hle
      simp at hle; omega
  | E0 => simp only [MXType.lhs, MXType.lam, MXType.dim, MXType.delta0, MXType.r] at hle; omega
  | E b => simp [MXType.r] at hr

/-- At `n = 2` the trivial subgroup *is* an obstruction (the count needs `n ≥ 3`). -/
theorem mx_obstruction_n2 : Obstruction ((MXType.D 0).lhs 2) 1 (2 * 2 + 2) (MXType.D 0).r := by
  unfold Obstruction; decide

/-! ## Theorem MG: `G'' = G_m^{2n} × A''`, `n = 2m`, `d₀ = 0`, `d₁ = 2n`, `d₂ = m`, `κ = n` -/

/-- Connected subgroups `T_L × B` of `G_m^{2n} × A''`, grouped by `Ψ''(T_{G'})`. `l = dim L`,
`b = dim B ≤ m`. -/
inductive MGType
  | zero               -- `G' = 0`
  | axis (l b : ℕ)     -- image `ℂ(0,1)`: `B ≠ 0` or `L` in the second block, `l ≤ n`
  | line (l : ℕ)       -- `B = 0`, image a line `ℂ(p,q) ≠ ℂ(0,1)`, `l ≤ n`
  | full               -- image `ℂ²`

namespace MGType

def Valid (m : ℕ) : MGType → Prop
  | zero => True
  | axis l b => l ≤ 2 * m ∧ b ≤ m
  | line l => l ≤ 2 * m
  | full => True

def r : MGType → ℕ
  | zero => 0 | axis _ _ => 1 | line _ => 1 | full => 2

/-- `λ + δ₁ + 2δ₂` with the λ-bounds of the paper: `λ = 2n` (zero), `λ ≥ 2n` (axis),
`λ ≥ n` (line); `δ₁ = 2n − l`, `δ₂ = m − b`. -/
def lhs (m : ℕ) : MGType → ℕ
  | zero => 4 * m + 4 * m + 2 * m
  | axis l b => 4 * m + (4 * m - l) + 2 * (m - b)
  | line l => 2 * m + (4 * m - l) + 2 * m
  | full => 0

end MGType

/-- **No obstruction for Theorem MG**, for every `n = 2m ≥ 2` (`d − N = 1`, weight
`d₁ + 2d₂ − κ = 4m + 2m − 2m = 4m`). -/
theorem mg_no_obstruction (m : ℕ) (hm : 1 ≤ m) (g : MGType) (hg : g.Valid m) :
    ¬ Obstruction (g.lhs m) 1 (4 * m) g.r := by
  rintro ⟨hr, hle⟩
  cases g with
  | zero => simp only [MGType.lhs, MGType.r] at hle; omega
  | axis l b => simp only [MGType.Valid] at hg; simp only [MGType.lhs, MGType.r] at hle; omega
  | line l => simp only [MGType.Valid] at hg; simp only [MGType.lhs, MGType.r] at hle; omega
  | full => simp [MGType.r] at hr

/-! ## Theorem MG♮: `G'' = G_m^{2n} × Q''`, `n = 2m`, `d₂ = m + 1`, `κ = n` -/

/-- Connected subgroups `T_L × H` of `G_m^{2n} × Q''` (`H ∈ {0, F, π⁻¹(B')}`, `h = dim H ≤ m+1`). -/
inductive MGnType
  | zero
  | axis (l h : ℕ)     -- image `ℂ(0,1)`
  | line (l : ℕ)       -- `H = 0`, image a `K`-line `ℂ(1,q)`
  | full

namespace MGnType

def Valid (m : ℕ) : MGnType → Prop
  | zero => True
  | axis l h => l ≤ 2 * m ∧ h ≤ m + 1
  | line l => l ≤ 2 * m
  | full => True

def r : MGnType → ℕ
  | zero => 0 | axis _ _ => 1 | line _ => 1 | full => 2

def lhs (m : ℕ) : MGnType → ℕ
  | zero => 4 * m + 4 * m + 2 * (m + 1)
  | axis l h => 4 * m + (4 * m - l) + 2 * (m + 1 - h)
  | line l => 2 * m + (4 * m - l) + 2 * (m + 1)
  | full => 0

end MGnType

/-- **No obstruction for Theorem MG♮** once `n = 2m ≥ 4` (weight `d₁ + 2d₂ − κ = 2n + 2`). -/
theorem mgn_no_obstruction (m : ℕ) (hm : 2 ≤ m) (g : MGnType) (hg : g.Valid m) :
    ¬ Obstruction (g.lhs m) 1 (4 * m + 2) g.r := by
  rintro ⟨hr, hle⟩
  cases g with
  | zero => simp only [MGnType.lhs, MGnType.r] at hle; omega
  | axis l h => simp only [MGnType.Valid] at hg; simp only [MGnType.lhs, MGnType.r] at hle; omega
  | line l => simp only [MGnType.Valid] at hg; simp only [MGnType.lhs, MGnType.r] at hle; omega
  | full => simp [MGnType.r] at hr

/-- At `n = 2` (`m = 1`) the trivial subgroup is an obstruction for MG♮ (equality `12 ≤ 12`). -/
theorem mgn_obstruction_n2 : Obstruction (MGnType.zero.lhs 1) 1 (4 * 1 + 2) MGnType.zero.r := by
  unfold Obstruction; decide

end CM4E.CaseCheck
