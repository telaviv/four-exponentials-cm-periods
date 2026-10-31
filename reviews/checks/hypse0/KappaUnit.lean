import LSG.W88.V5dMGnIso

/-! Referee lemmas for REFEREE_HYP_SE0. -/

open Complex LSG.W88.MStarCopy


-- (`@CM4E.Ext.Weierstrass.eta = @LSG.Weierstrass.eta := rfl` is checked in `EtaRfl.lean`.)

/-- **`κ₁ = 0` forces `j ∈ {0, 1728}`**: for a `CMLattice` `L = Ω(ℤ + ℤα)` with `KappaOneZero L`, the minimal
polynomial of `α` is `X² − qX + 1` with `q ∈ {−1, 0, 1}`, i.e. `α ∈ {ρ = e^{2πi/3}, i, e^{πi/3}}` and `ℤ + ℤα` is
`ℤ[i]` or `ℤ[ρ]`. -/
theorem kappaOneZero_unit (L : CMLattice) (hκ : KappaOneZero L) :
    L.p = -1 ∧ ∃ b : ℤ, (L.q : ℚ) = b ∧ (b = -1 ∨ b = 0 ∨ b = 1) := by
  have hd := LSG.W88.V5d.CMLat.cmD L hκ
  have hconj : starRingEnd ℂ L.α = L.α⁻¹ := hd.conj_eq
  have hα0 : L.α ≠ 0 := by intro h; have := L.him; rw [h] at this; simp at this
  have hnorm : starRingEnd ℂ L.α * L.α = 1 := by rw [hconj, inv_mul_cancel₀ hα0]
  have hy : 0 < L.α.im := L.him
  -- real and imaginary parts
  have hn := congrArg Complex.re hnorm
  simp only [mul_re, conj_re, conj_im, one_re] at hn
  have hq := L.hquad
  have hqre := congrArg Complex.re hq
  have hqim := congrArg Complex.im hq
  simp only [sq, mul_re, mul_im, add_re, add_im, Complex.ratCast_re,
    Complex.ratCast_im] at hqre hqim
  have hq2 : (L.q : ℝ) = 2 * L.α.re := by
    have : ((L.q : ℝ) - 2 * L.α.re) * L.α.im = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hp : (L.p : ℝ) = -1 := by rw [hq2] at hqre; linarith
  refine ⟨by exact_mod_cast hp, ?_⟩
  -- `q ∈ ℤ`: `α · αΩ ∈ Λ`
  have hl : L.α * L.pp.ω₂ ∈ L.pp.lattice := hd.unit.mul_mem _ L.pp.ω₂_mem_lattice
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hl
  have hω : L.ω ≠ 0 := L.hω₁ ▸ hd.ω₁_ne
  have e : ((L.p : ℂ) - a) + ((L.q : ℂ) - b) * L.α = 0 := by
    rw [L.hω₁, L.hω₂] at hab
    apply mul_right_cancel₀ hω
    linear_combination -hab - L.ω * hq
  have ei := congrArg Complex.im e
  simp only [add_im, sub_im, mul_im, sub_re, Complex.ratCast_re, Complex.ratCast_im, intCast_re,
    intCast_im, zero_im] at ei
  have hqb : (L.q : ℝ) = b := by
    have : ((L.q : ℝ) - b) * L.α.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  refine ⟨b, by exact_mod_cast hqb, ?_⟩
  have hre : L.α.re ^ 2 < 1 := by nlinarith
  have hb1 : (b : ℝ) < 2 := by nlinarith
  have hb2 : (-2 : ℝ) < b := by nlinarith
  have : b < 2 := by exact_mod_cast hb1
  have : -2 < b := by exact_mod_cast hb2
  omega

#print axioms kappaOneZero_unit
