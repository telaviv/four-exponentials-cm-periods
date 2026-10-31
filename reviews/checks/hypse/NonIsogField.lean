import CM4E

/-! Referee check (REFEREE_HYP_SE item 4): for CM lattices, `NonIsog` (both ways) is exactly `k ≠ k'`. -/

open Complex CM4E CM4E.Gen CM4E.AbVar LSG.W88

namespace RefereeSE

/-- If `E_L` and `E_{L'}` are isogenous (`¬ NonIsog`), then `α ∈ ℚ + ℚα'`, i.e. `k ⊆ k'`. -/
theorem sameField_of_not_nonIsog (L L' : CMLattice) (h : ¬ NonIsog L.pp L'.pp) :
    ∃ a b : ℚ, L.α = a + b * L'.α := by
  unfold NonIsog at h
  push Not at h
  obtain ⟨l, hl0, hl⟩ := h
  have hωL : L.ω ∈ L.pp.lattice := L.hω₁ ▸ L.pp.ω₁_mem_lattice
  have hαωL : L.α * L.ω ∈ L.pp.lattice := L.hω₂ ▸ L.pp.ω₂_mem_lattice
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp (hl _ hωL)
  obtain ⟨m', n', hmn'⟩ := PeriodPair.mem_lattice.mp (hl _ hαωL)
  rw [L'.hω₁, L'.hω₂] at hmn hmn'
  have hω' := L'.ω_ne_zero
  have hω := L.ω_ne_zero
  have e : L.α * ((m : ℂ) + n * L'.α) = (m' : ℂ) + n' * L'.α := by
    apply mul_right_cancel₀ hω'
    linear_combination L.α * hmn - hmn'
  have hq := L'.hquad
  set N : ℚ := (m : ℚ) ^ 2 + m * n * L'.q - n ^ 2 * L'.p with hN
  have hN0 : N ≠ 0 := by
    intro h0
    have hprod : ((m : ℂ) + n * L'.α) * ((m : ℂ) + n * L'.q - n * L'.α) = 0 := by
      have : ((N : ℚ) : ℂ) = 0 := by rw [h0]; simp
      rw [hN] at this; push_cast at this
      linear_combination this - (n : ℂ) ^ 2 * hq
    have him := L'.him
    rcases mul_eq_zero.mp hprod with h1 | h1
    · have hi := congrArg Complex.im h1
      simp at hi
      rcases hi with hn | hn
      · subst hn
        have : (m : ℂ) = 0 := by simpa using h1
        have hl' : l * L.ω = 0 := by rw [← hmn, this]; simp
        exact mul_ne_zero hl0 hω hl'
      · linarith
    · have hi := congrArg Complex.im h1
      simp at hi
      rcases hi with hn | hn
      · subst hn
        have : (m : ℂ) = 0 := by simpa using h1
        have hl' : l * L.ω = 0 := by rw [← hmn, this]; simp
        exact mul_ne_zero hl0 hω hl'
      · linarith
  have key : ((N : ℚ) : ℂ) * L.α = (((m' : ℚ) * (m + n * L'.q) - n * n' * L'.p : ℚ) : ℂ) +
      (((n' : ℚ) * (m + n * L'.q) - m' * n - n * n' * L'.q : ℚ) : ℂ) * L'.α := by
    rw [hN]; push_cast
    linear_combination ((m : ℂ) + n * L'.q - n * L'.α) * e + (L.α * (n : ℂ) ^ 2 - n * n') * hq
  have hNc : ((N : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨((m' : ℚ) * (m + n * L'.q) - n * n' * L'.p) / N,
    ((n' : ℚ) * (m + n * L'.q) - m' * n - n * n' * L'.q) / N, ?_⟩
  apply mul_left_cancel₀ hNc
  rw [key, Rat.cast_div, Rat.cast_div]
  generalize ((N : ℚ) : ℂ) = Nc at hNc ⊢
  field_simp

/-- `k ≠ k'` (`α ∉ ℚ + ℚα'`) implies non-isogeny in both directions (with `sameField_of_not_nonIsog`, the two
`NonIsog` hypotheses of `Bridge.thmSE_of_nonIsog` are equivalent to the paper's `k ≠ k'`). -/
theorem nonIsog_of_field (L L' : CMLattice) (h : ¬ ∃ a b : ℚ, L.α = a + b * L'.α) :
    NonIsog L.pp L'.pp ∧ NonIsog L'.pp L.pp := by
  refine ⟨by_contra fun hc => h (sameField_of_not_nonIsog L L' hc), by_contra fun hc => ?_⟩
  obtain ⟨a, b, hab⟩ := sameField_of_not_nonIsog L' L hc
  -- `α' = a + bα`, `b ≠ 0`, so `α = (α' − a)/b`
  have hb : (b : ℂ) ≠ 0 := by
    intro hb0
    have := congrArg Complex.im hab
    rw [hb0] at this
    simp at this
    exact (ne_of_gt L'.him) this
  have hb' : b ≠ 0 := by exact_mod_cast hb
  apply h
  refine ⟨-a / b, 1 / b, ?_⟩
  push_cast
  rw [hab]
  field_simp
  ring


/-- Conversely, `k ⊆ k'` (`α ∈ ℚ + ℚα'`) gives an isogeny `z ↦ (D ω'/ω) z`. -/
theorem not_nonIsog_of_field (L L' : CMLattice) (h : ∃ a b : ℚ, L.α = a + b * L'.α) :
    ¬ NonIsog L.pp L'.pp := by
  obtain ⟨a, b, hab⟩ := h
  have hω := L.ω_ne_zero
  have hω' := L'.ω_ne_zero
  intro hn
  refine hn ((a.den * b.den : ℕ) * L'.ω / L.ω) (by
    refine div_ne_zero (mul_ne_zero ?_ hω') hω
    exact_mod_cast Nat.mul_ne_zero a.den_nz b.den_nz) fun x hx => ?_
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hx
  refine PeriodPair.mem_lattice.mpr ⟨a.den * b.den * m + n * (a.num * b.den), n * (b.num * a.den), ?_⟩
  rw [L.hω₁, L.hω₂, L'.hω₁, L'.hω₂, hab]
  have ha : (a : ℂ) = (a.num : ℂ) / (a.den : ℂ) := by exact_mod_cast (Rat.num_div_den a).symm
  have hb : (b : ℂ) = (b.num : ℂ) / (b.den : ℂ) := by exact_mod_cast (Rat.num_div_den b).symm
  have ha0 : (a.den : ℂ) ≠ 0 := by exact_mod_cast a.den_nz
  have hb0 : (b.den : ℂ) ≠ 0 := by exact_mod_cast b.den_nz
  rw [ha, hb]
  push_cast
  field_simp
  ring

/-- **`NonIsog L L'` iff `k ≠ k'`.** -/
theorem nonIsog_iff (L L' : CMLattice) : NonIsog L.pp L'.pp ↔ ¬ ∃ a b : ℚ, L.α = a + b * L'.α :=
  ⟨fun h hf => not_nonIsog_of_field L L' hf h, fun h => (nonIsog_of_field L L' h).1⟩

lemma alg_mem {x : ℂ} : IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff.symm

/-- A nonzero period of a CM lattice is `(m + nα)ω` with `m + nα` algebraic and nonzero. -/
lemma period_form (L : CMLattice) {Ω : ℂ} (hΩ : Ω ∈ L.pp.lattice) (hΩ0 : Ω ≠ 0) :
    ∃ s : ℂ, IsAlgebraic ℚ s ∧ s ≠ 0 ∧ Ω = s * L.ω := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hΩ
  refine ⟨(m : ℂ) + n * L.α, ?_, ?_, ?_⟩
  · rw [alg_mem]
    exact add_mem (intCast_mem _ m) (mul_mem (intCast_mem _ n) (alg_mem.mp L.isAlgebraic_α))
  · rintro h
    apply hΩ0
    rw [L.hω₁, L.hω₂]
    linear_combination L.ω * h
  · rw [L.hω₁, L.hω₂]; ring

/-- **Theorem 4.12(1), paper form**: `k ≠ k'`, arbitrary nonzero periods `Ω`, `Ω'`. -/
theorem thmSE_paper (L L' : CMLattice) (hg₂ : IsAlgebraic ℚ L.pp.g₂) (hg₃ : IsAlgebraic ℚ L.pp.g₃)
    (hg₂' : IsAlgebraic ℚ L'.pp.g₂) (hg₃' : IsAlgebraic ℚ L'.pp.g₃)
    (hk : ¬ ∃ a b : ℚ, L.α = a + b * L'.α)
    (hCM : Bridge.CMMulLogE L) (hCM' : Bridge.CMMulLogE L')
    (Ω Ω' : ℂ) (hΩ : Ω ∈ L.pp.lattice) (hΩ0 : Ω ≠ 0) (hΩ' : Ω' ∈ L'.pp.lattice) (hΩ'0 : Ω' ≠ 0)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (y₁ y₂ : ℂ) (hy₁ : y₁ ∈ LtildeE L.pp) (hy₂ : y₂ ∈ LtildeE L.pp)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * Ω + a₁ * y₁ + a₂ * y₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * Ω' / Ω * y₁ ∈ LtildeEE L.pp L'.pp ∧ c * Ω' / Ω * y₂ ∈ LtildeEE L.pp L'.pp) := by
  obtain ⟨hni, hni'⟩ := nonIsog_of_field L L' hk
  obtain ⟨s, hs, hs0, rfl⟩ := period_form L hΩ hΩ0
  obtain ⟨s', hs', hs'0, rfl⟩ := period_form L' hΩ' hΩ'0
  have hω := L.ω_ne_zero
  have e : c * (s' * L'.ω) / (s * L.ω) = (c * s' / s) * L'.ω / L.ω := by field_simp
  rw [e]
  refine Bridge.thmSE_of_nonIsog L L' hg₂ hg₃ hg₂' hg₃' hni hni' hCM hCM' (c * s' / s) ?_ ?_ y₁ y₂ hy₁ hy₂ ?_
  · rw [alg_mem]; exact div_mem (mul_mem (alg_mem.mp hc) (alg_mem.mp hs')) (alg_mem.mp hs)
  · exact div_ne_zero (mul_ne_zero hc0 hs'0) hs0
  · intro a₀ a₁ a₂ h0 h1 h2 hrel
    have := hind (a₀ / s) a₁ a₂ (by rw [alg_mem]; exact div_mem (alg_mem.mp h0) (alg_mem.mp hs)) h1 h2
      (by rw [← hrel]; field_simp)
    refine ⟨?_, this.2⟩
    have h := this.1
    rwa [div_eq_zero_iff, or_iff_left hs0] at h

end RefereeSE

#print axioms RefereeSE.sameField_of_not_nonIsog
#print axioms RefereeSE.nonIsog_of_field
#print axioms RefereeSE.not_nonIsog_of_field
#print axioms RefereeSE.nonIsog_iff
#print axioms RefereeSE.thmSE_paper
