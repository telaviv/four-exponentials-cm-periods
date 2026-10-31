import CM4E.AbVar.CorA2

open Complex CM4E.Gen CM4E.AbVar CM4E.Waldschmidt

#print axioms CM4E.AbVar.mgA_K
#print axioms CM4E.AbVar.mgAn_K
#print axioms CM4E.AbVar.corA2
#print axioms CM4E.AbVar.corA2_beta5
#check @CM4E.AbVar.corA2_beta5
#check @CM4E.AbVar.corA2
#check @CM4E.AbVar.mgA_K
#check @CM4E.AbVar.mgAn_K
#print CM4E.AbVar.NotLtildeA
#print CM4E.AbVar.Thm11KappaAK
#print CM4E.AbVar.KSlotA
#print CM4E.AbVar.KFibA

-- (1) with LA = ∅ the model gmAK has the same per, d₁, d₂ as gmA
example (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) (s₀ : Fin g) {r : ℕ} (b : Fin r → ℂ) :
    (gmAK N g κ P s₀ b ∅).per = (gmA N g κ P s₀ b).per ∧ (gmAK N g κ P s₀ b ∅).d₂ = (gmA N g κ P s₀ b).d₂ ∧
    (gmAK N g κ P s₀ b ∅).d₁ = (gmA N g κ P s₀ b).d₁ := ⟨rfl, rfl, rfl⟩

-- (2) with LA = ∅ the logarithm generators coincide with gmA's (`lamGen perAgen`)
example (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) {r : ℕ} :
    lamAK (r := r) N g κ P ∅ = lamGen (perAgen N g κ P) := by
  ext x
  simp only [lamAK, lamGen, perAgen, Set.mem_union, Set.mem_setOf_eq, Set.mem_image, Set.mem_range,
    Set.mem_insert_iff, Set.mem_empty_iff_false, or_false]
  constructor
  · rintro (h | ⟨j, e, v, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨(j, e), rfl⟩, rfl⟩
  · rintro (h | ⟨q, ⟨⟨j, e⟩, rfl⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, e, P, rfl, rfl⟩

-- (3) gmAnK with LAn = ∅: same per, d₂ as gmAn
example (N g : ℕ) (κ : Fin g → ℕ) (P : Fin g → ℂ) (Pb : ℂ) {r : ℕ} (b : Fin r → ℂ) :
    (gmAnK N g κ P Pb b ∅).per = (gmAn N g κ P Pb b).per ∧ (gmAnK N g κ P Pb b ∅).d₂ = (gmAn N g κ P Pb b).d₂ :=
  ⟨rfl, rfl⟩

-- (4) the named input NotLtildeA already implies the Wüstholz input P/π ∉ ℚ̄ (hT is redundant in corA2)
example (P : ℂ) (h : NotLtildeA P) : Transcendental ℚ (P / Real.pi) := by
  intro halg
  apply h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have : P = (P / Real.pi) * Real.pi := by field_simp
  rw [this]
  exact Ltilde_smul halg pi_mem_Ltilde

example (h : NotLtildeA (perA5 0)) : WuestholzA5 := by
  intro halg
  apply h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have : perA5 0 = (perA5 0 / Real.pi) * Real.pi := by field_simp
  rw [this]
  exact Ltilde_smul halg pi_mem_Ltilde
