import CM4E.Final

open CM4E CM4E.Gen CM4E.Waldschmidt

#print axioms CM4E.Gen.frame2_false_K
#print axioms CM4E.Gen.frame2_false
#print axioms CM4E.Gen.mg_K
#print axioms CM4E.Gen.mgn_K
#print axioms CM4E.Final.mg_K_varpi
#print axioms CM4E.Final.mgn_K_varpi

#check @CM4E.Final.mg_K_varpi
#check @CM4E.Final.mgn_K_varpi
#print CM4E.Gen.gmMGK
#print CM4E.Gen.gmMGnK
#print CM4E.Gen.gmF2
#print CM4E.Gen.Thm11KappaMGK
#print CM4E.Gen.Thm11KappaMGnK
#print CM4E.Gen.KLog
#print CM4E.Gen.KLogE
#print CM4E.Gen.KFib
#print CM4E.MX.LogNat
#print CM4E.Gen.LogE

-- the d-fields are what the docstrings say
example (L : CMLattice) {r : ℕ} (b : Fin r → ℂ) : (gmMGK L b).d₁ = 2 * (2 * r) := by
  simp [gmMGK, gmF2]; ring
example (L : CMLattice) {r : ℕ} (b : Fin r → ℂ) : (gmMGK L b).d₂ = Module.finrank ℂ (Qm L b) := rfl
example (L : CMLattice) {r : ℕ} (b : Fin r → ℂ) : (gmMGnK L b).d₂ = Module.finrank ℂ (Qn L b) := rfl
example (L : CMLattice) {r : ℕ} (b : Fin r → ℂ) : (gmMGnK L b).d₁ = 2 * (2 * r) := by
  simp [gmMGnK, gmF2]; ring

-- the per-submodules of the new models coincide with those of gmMG / gmMGn
example (L : CMLattice) {r : ℕ} (b : Fin r → ℂ) : (gmMGK L b).per = (gmMG L b).per := rfl
example (L : CMLattice) {r : ℕ} (b : Fin r → ℂ) : (gmMGnK L b).per = (gmMGn L b).per := rfl

-- etaL for latI is (m - n i) π/ϖ
example (m n : ℤ) : etaL latI m n = ((m : ℂ) - n * Complex.I) * (Real.pi / varpi) := by
  simp [etaL, latI, sub_eq_add_neg]
