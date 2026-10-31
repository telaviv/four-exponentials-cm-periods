import CM4E
open CM4E

#print axioms CM4E.Gen.frameM_false
#print axioms CM4E.Gen.thmM
#print axioms CM4E.Gen.thmM_I_k
#print axioms CM4E.Gen.m1
#print axioms CM4E.Gen.m3
#print axioms CM4E.Gen.m3'
#print axioms CM4E.Gen.meta_I
#print axioms CM4E.Gen.logE_of_wp
#print axioms CM4E.Gen.logNat_of_logE
#print axioms CM4E.Final.thmM_varpi
#print axioms CM4E.Final.thmM_omegaRho
#print axioms CM4E.Final.thmM_varpi_k
#print axioms CM4E.Final.m1_varpi
#print axioms CM4E.Final.m3_varpi
#print axioms CM4E.Final.m3'_varpi
#print axioms CM4E.Final.meta_varpi
#check @CM4E.Final.thmM_varpi
#check @CM4E.Final.thmM_omegaRho
#check @CM4E.Final.thmM_varpi_k
#check @CM4E.Final.m1_varpi
#check @CM4E.Final.m3_varpi
#check @CM4E.Final.m3'_varpi
#check @CM4E.Final.meta_varpi
#print CM4E.Gen.gmM
#print CM4E.Gen.Thm11KappaM
#print CM4E.Gen.gmFM
-- the model's fields reduce as expected
example (L : CM4E.Gen.CMLattice) {r : ℕ} (b : Fin r → ℂ) :
    (CM4E.Gen.gmM L b).d₁ = 2 * r := by simp [CM4E.Gen.gmM, CM4E.Gen.gmFM]; ring
example (L : CM4E.Gen.CMLattice) {r : ℕ} (b : Fin r → ℂ) :
    (CM4E.Gen.gmM L b).d₂ = Module.finrank ℂ (CM4E.Gen.Qm L b) := rfl
