import CM4E.Bridge.Results
open CM4E.Bridge
#print axioms CM4E.Bridge.hyperplaneKappa_transport
#print axioms CM4E.Bridge.hypStdCM_of_hypStd
#print axioms CM4E.Bridge.ker_E0
#print axioms CM4E.Bridge.phiE
#print axioms CM4E.Bridge.comap_phiT_torusLie
#print axioms CM4E.Bridge.thm11KappaMG_of_std
#print axioms CM4E.Bridge.thm11KappaSMG_of_std
#print axioms CM4E.Bridge.int_I
#print axioms CM4E.Bridge.int_rho
#print axioms CM4E.Bridge.fourExpAt_varpi_div_pi_all
#print axioms CM4E.Bridge.fourExpAt_omegaRho_div_pi_all
#print axioms CM4E.Bridge.mg1_varpi
#print axioms CM4E.Bridge.mg3_varpi
#check @CM4E.Bridge.HypStd
#print CM4E.Bridge.HypStdCM
#print CM4E.Gen.latI
#print CM4E.Gen.latRho
example : CM4E.Gen.latI.pp = CM4E.lemniscatic := rfl
-- sanity: Results' statements coincide with Final's (up to the hypothesis)
example (hS : HypStdCM CM4E.lemniscatic) : ∀ c : ℂ, IsAlgebraic ℚ c → c ≠ 0 → CM4E.FourExpAt (c * CM4E.varpi / Real.pi) :=
  fourExpAt_varpi_div_pi_all hS
