import CM4E

open CM4E CM4E.Gen CM4E.Waldschmidt

/-! Kernel check: the copy `CM4E.Bridge.gmStdVec` gives the same `HyperplaneKappa` proposition as lean_lsg's. -/
example (L : CMLattice) (d0 d1 : ℕ) {m r : ℕ} (M : Matrix (Fin r) (Fin m) ℂ) :
    HyperplaneKappa (CM4E.Bridge.gmStdVec d0 d1 (fun _ : Fin m => L.pp) M) ↔
      LSG.W88.MStarCopy.HyperplaneKappa
        (LSG.W88.MStarCopy.gmStdVec d0 d1 (fun _ : Fin m => (CM4E.Bridge.adaptL L).pp) M) := Iff.rfl

example (L : CMLattice) : KappaOneZero L ↔ LSG.W88.MStarCopy.KappaOneZero (CM4E.Bridge.adaptL L) := Iff.rfl

#check @CM4E.Bridge.thmSE0_paper
#check @CM4E.Bridge.thmSE0_varpi
#check @CM4E.Bridge.thmSE0_varpi_Ltilde
#check @CM4E.Bridge.transcendental_eta_div_omega
#check @CM4E.Bridge.transcendental_pi_div_varpi_sq
#check @CM4E.Bridge.thm11KappaSE0_uncond
#check @LSG.W88.hypStdVecCM
#print CM4E.AbVar.FibE
#print CM4E.AbVar.QbarLFib
#print CM4E.AbVar.Thm11KappaSE0

#print axioms CM4E.Bridge.thmSE0_varpi
#print axioms CM4E.Bridge.thmSE0_paper
#print axioms CM4E.Bridge.transcendental_pi_div_varpi_sq
#print axioms CM4E.Bridge.thmSE0_varpi_Ltilde
#print axioms CM4E.Bridge.thmSE0_of_cm
#print axioms CM4E.Bridge.transcendental_eta_div_omega
#print axioms CM4E.Bridge.thm11KappaSE0_uncond
#print axioms CM4E.Bridge.uniform_SE0
#print axioms CM4E.Bridge.hyperplaneKappa_gmESV
#print axioms CM4E.Bridge.hypStdVec_cm
#print axioms CM4E.AbVar.thmSE0
#print axioms CM4E.AbVar.frameX0_false
#print axioms LSG.W88.hypStdVecCM
