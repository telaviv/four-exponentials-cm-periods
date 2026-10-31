import CM4E

open CM4E.AbVar

#print axioms CM4E.AbVar.XSetup.propX15
#print axioms CM4E.AbVar.XSetup.thmXA
#print axioms CM4E.AbVar.thmX7_of_gen
#print axioms CM4E.AbVar.ch_span
#print axioms CM4E.AbVar.propXA_K
#print axioms CM4E.AbVar.XSetup.propX15_sub
#print axioms CM4E.AbVar.XSetup.propX15_sup

/-- Referee check: `XSetup.Distinct` follows from `WuestholzXA X.slot` (so `hD` is redundant given `hWB`). -/
theorem distinct_of_wuestholz (X : XSetup) (hWB : WuestholzXA X.slot) : X.Distinct := by
  intro j j' hjj' hc hs
  have hper : X.per j = X.per j' := by
    simp only [XSetup.per, XSetup.slot, FKSlot.per]
    have : ∀ (i i' : Fin X.m) (h : i = i') (s : Fin (X.AV i).g) (s' : Fin (X.AV i').g),
        (s : ℕ) = s' → (X.AV i).P s = (X.AV i').P s' := by
      rintro i _ rfl s s' h; rw [Fin.ext h]
    exact this _ _ hc _ _ hs
  -- coefficient vector `e_j - e_j'`
  let a : Fin 4 → ℂ := fun k => (if k = j then 1 else 0) - (if k = j' then 1 else 0)
  have ha : ∀ k, IsAlgebraic ℚ (a k) := fun k => by
    simp only [a]; split_ifs <;> simp [isAlgebraic_zero, isAlgebraic_one, isAlgebraic_one.neg]
  have hsum : (0 : ℂ) + a 0 * (X.slot 0).per + a 1 * (X.slot 1).per + a 2 * (X.slot 2).per +
      a 3 * (X.slot 3).per = 0 := by
    have : ∀ k, (X.slot k).per = X.per k := fun _ => rfl
    simp only [this]
    fin_cases j <;> fin_cases j' <;> simp_all [a] <;> linear_combination hper
  obtain ⟨-, h0, h1, h2, h3⟩ := hWB 0 (a 0) (a 1) (a 2) (a 3) isAlgebraic_zero (ha 0) (ha 1) (ha 2) (ha 3) hsum
  have hj : a j = 0 := by fin_cases j <;> assumption
  simp [a, hjj'] at hj

#print axioms distinct_of_wuestholz
