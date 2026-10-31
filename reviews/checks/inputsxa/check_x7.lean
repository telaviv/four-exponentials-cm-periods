import CM4E.AbVar.X7Gen

/-! Scratch checks for REFEREE_INPUTS_XA.md (not part of the build). -/

open CM4E.AbVar CM4E.Gen

/-- `WuestholzXA (X7S LA).slot` is definitionally `WuestholzBeta7`. -/
example (LA : Set (Fin 3 → ℂ)) : WuestholzXA (X7S LA).slot ↔ WuestholzBeta7 := Iff.rfl

/-- ... and even equal as propositions, by `rfl`. -/
example (LA : Set (Fin 3 → ℂ)) : WuestholzXA (X7S LA).slot = WuestholzBeta7 := rfl

/-- The new split input implies the old level-seven one. -/
example (LA : Set (Fin 3 → ℂ)) (h : WuestholzSplitXA (X7S LA).slot) : WuestholzX7 LA := by
  refine ⟨?_, ?_⟩
  · intro v hv u hu q c c' hq hc hc' hrel
    have hx : v 0 ∈ zQbar ((X7S LA).slot 0) :=
      ⟨1, fun _ => 1, fun _ => v, fun _ => isAlgebraic_one, fun _ => hv, by simp; rfl⟩
    have hx' : u ∈ zQbar ((X7S LA).slot 3) :=
      ⟨1, fun _ => 1, fun _ => fun _ => u, fun _ => isAlgebraic_one,
        fun _ => Set.mem_insert_of_mem _ (show LogE E7 u from hu), by simp⟩
    exact h.1 (v 0) u q c c' hx hx' hq hc hc' hrel
  · intro v hv v' hv' q c c' hq hc hc' hrel
    have hx : v' 2 ∈ zQbar ((X7S LA).slot 2) :=
      ⟨1, fun _ => 1, fun _ => v', fun _ => isAlgebraic_one, fun _ => hv', by simp; rfl⟩
    have hx' : v 1 ∈ zQbar ((X7S LA).slot 1) :=
      ⟨1, fun _ => 1, fun _ => v, fun _ => isAlgebraic_one, fun _ => hv, by simp; rfl⟩
    exact h.2 (v' 2) (v 1) q c c' hx hx' hq hc hc' hrel

/-- A bad `LA` falsifies the split input (vacuity, not unsoundness). -/
example : ¬ WuestholzSplitXA (X7S {fun _ => 1}).slot := by
  intro h
  have hx : (1 : ℂ) ∈ zQbar ((X7S {fun _ => (1 : ℂ)}).slot 0) :=
    ⟨1, fun _ => 1, fun _ => fun _ => 1, fun _ => isAlgebraic_one,
      fun _ => Set.mem_insert_of_mem _ rfl, by simp⟩
  have hx' : (0 : ℂ) ∈ zQbar ((X7S {fun _ => (1 : ℂ)}).slot 3) :=
    ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, by simp⟩
  have := (h.1 1 0 (-1) 0 0 hx hx' isAlgebraic_one.neg isAlgebraic_zero isAlgebraic_zero (by ring)).1
  norm_num at this
