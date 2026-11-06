/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import CM4E.Bridge.StdVec
import CM4E.Bridge.Transport
import CM4E.Bridge.Std
import CM4E.Bridge.SE
import CM4E.AbVar.SE0
import LSG.W88.V5dMGnK

/-!
# Theorem SE₀ from the vector-extension standard model (one CM curve with `κ₁ = 0`)

* `hyperplaneKappa_gmESV`: the model `gmESV L a₁ a₂ cM` of `G_a × ((E^m)^♮` pushed out along the row `cM`)
  (`CM4E/AbVar/SE0.lean`) is the standard model `gmStdVec 1 0 (fun _ => L.pp) (rowM cM)` (`CM4E/Bridge/StdVec.lean`)
  in other coordinates (`phiV : (z, s₁, s₂) ↦ ((s₁), (), z, (s₂))`), so `lean_lsg`'s `hypStdVecCM` (one CM curve with
  `κ₁ = 0`, `r = 1`) implies `HyperplaneKappa (gmESV L a₁ a₂ cM)` once every nonzero subgroup tangent `H.tan` contains an
  algebraic vector outside `ker Ψ''` (the uniform subgroup condition). Logarithms go through `lean_lsg`'s additive
  subgroup `LSG.AuxV.lamVSub` of `LamV` (addition law for `℘` and `ζ`), using `LSG.W88.V5d.logNat_zeta` (`MX.LogNat` with
  `etaL L` is `Λ(E^♮)` when `κ₁ = 0`); periods use `η(aΩ + bαΩ) = (a + bᾱ)η₀ = etaL L a b` (`eta_lattice`).
* `uniform_SE0`: the condition for the forms of Theorem SE₀ (`aSE1 γ`, `aSE2 γ 0`, fibre row `aSE2 0 γ`). A nonzero vector
  part `Γ ⊂ ℂ × ℂ` (`G_a` and fibre, including the diagonal lines) has an algebraic `(a, s) ≠ 0` with `Ψ'' = (a, s)`.
  Otherwise the abelian part `t` is nonzero; for a nonzero lattice point `λ ∈ t`, `T(B^♮)` contains `(λ/Ω, 0)` and
  `(0, conj(λ/Ω))` (`LSG.CM.fst_mem`, `snd_mem`, for `κ₁ = 0`), algebraic vectors on which
  `Ψ''` is `(μ₁(λ)/Ω, μ₂(λ)/Ω)` and `(0, Σ_j γ_j conj(λ_{b3 j}/Ω))`; if all vanish, the `k`-independence of `γ`
  (`lattice_eq_zero`, applied to `λ_{b1}`, `λ_{b2}` and to the lattice vector `Ω·conj(λ_{b3}/Ω)`) gives `λ = 0`.
* `transcendental_eta_div_omega`: `η₀/Ω ∉ ℚ̄` (the part of Lemma SE0 that SE₀ uses: `η ∉ ℚ̄Ω`). Proof: W88 §5d on
  `E^♮` (`gmStdVec 0 0 (fun _ : Fin 1 => L.pp) 1`) with `V = W = ℂ(1, β)` and `Y = ℚ(Ω, η₀)` (`m = 1 > 0`): `V` would
  contain the tangent space of a nonzero connected subgroup; a nonzero fibre vector `(0, s)` is not in `V`, and
  `T(E^♮) ∋ (Ω, 0)` forces `β = 0`.
* `thmSE0_of_cm`: **Theorem SE₀ for a CM lattice with `κ₁ = 0`**, with no form of W88 assumed (`Ω = L.ω`);
  `thmSE0_paper`: the same for an arbitrary nonzero period `Ω` and `η = η(Ω)` (Theorem 4.12(3) as stated);
  `thmSE0_varpi`: the instance `E = E_i` (`ϖℤ[i]`, `η = π/ϖ`, `t = cπ/ϖ²`), with no hypotheses;
  `transcendental_pi_div_varpi_sq`: `π/ϖ² ∉ ℚ̄`; `thmSE0_varpi_Ltilde`: the corresponding case of Corollary SE4
  (`tu₁, tu₂` not both in `𝓛̃_{E_i}`), under the independence of `ϖ, u₁, u₂`.

Soundness of the model (not checked by Lean): no new model is introduced here. Everything is reduced to the standard
model `gmStdVec` of `CM4E/Bridge/StdVec.lean` (the statement of `lean_lsg`'s Theorem 4.1 for the push-outs of
`(E^m)^♮`, `lean_lsg` `dev/VECEXT.md` §2) and to the soundness of `gmESV`, stated in `CM4E/AbVar/SE0.lean`, whose `sub` field is the
uniform subgroup condition proved here from the subgroup data of `gmStdVec`.
-/

open Complex Module CM4E.Waldschmidt CM4E.Gen CM4E.AbVar CM4E.MX LSG.W88.Vec

namespace CM4E.Bridge

variable {m : ℕ}

/-! ## Coordinates -/

/-- The coordinate isomorphism `T(G_a × G₂) = ℂ^m × ℂ × ℂ ≅ ℂ¹ × ℂ⁰ × ℂ^m × ℂ¹`. -/
noncomputable def phiV (m : ℕ) : TX (Fin m → ℂ) ≃ₗ[ℂ] TanV 1 0 m 1 where
  toFun v := (fun _ => v.2.1, 0, v.1, fun _ => v.2.2)
  invFun w := (w.2.2.1, w.1 0, w.2.2.2 0)
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i; simp
    · simp
    · simp
    · funext i; simp
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext i; simp
    · simp
    · simp
    · funext i; simp
  left_inv v := rfl
  right_inv w := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl ?_))
    · funext i; rw [Subsingleton.elim i 0]
    · exact Subsingleton.elim _ _
    · funext i; rw [Subsingleton.elim i 0]

lemma phiV_apply (v : TX (Fin m → ℂ)) : phiV m v = (fun _ => v.2.1, 0, v.1, fun _ => v.2.2) := rfl

/-- The push-out row `cM` as a `1 × m` matrix. -/
def rowM (cM : Fin m → ℂ) : Matrix (Fin 1) (Fin m) ℂ := Matrix.of fun _ j => cM j

lemma rowM_mulVec (cM z : Fin m → ℂ) (i : Fin 1) : (rowM cM).mulVec z i = ∑ j, cM j * z j := by
  simp [rowM, Matrix.mulVec, dotProduct]

/-! ## CM facts (via `lean_lsg`) -/

/-- `η(aΩ + bαΩ) = (a + bᾱ)η₀` (`κ₁ = 0`). -/
lemma eta_lattice (L : CMLattice) (hκ : KappaOneZero L) (a b : ℤ) :
    LSG.Weierstrass.eta L.pp ((a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂) = etaL L a b := by
  have hd := LSG.W88.V5d.CMLat.cmD (adaptL L) hκ
  have hl : (a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂ ∈ L.pp.lattice := PeriodPair.mem_lattice.mpr ⟨a, b, rfl⟩
  have e1 : LSG.Weierstrass.eta L.pp ((a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂) =
      starRingEnd ℂ (((a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂) / L.pp.ω₁) * LSG.Weierstrass.eta L.pp L.pp.ω₁ :=
    hd.eta_eq_conj hl
  have e2 : LSG.Weierstrass.eta L.pp L.pp.ω₁ = L.η₀ := LSG.W88.V5d.CMLat.eta_one_eq (adaptL L) hκ
  have hω₂ : L.pp.ω₂ = L.α * L.pp.ω₁ := hd.hω
  have hω : L.pp.ω₁ ≠ 0 := hd.ω₁_ne
  rw [e1, e2, etaL, hω₂, show ((a : ℂ) * L.pp.ω₁ + b * (L.α * L.pp.ω₁)) / L.pp.ω₁ = a + b * L.α by field_simp]
  simp [map_add, map_mul]

/-- `ζ(Ω) = η₀` (`κ₁ = 0`). -/
lemma zeta_omega (L : CMLattice) (hκ : KappaOneZero L) : LSG.Weierstrass.zeta L.pp L.ω = L.η₀ := by
  have h := eta_lattice L hκ 1 0
  simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, add_zero, L.hω₁] at h
  rw [LSG.W88.Vec.zeta_of_mem_lattice _ (L.hω₁ ▸ L.pp.ω₁_mem_lattice), h]
  simp [etaL]

/-- `Ω·conj(λ/Ω)` is a lattice point (`ᾱ = α⁻¹`, `α⁻¹Λ = Λ`). -/
lemma conj_div_mem (L : CMLattice) (hκ : KappaOneZero L) {x : ℂ} (hx : x ∈ L.pp.lattice) :
    L.pp.ω₁ * starRingEnd ℂ (x / L.pp.ω₁) ∈ L.pp.lattice := by
  have hd := LSG.W88.V5d.CMLat.cmD (adaptL L) hκ
  obtain ⟨a, b, h⟩ := hd.div_eq hx
  have hc : starRingEnd ℂ L.α = L.α⁻¹ := hd.conj_eq
  have h' : x / L.pp.ω₁ = a + b * L.α := h
  rw [h', map_add, map_mul, map_intCast, map_intCast, hc,
    show L.pp.ω₁ * ((a : ℂ) + b * L.α⁻¹) = (a : ℂ) * L.pp.ω₁ + b * (L.α⁻¹ * L.pp.ω₁) by ring]
  exact add_mem (LSG.Weierstrass.intCast_mul_mem L.pp L.pp.ω₁_mem_lattice a)
    (LSG.Weierstrass.intCast_mul_mem L.pp (hd.unit.inv_mul_mem _ L.pp.ω₁_mem_lattice) b)

/-! ## The model `gmESV` from the standard model -/

/-- **The model `gmESV` from the standard model `gmStdVec 1 0 (fun _ => L.pp) (rowM cM)`**, given the uniform subgroup
condition. -/
theorem hyperplaneKappa_gmESV (L : CMLattice) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) (a₁ a₂ cM : Fin m → ℂ) (hcM : ∀ j, IsAlgebraic ℚ (cM j))
    (huni : ∀ H : SubgroupDataV (d0 := 1) (d1 := 0) (fun _ : Fin m => L.pp) (rowM cM), H.tan ≠ ⊥ →
      ∃ x, phiV m x ∈ H.tan ∧ algX algVF x ∧ PsiX (dotL a₁) (dotL a₂) x ≠ 0) :
    HyperplaneKappa (gmESV L a₁ a₂ cM) := by
  have hLs : ∀ j : Fin m, IsAlgebraic ℚ ((fun _ : Fin m => L.pp) j).g₂ ∧
      IsAlgebraic ℚ ((fun _ : Fin m => L.pp) j).g₃ := fun _ => ⟨hg₂, hg₃⟩
  have hM : AlgMat (rowM cM) := fun _ j => hcM j
  refine hyperplaneKappa_transport (gmESV L a₁ a₂ cM) (gmStdVec 1 0 (fun _ : Fin m => L.pp) (rowM cM)) (phiV m)
    ?_ ?_ ?_ ?_ ?_ (hypStdVec_cm L hκ hg₂ hg₃ 1 0 (rowM cM) le_rfl hM)
  · -- algebraic vectors
    rintro v ⟨h1, h2, h3⟩
    exact ⟨fun _ => h2, fun i => i.elim0, h1, fun _ => h3⟩
  · -- logarithms
    intro v hv
    obtain ⟨D, hD, hDv⟩ := exists_nsmul_mem_closure _ hv
    refine ⟨D, hD, ?_⟩
    have hle : AddSubgroup.closure (lamESV L cM) ≤
        (LSG.AuxV.lamVSub (d0 := 1) (d1 := 0) (fun _ : Fin m => L.pp) (rowM cM) hLs hM).comap
          (phiV m).toLinearMap.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro g (⟨j, u, w, huw, rfl⟩ | ⟨c₁, c₂, h1, h2, rfl⟩)
      · obtain ⟨hu, hw⟩ := LSG.W88.V5d.logNat_zeta (adaptL L) hκ huw
        show phiV m (genV cM j u w) ∈ LamV (fun _ : Fin m => L.pp) (rowM cM)
        refine ⟨fun _ => isAlgebraic_zero, fun i => i.elim0, fun j' => ?_, fun i => ?_⟩
        · show (Pi.single j u : Fin m → ℂ) j' ∈ L.pp.lattice ∨
            IsAlgebraic ℚ (L.pp.weierstrassP ((Pi.single j u : Fin m → ℂ) j'))
          by_cases h : j' = j
          · subst h; rw [Pi.single_eq_same]; exact hu
          · simp only [Pi.single_apply, h, ite_false]; exact Or.inl L.pp.lattice.zero_mem
        · show IsAlgebraic ℚ (cM j * w -
            (rowM cM).mulVec (zetaV (fun _ : Fin m => L.pp) (Pi.single j u)) i)
          rw [rowM_mulVec]
          have e : ∑ k, cM k * zetaV (fun _ : Fin m => L.pp) (Pi.single j u) k =
              cM j * LSG.Weierstrass.zeta L.pp u := by
            rw [Finset.sum_eq_single j]
            · simp [zetaV]
            · intro k _ hk
              simp [zetaV, hk, LSG.W88.Vec.zeta_zero]
            · simp
          rw [e, ← mul_sub]
          exact (hcM j).mul hw
      · show phiV m (((0 : Fin m → ℂ), c₁, c₂) : TX (Fin m → ℂ)) ∈ LamV (fun _ : Fin m => L.pp) (rowM cM)
        refine ⟨fun _ => h1, fun i => i.elim0, fun j' => Or.inl L.pp.lattice.zero_mem, fun i => ?_⟩
        show IsAlgebraic ℚ (c₂ - (rowM cM).mulVec (zetaV (fun _ : Fin m => L.pp) 0) i)
        have : zetaV (fun _ : Fin m => L.pp) (0 : Fin m → ℂ) = 0 :=
          funext fun _ => LSG.W88.Vec.zeta_zero _
        rw [this, Matrix.mulVec_zero]
        simpa using h2
    exact hle hDv
  · -- periods
    intro v hv
    have hle : Submodule.span ℚ (perESV L cM) ≤
        (Submodule.span ℚ (PerV (d0 := 1) (d1 := 0) (fun _ : Fin m => L.pp) (rowM cM) :
          Set (TanV 1 0 m 1))).comap (ratMap (phiV m)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, a, b, rfl⟩
      apply Submodule.subset_span
      rw [ratMap_apply, phiV_apply]
      have hl : (a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂ ∈ L.pp.lattice := PeriodPair.mem_lattice.mpr ⟨a, b, rfl⟩
      refine ⟨by funext i; simp [genV], fun i => i.elim0, fun j' => ?_, ?_⟩
      · show (Pi.single j _ : Fin m → ℂ) j' ∈ L.pp.lattice
        by_cases h : j' = j
        · subst h; simpa using hl
        · simp only [Pi.single_apply, h, ite_false]; exact L.pp.lattice.zero_mem
      · funext i
        show cM j * etaL L a b = (rowM cM).mulVec (etaV (fun _ : Fin m => L.pp) (Pi.single j _)) i
        rw [rowM_mulVec, Finset.sum_eq_single j]
        · simp [etaV, eta_lattice L hκ]
        · intro k _ hk
          simp [etaV, hk, LSG.Weierstrass.eta_zero]
        · simp
    exact hle hv
  · -- subgroups (uniform condition)
    rintro S ⟨H, rfl⟩ hne
    right
    exact huni H hne
  · -- the count
    show 0 + 2 * (m + 1) ≤ 0 + 2 * (finrank ℂ (Fin m → ℂ) + 1)
    simp

/-! ## The uniform subgroup condition for Theorem SE₀ -/

/-- **The uniform subgroup condition for Theorem SE₀** (one CM curve with `κ₁ = 0`). -/
theorem uniform_SE0 (L : CMLattice) (hκ : KappaOneZero L) {r : ℕ} {γ : Fin r → ℂ}
    (hb : IsAdaptedFieldBasis L.α γ)
    (H : SubgroupDataV (d0 := 1) (d1 := 0) (fun _ : Fin (r + r + r) => L.pp) (rowM (aSE2 0 γ)))
    (hH : H.tan ≠ ⊥) :
    ∃ x, phiV _ x ∈ H.tan ∧ algX algVF x ∧ PsiX (dotL (aSE1 γ)) (dotL (aSE2 γ 0)) x ≠ 0 := by
  classical
  by_cases hΓ : H.gam = ⊥
  · -- the abelian part is nonzero
    have ht : H.t ≠ ⊥ := by
      intro ht; apply hH
      rw [SubgroupDataV.tan, hΓ, ht, LSG.W88.V5d.perTan_bot,
        show LSG.W88.torusLie H.U = ⊥ from Subsingleton.elim _ _]
      simp
    have hd := LSG.W88.V5d.CMLat.cmD (adaptL L) hκ
    have hω : L.pp.ω₁ ≠ 0 := hd.ω₁_ne
    obtain ⟨l, ⟨hlt, hl⟩, hl0⟩ : ∃ l ∈ {z | z ∈ H.t ∧ ∀ j, z j ∈ ((fun _ : Fin (r + r + r) => L.pp) j).lattice}, l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply ht
      rw [← LSG.CM.span_lat_eq H.t_ab, Submodule.span_eq_bot]
      exact hcon
    have hl' : ∀ j, l j ∈ L.pp.lattice := hl
    -- `(λ/Ω, 0)` and `(0, conj(λ/Ω))` in `T(B^♮)`
    have hfst : (l, (0 : Fin (r + r + r) → ℂ)) ∈ perTanId (fun _ : Fin (r + r + r) => L.pp) H.t := LSG.CM.fst_mem hd hlt hl
    have hsnd : ((0 : Fin (r + r + r) → ℂ), etaV (fun _ : Fin (r + r + r) => L.pp) l) ∈ perTanId (fun _ : Fin (r + r + r) => L.pp) H.t := LSG.CM.snd_mem hd hlt hl
    set ac : Fin (r + r + r) → ℂ := fun k => starRingEnd ℂ (l k / L.pp.ω₁) with hacdef
    have hη : LSG.Weierstrass.eta L.pp L.pp.ω₁ ≠ 0 := hd.eta_one_ne
    have hac : ((0 : Fin (r + r + r) → ℂ), ac) ∈ perTanId (fun _ : Fin (r + r + r) => L.pp) H.t := by
      have h := Submodule.smul_mem _ (LSG.Weierstrass.eta L.pp L.pp.ω₁)⁻¹ hsnd
      have e : ac = (LSG.Weierstrass.eta L.pp L.pp.ω₁)⁻¹ • etaV (fun _ : Fin (r + r + r) => L.pp) l := funext fun k => by
        have e1 : etaV (fun _ : Fin (r + r + r) => L.pp) l k = starRingEnd ℂ (l k / L.pp.ω₁) * LSG.Weierstrass.eta L.pp L.pp.ω₁ :=
          hd.eta_eq_conj (hl k)
        simp only [hacdef, Pi.smul_apply, smul_eq_mul, e1]
        field_simp
      rw [e]; simpa using h
    have hlo : (L.pp.ω₁⁻¹ • l, (0 : Fin (r + r + r) → ℂ)) ∈ perTanId (fun _ : Fin (r + r + r) => L.pp) H.t := by
      have h := Submodule.smul_mem _ L.pp.ω₁⁻¹ hfst
      simpa using h
    set x₁ : TX (Fin (r + r + r) → ℂ) := (L.pp.ω₁⁻¹ • l, 0, 0)
    set x₂ : TX (Fin (r + r + r) → ℂ) := (0, 0, ∑ j, aSE2 0 γ j * ac j)
    have hx₁ : phiV _ x₁ ∈ H.tan := by
      refine Submodule.mem_sup_right ⟨(L.pp.ω₁⁻¹ • l, 0), ⟨_, hlo, by simp⟩, ?_⟩
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · funext i; simp [g2Incl, x₁, phiV_apply]
      · exact Subsingleton.elim _ _
      · simp [g2Incl, x₁, phiV_apply]
      · funext i; simp [g2Incl, x₁, phiV_apply]
    have hx₂ : phiV _ x₂ ∈ H.tan := by
      refine Submodule.mem_sup_right ⟨(0, (rowM (aSE2 0 γ)).mulVec ac), ⟨_, hac, by simp⟩, ?_⟩
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · funext i; simp [g2Incl, x₂, phiV_apply]
      · exact Subsingleton.elim _ _
      · simp [g2Incl, x₂, phiV_apply]
      · funext i; simp [g2Incl, x₂, phiV_apply, rowM_mulVec]
    have hlalg : ∀ j, IsAlgebraic ℚ (l j / L.pp.ω₁) := fun j => hd.isAlgebraic_div (hl j)
    have hacalg : ∀ j, IsAlgebraic ℚ (ac j) := fun j => LSG.CM.isAlgebraic_conj (hlalg j)
    have hγalg : ∀ j, IsAlgebraic ℚ (aSE2 0 γ j) :=
      forall_blocks (P := fun j => IsAlgebraic ℚ (aSE2 0 γ j)) (fun i => by simp [isAlgebraic_zero])
        (fun i => by simp [isAlgebraic_zero]) (fun i => by simpa using hb.alg i)
    have ha₁ : algX algVF x₁ := by
      refine ⟨fun j => ?_, isAlgebraic_zero, isAlgebraic_zero⟩
      show IsAlgebraic ℚ ((L.pp.ω₁⁻¹ • l) j)
      rw [Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
      exact hlalg j
    have ha₂ : algX algVF x₂ := by
      refine ⟨fun j => isAlgebraic_zero, isAlgebraic_zero, ?_⟩
      show IsAlgebraic ℚ (∑ j, aSE2 0 γ j * ac j)
      rw [← mem_algebraicClosure_iff]
      exact sum_mem fun j _ => mul_mem (mem_algebraicClosure_iff.mpr (hγalg j))
        (mem_algebraicClosure_iff.mpr (hacalg j))
    by_contra hcon
    push Not at hcon
    have e1 := hcon x₁ hx₁ ha₁
    have e2 := hcon x₂ hx₂ ha₂
    rw [PsiX_apply] at e1 e2
    have e11 := congrArg Prod.fst e1
    have e12 := congrArg Prod.snd e1
    have e22 := congrArg Prod.snd e2
    simp only [x₁, x₂, add_zero, map_zero, zero_add, Prod.fst_zero, Prod.snd_zero, map_smul, smul_eq_mul,
      mul_eq_zero, inv_eq_zero, hω, false_or] at e11 e12 e22
    rw [dotL_apply, sum_blocks] at e11 e12
    rw [sum_blocks] at e22
    simp only [aSE1_b1, aSE1_b2, aSE1_b3, aSE2_b1, aSE2_b2, aSE2_b3, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add] at e11 e12 e22
    have z1 := lattice_eq_zero hb (fun i => l (b1 i)) (fun i => hl' _) e11
    have z2 := lattice_eq_zero hb (fun i => l (b2 i)) (fun i => hl' _) e12
    have z3 := lattice_eq_zero hb (fun i => L.pp.ω₁ * ac (b3 i)) (fun i => conj_div_mem L hκ (hl' _)) (by
      rw [← mul_zero L.pp.ω₁, ← e22, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    apply hl0
    funext j
    refine forall_blocks (P := fun j => l j = 0) (fun i => congrFun z1 i) (fun i => congrFun z2 i)
      (fun i => ?_) j
    have h3 := congrFun z3 i
    simp only [Pi.zero_apply, mul_eq_zero, hω, false_or, hacdef, map_eq_zero, div_eq_zero_iff, or_false] at h3
    exact h3
  · -- the vector part is nonzero: an algebraic `(a, s) ≠ 0`
    obtain ⟨w, hwΓ, hwa, hw0⟩ : ∃ w ∈ H.gam, AlgPair w ∧ w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hΓ
      rw [H.gam_rat, Submodule.span_eq_bot]
      exact fun w hw => hcon w hw.1 hw.2
    refine ⟨(0, w.1 0, w.2 0), ?_, ⟨fun _ => isAlgebraic_zero, hwa.1 0, hwa.2 0⟩, ?_⟩
    · refine Submodule.mem_sup_left (Submodule.mem_sup_left ⟨w, hwΓ, ?_⟩)
      refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
      · funext i; rw [Subsingleton.elim i 0]; simp [vecIncl, phiV_apply]
      · simp [vecIncl, phiV_apply]
      · simp [vecIncl, phiV_apply]
      · funext i; rw [Subsingleton.elim i 0]; simp [vecIncl, phiV_apply]
    · rw [PsiX_apply]
      intro h
      apply hw0
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [map_zero, zero_add, Prod.fst_zero, Prod.snd_zero] at h1 h2
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [Subsingleton.elim i 0]; exact h1
      · rw [Subsingleton.elim i 0]; exact h2

/-- **`Thm11KappaSE0 L` for every CM lattice** (from `lean_lsg`'s `hypStdVecCM`). -/
theorem thm11KappaSE0_uncond (L : CMLattice) : Thm11KappaSE0 L := by
  intro hκ hg₂ hg₃ r γ hb
  refine hyperplaneKappa_gmESV L hκ hg₂ hg₃ _ _ _ ?_ (uniform_SE0 L hκ hb)
  exact forall_blocks (P := fun j => IsAlgebraic ℚ (aSE2 0 γ j)) (fun i => by simp [isAlgebraic_zero])
    (fun i => by simp [isAlgebraic_zero]) (fun i => by simpa using hb.alg i)

/-! ## Lemma SE0 (the part used): `η₀/Ω ∉ ℚ̄` -/

/-- **`η₀/Ω` is transcendental** for a CM lattice with `κ₁ = 0` and algebraic invariants (W88 §5d on `E^♮`). -/
theorem transcendental_eta_div_omega (L : CMLattice) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) : Transcendental ℚ (L.η₀ / L.ω) := by
  intro hβ
  set β := L.η₀ / L.ω with hβdef
  have hω := L.ω_ne_zero
  have hη0 : L.η₀ ≠ 0 := by
    intro h
    have := L.legendre
    rw [h, mul_zero, zero_mul] at this
    exact (by simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * (Real.pi : ℂ) * I) ≠ 0) this.symm
  set M₁ : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => 1 with hM₁
  have hS := hypStdVec_cm L hκ hg₂ hg₃ 0 0 M₁ le_rfl (fun _ _ => by simp [M₁, isAlgebraic_one])
  set v₀ : TanV 0 0 1 1 := (0, 0, fun _ => 1, fun _ => β) with hv₀def
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have := congrArg (fun x : TanV 0 0 1 1 => x.2.2.1 0) h
    simp [v₀] at this
  set V := Submodule.span ℂ {v₀} with hVdef
  have hfV : finrank ℂ V = 1 := finrank_span_singleton hv₀
  have hfT : finrank ℂ (TanV 0 0 1 1) = 2 := by simp [TanV, Module.finrank_prod]
  set y : Fin 1 → TanV 0 0 1 1 := fun _ => (0, 0, fun _ => L.ω, fun _ => L.η₀) with hydef
  have hy0 : y 0 ≠ 0 := by
    intro h
    have := congrArg (fun x : TanV 0 0 1 1 => x.2.2.1 0) h
    simp [y] at this
    exact hω this
  have hy : ∀ i, y i = L.ω • v₀ := by
    intro i
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ ?_))
    · funext j; simp [y, v₀]
    · funext j; simp [y, v₀, hβdef]; field_simp
  have hyV : ∀ i, y i ∈ V := fun i => by
    rw [hy i]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hωL : L.ω ∈ L.pp.lattice := L.hω₁ ▸ L.pp.ω₁_mem_lattice
  have hyL : ∀ i, y i ∈ (gmStdVec 0 0 (fun _ : Fin 1 => L.pp) M₁).lam := by
    intro i
    refine ⟨fun k => k.elim0, fun k => k.elim0, fun j => Or.inl hωL, fun k => ?_⟩
    show IsAlgebraic ℚ (L.η₀ - M₁.mulVec (zetaV (fun _ : Fin 1 => L.pp) (fun _ => L.ω)) k)
    have : M₁.mulVec (zetaV (fun _ : Fin 1 => L.pp) (fun _ => L.ω)) k = L.η₀ := by
      simp [M₁, Matrix.mulVec, dotProduct, zetaV, zeta_omega L hκ]
    rw [this, sub_self]
    exact isAlgebraic_zero
  have hfy : finrank ℚ (Submodule.span ℚ (Set.range y)) = 1 := by
    have : Set.range y = {y 0} := by
      ext x; simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨i, hi⟩ => by rw [← hi, Subsingleton.elim i 0], fun h => ⟨0, h.symm⟩⟩
    rw [this]
    exact finrank_span_singleton hy0
  obtain ⟨S, ⟨H, rfl⟩, hne, hle⟩ := hS V V 1 y (by rw [hfV, hfT]) le_rfl
    ⟨{v₀}, by
      rintro v rfl
      exact ⟨fun k => k.elim0, fun k => k.elim0, fun j => by simpa [v₀] using isAlgebraic_one,
        fun j => by simpa [v₀] using hβ⟩, rfl⟩
    (fun i => ⟨hyV i, hyL i⟩)
    (by
      rw [hfy, hfT, hfV]
      show ((1 : ℕ) : ℤ) > ((0 : ℕ) + 2 * ((1 + 1 : ℕ) : ℤ) - _) * (((2 : ℕ) : ℤ) - 1 - ((1 : ℕ) : ℤ))
      simp)
  have hmemV : ∀ x ∈ H.tan, ∃ a : ℂ, a • v₀ = x := fun x hx => Submodule.mem_span_singleton.mp (hle hx)
  by_cases hΓ : H.gam = ⊥
  · have ht : H.t ≠ ⊥ := by
      intro ht; apply hne
      rw [SubgroupDataV.tan, hΓ, ht, LSG.W88.V5d.perTan_bot,
        show LSG.W88.torusLie H.U = ⊥ from Subsingleton.elim _ _]
      simp
    have hd := LSG.W88.V5d.CMLat.cmD (adaptL L) hκ
    obtain ⟨l, ⟨hlt, hl⟩, hl0⟩ : ∃ l ∈ {z | z ∈ H.t ∧ ∀ j, z j ∈ ((fun _ : Fin 1 => L.pp) j).lattice}, l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply ht
      rw [← LSG.CM.span_lat_eq H.t_ab, Submodule.span_eq_bot]
      exact hcon
    have hfst : (l, (0 : Fin 1 → ℂ)) ∈ perTanId (fun _ : Fin 1 => L.pp) H.t := LSG.CM.fst_mem hd hlt hl
    have hx : ((0 : Fin 0 → ℂ), (0 : Fin 0 → ℂ), l, (0 : Fin 1 → ℂ)) ∈ H.tan := by
      refine Submodule.mem_sup_right ⟨(l, 0), ⟨_, hfst, by simp⟩, ?_⟩
      simp [g2Incl]
    obtain ⟨a, ha⟩ := hmemV _ hx
    have f0 := congrArg (fun z : TanV 0 0 1 1 => z.2.2.1 0) ha
    have f1 := congrArg (fun z : TanV 0 0 1 1 => z.2.2.2 0) ha
    simp only [v₀, Prod.smul_mk, Pi.smul_apply, smul_eq_mul, mul_one, Pi.zero_apply] at f0 f1
    rcases mul_eq_zero.mp f1 with h | h
    · apply hl0
      funext j
      rw [Subsingleton.elim j 0, ← f0, h]
      rfl
    · apply hη0
      have : L.η₀ = β * L.ω := by rw [hβdef]; field_simp
      rw [this, h, zero_mul]
  · obtain ⟨w, hwΓ, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hΓ
    obtain ⟨a, ha⟩ := hmemV _ (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨w, hwΓ, rfl⟩))
    have f0 := congrArg (fun z : TanV 0 0 1 1 => z.2.2.1 0) ha
    have f1 := congrArg (fun z : TanV 0 0 1 1 => z.2.2.2 0) ha
    simp only [v₀, Prod.smul_mk, Pi.smul_apply, smul_eq_mul, mul_one] at f0 f1
    simp [vecIncl] at f0 f1
    apply hw0
    refine Prod.ext (funext fun i => i.elim0) (funext fun i => ?_)
    rw [Subsingleton.elim i 0, ← f1, f0, zero_mul]
    rfl

/-! ## Theorem SE₀ -/

/-- **Theorem SE, part (SE₀), for a CM lattice with `κ₁ = 0`** (the paper, Theorem 6.12(3)),
with no form of W88 assumed: if `E_L` has algebraic invariants, `ζ(αz) = ᾱζ(z)`, and complex
multiplication acts on its elliptic logarithms of algebraic points, then for `c ∈ ℚ̄ˣ`, `t = c·η₀/Ω` and
`u₁, u₂ ∈ 𝓛̃_{E_L}` with `Ω, u₁, u₂` linearly independent over `ℚ̄`, the numbers `tu₁, tu₂` are not both in
`ℚ̄𝓛_{E_L} + ℚ̄·Fib_{E_L}`. -/
theorem thmSE0_of_cm (L : CMLattice) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) (hCM : CMMulLogE L) (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0)
    (u₁ u₂ : ℂ) (hu₁ : u₁ ∈ LtildeE L.pp) (hu₂ : u₂ ∈ LtildeE L.pp)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * L.ω + a₁ * u₁ + a₂ * u₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * L.η₀ / L.ω * u₁ ∈ QbarLFib L ∧ c * L.η₀ / L.ω * u₂ ∈ QbarLFib L) := by
  rintro ⟨h1, h2⟩
  refine thmSE0 L (thm11KappaSE0_uncond L) hκ hg₂ hg₃ hCM (transcendental_eta_div_omega L hκ hg₂ hg₃)
    c hc hc0 ![u₁, u₂] (fun j => by fin_cases j; exacts [hu₁, hu₂]) (by simpa using hind)
    (fun j => by fin_cases j; exacts [h1, h2])

/-- **Theorem 4.12(3), paper form**: an arbitrary nonzero period `Ω` of `E_L` and `η = η(Ω)` (`= η*(Ω)` as `κ₁ = 0`):
for `c ∈ ℚ̄ˣ`, `t = cη/Ω` and `u₁, u₂ ∈ 𝓛̃_{E_L}` with `Ω, u₁, u₂` linearly independent over `ℚ̄`, the numbers `tu₁, tu₂`
are not both in `ℚ̄𝓛_{E_L} + ℚ̄·Fib_{E_L}`. -/
theorem thmSE0_paper (L : CMLattice) (hκ : KappaOneZero L) (hg₂ : IsAlgebraic ℚ L.pp.g₂)
    (hg₃ : IsAlgebraic ℚ L.pp.g₃) (hCM : CMMulLogE L) (Ω : ℂ) (hΩ : Ω ∈ L.pp.lattice) (hΩ0 : Ω ≠ 0)
    (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (u₁ u₂ : ℂ) (hu₁ : u₁ ∈ LtildeE L.pp)
    (hu₂ : u₂ ∈ LtildeE L.pp)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * Ω + a₁ * u₁ + a₂ * u₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * LSG.Weierstrass.eta L.pp Ω / Ω * u₁ ∈ QbarLFib L ∧
      c * LSG.Weierstrass.eta L.pp Ω / Ω * u₂ ∈ QbarLFib L) := by
  have hω := L.ω_ne_zero
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp hΩ
  have he : LSG.Weierstrass.eta L.pp ((a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂) = etaL L a b :=
    eta_lattice L hκ a b
  set s : ℂ := (a : ℂ) + b * L.α with hsdef
  have hΩs : (a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂ = s * L.ω := by rw [L.hω₁, L.hω₂, hsdef]; ring
  have hs0 : s ≠ 0 := by
    intro h; apply hΩ0; rw [hΩs, h, zero_mul]
  have hsalg : IsAlgebraic ℚ s := (isAlgebraic_intCast a).add ((isAlgebraic_intCast b).mul L.isAlgebraic_α)
  have hcs : starRingEnd ℂ s = (a : ℂ) + b * starRingEnd ℂ L.α := by simp [hsdef, map_add, map_mul]
  have hcs0 : starRingEnd ℂ s ≠ 0 := by rwa [map_ne_zero]
  have hcsalg : IsAlgebraic ℚ (starRingEnd ℂ s) := LSG.CM.isAlgebraic_conj hsalg
  have e : c * LSG.Weierstrass.eta L.pp ((a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂) /
      ((a : ℂ) * L.pp.ω₁ + b * L.pp.ω₂) = (c * starRingEnd ℂ s / s) * L.η₀ / L.ω := by
    rw [he, hΩs, etaL, ← hcs]
    field_simp
  rw [e]
  refine thmSE0_of_cm L hκ hg₂ hg₃ hCM (c * starRingEnd ℂ s / s) ?_ ?_ u₁ u₂ hu₁ hu₂ ?_
  · rw [← mem_algebraicClosure_iff]
    exact div_mem (mul_mem (mem_algebraicClosure_iff.mpr hc) (mem_algebraicClosure_iff.mpr hcsalg))
      (mem_algebraicClosure_iff.mpr hsalg)
  · exact div_ne_zero (mul_ne_zero hc0 hcs0) hs0
  · intro a₀ a₁ a₂ h0 h1 h2 hrel
    have := hind (a₀ / s) a₁ a₂ (by
      rw [← mem_algebraicClosure_iff]
      exact div_mem (mem_algebraicClosure_iff.mpr h0) (mem_algebraicClosure_iff.mpr hsalg)) h1 h2
      (by rw [← hrel, hΩs]; field_simp)
    refine ⟨?_, this.2⟩
    have h := this.1
    rwa [div_eq_zero_iff, or_iff_left hs0] at h

/-- **`π/ϖ²` is transcendental** (`η₀/Ω` for `ϖℤ[i]`, `η₀ = π/ϖ`). -/
theorem transcendental_pi_div_varpi_sq : Transcendental ℚ ((Real.pi : ℂ) / varpi ^ 2) := by
  have h := transcendental_eta_div_omega latI kappaOneZero_latI Final.hg₂ g₃_lemniscatic_isAlgebraic
  have e : latI.η₀ / latI.ω = (Real.pi : ℂ) / varpi ^ 2 := by
    show (Real.pi : ℂ) / varpi / varpi = _
    rw [div_div, sq]
  rwa [e] at h

/-- **Theorem SE₀ for `E = E_i`** (`ϖℤ[i]`, `η = π/ϖ`), with no hypotheses: for `c ∈ ℚ̄ˣ`, `t = cπ/ϖ²` and
`u₁, u₂ ∈ 𝓛̃_{E_i}` with `ϖ, u₁, u₂` linearly independent over `ℚ̄`, the numbers `tu₁, tu₂` are not both in
`ℚ̄𝓛_{E_i} + ℚ̄·Fib_{E_i}`. -/
theorem thmSE0_varpi (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (u₁ u₂ : ℂ)
    (hu₁ : u₁ ∈ LtildeE lemniscatic) (hu₂ : u₂ ∈ LtildeE lemniscatic)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * varpi + a₁ * u₁ + a₂ * u₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * Real.pi / varpi ^ 2 * u₁ ∈ QbarLFib latI ∧ c * Real.pi / varpi ^ 2 * u₂ ∈ QbarLFib latI) := by
  have e : c * latI.η₀ / latI.ω = c * Real.pi / varpi ^ 2 := by
    show c * ((Real.pi : ℂ) / varpi) / varpi = _
    rw [sq, mul_div_assoc, div_div, mul_div_assoc]
  have h := thmSE0_of_cm latI kappaOneZero_latI Final.hg₂ g₃_lemniscatic_isAlgebraic cmMulLogE_latI c hc hc0
    u₁ u₂ hu₁ hu₂ hind
  rwa [e] at h

/-- **Corollary SE4 at `t = cπ/ϖ²`, assuming `ϖ ∉ ℚ̄u₁ + ℚ̄u₂`**: for `u₁, u₂ ∈ 𝓛̃_{E_i}` with `ϖ, u₁, u₂` linearly
independent over `ℚ̄`, the numbers `tu₁, tu₂` are not both in `𝓛̃_{E_i}`. -/
theorem thmSE0_varpi_Ltilde (c : ℂ) (hc : IsAlgebraic ℚ c) (hc0 : c ≠ 0) (u₁ u₂ : ℂ)
    (hu₁ : u₁ ∈ LtildeE lemniscatic) (hu₂ : u₂ ∈ LtildeE lemniscatic)
    (hind : ∀ a₀ a₁ a₂ : ℂ, IsAlgebraic ℚ a₀ → IsAlgebraic ℚ a₁ → IsAlgebraic ℚ a₂ →
      a₀ * varpi + a₁ * u₁ + a₂ * u₂ = 0 → a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0) :
    ¬ (c * Real.pi / varpi ^ 2 * u₁ ∈ LtildeE lemniscatic ∧ c * Real.pi / varpi ^ 2 * u₂ ∈ LtildeE lemniscatic) :=
  fun ⟨h1, h2⟩ => thmSE0_varpi c hc hc0 u₁ u₂ hu₁ hu₂ hind
    ⟨LtildeE_subset_QbarLFib latI h1, LtildeE_subset_QbarLFib latI h2⟩

end CM4E.Bridge
