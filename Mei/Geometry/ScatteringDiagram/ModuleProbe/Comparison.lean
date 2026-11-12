/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.WallEvent
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.BackwardRecursion.Coherent
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Source
public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block.Local
public import Mei.LinearAlgebra.GradedModule.Shifted.Finite

/-!
# The probe field equals the actual weighted ray sum

At each finite order, the independently extracted module-probe field
agrees with the weighted sum of actual decorated rays on a common generic
endpoint locus. The incoming source is the whole space. The finite quotient's
homogeneous incoming coefficient must represent the probe's incoming coefficient.

Both geometric recurrences use one fixed active-wall inventory. Their selected
incoming cuts are generic for the preceding degrees. Probe cutoff coherence
identifies their lower inputs, and local nilpotent recursion uniqueness compares
the two solutions. Neither field is defined in terms of the other. The result
retains simultaneous encounters, unchanged-degree encounters and degree changes
in the kernel of the spatial projection; no monomial basis is chosen.

The comparison follows Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5). It uses the existing actual-ray
recurrence, probe transport and far-ray condition, and
`eqOn_of_eventEndpointStep_eq_add` for uniqueness on generic endpoint domains.
-/

open TauCeti (WallComplement)

public noncomputable section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

open Set Filter Topology Mei.Convex TauCeti.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (D₀ : DirectedDiagram (d := d) h H ι) (a : ℳ p)
  (D : DirectedDiagram (d := positiveDegrees d p) (h.prod h')
    (wallSpaces d ℳ p ℒ H) ((ι ⊕ Unit) ⊕ κ))
  (B : DirectedDiagram (d := d) h H κ')

local notation "field" => extendedCoefficientField d ℳ p ℒ H h h' D B
local notation "component" k:max n:max => d.shiftedQuotientComponent ℳ p (p + (n : Γ)) k
  (PositiveDegrees.degree_add_val_sub_self_le d p k n)

/-- The finite probe field equals the actual simultaneous-event weighted ray
sum on the common generic locus of finitely many arrangements. Extra probe
walls carrying the compared charge-one degrees are outgoing, and the homogeneous
finite input represents the same entire incoming coefficient as the probe. No
geometric recursion is assumed. -/
theorem exists_extendedCoefficientField_eq_cutoffWallEventEvaluation
    (hinitial : ∀ c, D.wall (.inl c) =
      (initialDiagram d ℳ p ℒ H h h' D₀ a).wall c)
    (K : ℕ) (hBc : B.LevelConsistent K)
    (hD : D.LevelConsistent (K + 1))
    (hB : (D.map (chargeZeroGradedLieHom d ℳ p ℒ)
      (chargeZeroGradedLieHom_mem_wall d ℳ p ℒ H)).LevelEquivalent
      (cylinderDiagram d ℳ p ℒ H h h' B) K)
    (hout : ∀ n : d.cutoff K, ∀ c, Sum.inr c ∈ D.active (K + 1) →
      (p + n.val, 1) ∈ (D.wall (.inr c)).ray.rayDegrees →
        (D.wall (.inr c)).Outgoing)
    (b : (d.shiftedQuotientGrading ℳ p K).piece 0)
    (hb : d.shiftedQuotientComponent ℳ p p K (by simp only [sub_self, map_zero]; omega)
      b = a) :
    ∃ F : d.cutoff K → ExceptionalArrangement V,
      ∀ Q, (∀ n, (F n).IsGeneric Q) →
        ∃ hQ : ∀ c : B.active K, Q ∉ (B.wall c).support,
          field K hBc ⟨Q, hQ⟩ =
            cutoffWallEventEvaluation d ℳ p ℒ H h B
              K K (Nat.le_refl _) b univ Q := by
  classical
  cases K with
  | zero =>
    obtain ⟨A, hA⟩ := exists_cutoffWallEventEvaluation_leadingComponentArrangement
      d ℳ p ℒ H h B 0
    refine ⟨fun _ => A, fun Q hQ => ⟨fun c =>
      (B.not_mem_active_zero c.val c.property).elim, ?_⟩⟩
    apply d.shiftedQuotient_ext ℳ p
    intro n
    have hn : n.val = 0 := by
      simpa only [d.cutoff_zero, mem_singleton_iff] using n.property
    have hp := shiftedQuotientComponent_extendedCoefficientField_self
      d ℳ p ℒ H h h' D₀ a D B hinitial 0 hD hBc hB
      (fun c hc hdeg => hout n c hc (by rwa [hn, add_zero]))
      ⟨Q, fun c => (B.not_mem_active_zero c.val c.property).elim⟩
    have hr := hA Q (hQ n) 0 (Nat.le_refl _) b
    -- The only retained ambient index is `p`; transport its dependent bound
    -- at the same time to avoid inserting casts into component values.
    generalize_proofs hcut
    generalize hqn : p + n.val = q at hcut ⊢
    have hqp : q = p := by rw [← hqn, hn, add_zero]
    clear hqn
    subst q
    exact hp.trans (hb.symm.trans hr.symm)
  | succ k =>
    let := h.finiteDimensional
    obtain ⟨A, hA⟩ := exists_cutoffWallEventEvaluation_leadingComponentArrangement
      d ℳ p ℒ H h B (k + 1)
    obtain ⟨C, hC⟩ := exists_ray_admissibilityArrangement
      (B.activeSupport (k + 1)) (fun c => (B.wall c).isConvexPolyhedron)
      (fun c => (B.wall c).finrank_direction_add_one) (∅ : Finset V)
    have hallowed (Q : V) (hQ : C.IsGeneric Q) :
        ∀ c : B.active (k + 1), Q ∉ (B.wall c).support := by
      obtain ⟨y, hy, -⟩ := hC Q hQ
      exact hy ▸ y.notMem
    obtain ⟨F, f, hFA, hf, hF⟩ := exists_commonProbeWallEventRecursionDomains
      d ℳ p ℒ H h h' D₀ a D B hinitial k hBc hD hB
      (fun n _ c hc hdeg => hout n c hc hdeg) (A.union C)
    let Ω (n : d.cutoff (k + 1)) := {Q | (F n).IsGeneric Q}
    let P := coherentProbeEndpointFunction d ℳ p ℒ H h h' D B
      (k + 1) (k + 1) (Nat.le_refl _) hBc
    let Θ : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) := fun Q n =>
      (component (k + 1) n) (cutoffWallEventEvaluation d ℳ p ℒ H h B
        (k + 1) (k + 1) (Nat.le_refl _) b univ Q)
    let source : PositiveDegrees.ShiftedEndpointFunction d ℳ p V (k + 1) :=
      fun _ n => (component (k + 1) n) b
    have hallow (Q : V) (n : d.cutoff (k + 1)) (hQ : Q ∈ Ω n) :=
      hallowed Q (ExceptionalArrangement.isGeneric_union.mp (hFA n Q hQ)).2
    -- Coherence replaces every genuine lower-cutoff input by the corresponding
    -- component of the same larger-cutoff field used at the output.
    have hinput (Q : V) (n m : d.cutoff (k + 1)) (hQ : Q ∈ Ω m)
        (hmn : d.Precedes m.val n.val) : f Q m = P Q m := by
      have hmdeg := d.degree_lt_of_precedes hmn
      have hnle := (d.mem_cutoff.mp n.property).2
      have hm : m.val ∈ d.cutoff k := d.mem_cutoff.mpr
        ⟨(d.mem_cutoff.mp m.property).1, by omega⟩
      let m₀ : d.cutoff k := ⟨m.val, hm⟩
      let z : WallComplement (B.activeSupport (k + 1)) := ⟨Q, hallow Q m hQ⟩
      let z₀ := (WallComplement.restrictPrefunctor (B.activeSupport (k + 1))
        (Set.inclusion (B.active_mono (Nat.le_succ k)))).obj z
      have hlow := hf z₀ m₀
      have hhigh := coherentProbeEndpointFunction_eq_component d ℳ p ℒ H h h' D B
        k (k + 1) (Nat.le_succ k) hBc hD hB z m₀
      have hincl := coherentProbeEndpointFunction_cutoff_inclusion d ℳ p ℒ H h h' D B
        (Nat.le_succ k) (Nat.le_refl (k + 1)) hBc Q m₀
      exact hlow.trans (hhigh.symm.trans hincl.symm)
    -- Select actual event cuts on each generic output domain. Outside it, empty
    -- event sets suffice because local uniqueness imposes no equation there.
    have hsteps (Q : V) (n : d.cutoff (k + 1)) :
        ∃ (events : Finset (WallEvent (B.active (k + 1))))
          (point : WallEvent (B.active (k + 1)) → V →
            d.cutoff (k + 1) → d.cutoff (k + 1) → V),
          (Q ∈ Ω n → ∀ c ∈ events, ∀ m, d.Precedes m.val n.val →
            c.normal (B.activeNormal (k + 1)) (i (ρ (p + n.val))) =
              c.normal (B.activeNormal (k + 1)) (i (ρ (p + m.val))) →
            point c Q n m ∈ Ω m) ∧
          (Q ∈ Ω n → P Q n = source Q n +
            eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
              (fun _ _ => events) point P Q n) ∧
          (Q ∈ Ω n → Θ Q n = source Q n +
            eventEndpointStep d ℳ p ℒ H h B (k + 1) (k + 1) (Nat.le_refl _)
              (fun _ _ => events) point Θ Q n) := by
      by_cases hQ : Q ∈ Ω n
      · by_cases hn : n.val = 0
        · refine ⟨∅, fun _ X _ _ => X, by simp, ?_, ?_⟩
          · intro _
            have hp := shiftedQuotientComponent_extendedCoefficientField_self
              d ℳ p ℒ H h h' D₀ a D B hinitial (k + 1) hD hBc hB
              (fun c hc hdeg => hout n c (D.active_mono (by omega) hc)
                (by rwa [hn, add_zero])) ⟨Q, hallow Q n hQ⟩
            dsimp only [P, source]
            rw [coherentProbeEndpointFunction_apply_of_allowed d ℳ p ℒ H h h' D B
              (k + 1) (k + 1) (Nat.le_refl _) hBc Q n (hallow Q n hQ),
              eventEndpointStep_apply]
            simp only [Finset.sum_empty, add_zero]
            -- Generalize the ambient index together with its dependent cutoff
            -- proof; rewriting it inside the subtype alone would insert casts.
            generalize_proofs hcut
            generalize hqn : p + n.val = q at hcut ⊢
            have hqp : q = p := by rw [← hqn, hn, add_zero]
            clear hqn
            subst q
            exact hp.trans hb.symm
          · intro _
            have he := hA Q (ExceptionalArrangement.isGeneric_union.mp
              (hFA n Q hQ)).1 (k + 1) (Nat.le_refl _) b
            dsimp only [Θ, source]
            rw [eventEndpointStep_apply]
            simp only [Finset.sum_empty, add_zero]
            -- As above, transport the degree and its bound simultaneously.
            generalize_proofs hcut
            generalize hqn : p + n.val = q at hcut ⊢
            have hqp : q = p := by rw [← hqn, hn, add_zero]
            clear hqn
            subst q
            exact he
        · obtain ⟨y, hy, hrec⟩ := hF n hn Q hQ
          obtain ⟨T, hT, htail, x, e, hx, he⟩ := hrec.exists
          obtain ⟨η, hη, hp, hr⟩ := he b univ 1 zero_lt_one
          let events := segmentWallEvents (B.activeNormal (k + 1)) e
          let point (c : WallEvent (B.active (k + 1))) (X : V)
              (r m : d.cutoff (k + 1)) := X +
            segmentEventParameter (B.activeNormal (k + 1)) e T c • i (ρ (p + r.val)) +
              η c • i (ρ (p + m.val))
          have hs : source Q n = 0 :=
            d.shiftedQuotientComponent_eq_zero_of_mem ℳ p b.property
              (by simpa only [add_zero, ne_eq, left_eq_add] using hn)
              (PositiveDegrees.degree_add_val_sub_self_le d p (k + 1) n)
          refine ⟨events, point, fun _ c hc m hmn hv => (hη c hc).2.2 m hmn hv, ?_, ?_⟩
          · intro _
            rw [hs, zero_add]
            have houtput : P Q n = (component (k + 1) n) (field (k + 1) hBc y) := by
              dsimp only [P]
              rw [coherentProbeEndpointFunction_apply_of_allowed d ℳ p ℒ H h h' D B
                (k + 1) (k + 1) (Nat.le_refl _) hBc Q n (hallow Q n hQ)]
              congr 1
              exact congrArg (field (k + 1) hBc) (WallComplement.ext hy.symm)
            rw [houtput, hp, eventEndpointStep_apply, eventEndpointStep_apply]
            apply Finset.sum_congr rfl
            intro c hc
            apply Finset.sum_congr rfl
            intro m _
            split_ifs with hmn hv
            · rw [hinput _ n m ((hη c hc).2.2 m hmn hv) hmn]
            · rfl
            · rfl
          · intro _
            simpa only [Θ, hs, zero_add] using hr
      · exact ⟨∅, fun _ X _ _ => X, fun h => (hQ h).elim,
          fun h => (hQ h).elim, fun h => (hQ h).elim⟩
    choose events point hread hprobe hray using hsteps
    let read (c : WallEvent (B.active (k + 1))) (Q : V)
        (n m : d.cutoff (k + 1)) := point Q n c Q n m
    -- Shared local nilpotent uniqueness compares the two independent recurrences.
    have heq := eqOn_of_eventEndpointStep_eq_add d ℳ p ℒ H h B
      (k + 1) (k + 1) (Nat.le_refl _) events read Ω
      (fun Q n hQ c hc m hmn hv _ => hread Q n hQ c hc m hmn hv)
      source source P Θ (fun _ _ _ => rfl)
      (fun Q n hQ => by
        simpa only [eventEndpointStep_apply, read] using hprobe Q n hQ)
      (fun Q n hQ => by
        simpa only [eventEndpointStep_apply, read] using hray Q n hQ)
    let n₀ : d.cutoff (k + 1) :=
      ⟨0, d.mem_cutoff.mpr ⟨zero_mem _, by simp only [map_zero]; omega⟩⟩
    refine ⟨F, fun Q hQ => ⟨hallow Q n₀ (hQ n₀), ?_⟩⟩
    apply d.shiftedQuotient_ext ℳ p
    intro n
    have hn := heq n (hQ n)
    dsimp only [P, Θ] at hn
    rw [coherentProbeEndpointFunction_apply_of_allowed d ℳ p ℒ H h h' D B
      (k + 1) (k + 1) (Nat.le_refl _) hBc Q n (hallow Q n (hQ n))] at hn
    exact hn

end Mei.ModuleProbe
