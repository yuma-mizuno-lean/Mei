/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block
public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion.Dependent
public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion.Truncation

/-!
# Event steps with an inventory chosen by output degree

Each output degree uses the diagram truncated at that degree. These inventories
may differ, but every contributing input has strictly smaller degree. Tagging
the output inventories therefore gives one nilpotent operator on the ambient
cutoff, with the same local finite-sum solution as an ordinary lower-degree step.
-/

public noncomputable section

open TauCeti (DirectedWallSpaces)

open Set Filter Topology Mei.Convex Mei.Convex.WallComplement

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι κ' : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (B : DirectedDiagram (d := d) h H ι)

open Classical in
/-- An event block at the output's geometric cutoff, with the normal-velocity
condition required by its actual incoming cut. -/
def degreeEventBlock (K : ℕ) (n : d.cutoff K)
    (b : WallEvent (B.active (d.degree n.val).toNat)) (m : d.cutoff K)
    (hmn : d.Precedes m.val n.val) : ℳ (p + m.val) →ₗ[R] ℳ (p + n.val) :=
  if b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + n.val))) =
      b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + m.val))) then
    eventBlock d ℳ p ℒ H h B _ _ (Nat.le_refl _)
      b (d.degreeCutoffIndex n) (d.precedingDegreeCutoffIndex n m hmn)
  else 0

open Classical in
/-- The degree-specific block uses the ordinary event coefficient at that degree. -/
theorem degreeEventBlock_def (K : ℕ) (n : d.cutoff K)
    (b : WallEvent (B.active (d.degree n.val).toNat)) (m : d.cutoff K)
    (hmn : d.Precedes m.val n.val) :
    degreeEventBlock d ℳ p ℒ H h B K n b m hmn =
      if b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + n.val))) =
          b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + m.val))) then
        eventBlock d ℳ p ℒ H h B _ _ (Nat.le_refl _)
          b (d.degreeCutoffIndex n) (d.precedingDegreeCutoffIndex n m hmn)
      else 0 := by rfl

/-- The ambient endpoint step assembled from degree-dependent geometric inventories. -/
def degreeEventEndpointStep (K : ℕ)
    (events : (Q : V) → (n : d.cutoff K) →
      Finset (WallEvent (B.active (d.degree n.val).toNat)))
    (point : (n : d.cutoff K) → WallEvent (B.active (d.degree n.val).toNat) →
      V → d.cutoff K → V) :
    Module.End R (PositiveDegrees.ShiftedEndpointFunction d ℳ p V K) :=
  PositiveDegrees.shiftedDependentLowerStep d ℳ p K events
    (degreeEventBlock d ℳ p ℒ H h B K) point

open Classical in
/-- The assembled operator uses only the output degree's events and strictly
preceding inputs, with their event-block normal compatibility condition. -/
theorem degreeEventEndpointStep_apply (K : ℕ)
    (events : (Q : V) → (n : d.cutoff K) →
      Finset (WallEvent (B.active (d.degree n.val).toNat)))
    (point : (n : d.cutoff K) → WallEvent (B.active (d.degree n.val).toNat) →
      V → d.cutoff K → V)
    (F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V K) (Q : V) (n : d.cutoff K) :
    degreeEventEndpointStep d ℳ p ℒ H h B K events point F Q n =
      ∑ b ∈ events Q n, ∑ m : d.cutoff K,
        if hmn : d.Precedes m.val n.val then
          degreeEventBlock d ℳ p ℒ H h B K n b m hmn (F (point n b Q m) m)
        else 0 :=
  PositiveDegrees.shiftedDependentLowerStep_apply d ℳ p K events _ point F Q n

/-- Varying the geometric inventory with the output degree preserves nilpotence. -/
theorem degreeEventEndpointStep_pow_eq_zero (K : ℕ)
    (events : (Q : V) → (n : d.cutoff K) →
      Finset (WallEvent (B.active (d.degree n.val).toNat)))
    (point : (n : d.cutoff K) → WallEvent (B.active (d.degree n.val).toNat) →
      V → d.cutoff K → V) :
    (degreeEventEndpointStep d ℳ p ℒ H h B K events point) ^ (K + 1) = 0 :=
  PositiveDegrees.shiftedDependentLowerStep_pow_eq_zero d ℳ p K events _ point

/-- A row of the assembled operator is precisely the ordinary event step at the
output's degree, applied to the restriction of the same ambient endpoint function.
No higher input can contribute because every nonzero term strictly lowers degree. -/
theorem degreeEventEndpointStep_apply_eq (K : ℕ)
    (events : (Q : V) → (n : d.cutoff K) →
      Finset (WallEvent (B.active (d.degree n.val).toNat)))
    (point : (n : d.cutoff K) → WallEvent (B.active (d.degree n.val).toNat) →
      V → d.cutoff K → V)
    (F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V K) (Q : V) (n : d.cutoff K)
    (hnK : (d.degree n.val).toNat ≤ K) :
    degreeEventEndpointStep d ℳ p ℒ H h B K events point F Q n =
      eventEndpointStep d ℳ p ℒ H h B _ _ (Nat.le_refl _)
        (fun _ _ => events Q n)
        (fun b X _ m => point n b X ⟨m.val, d.cutoff_mono hnK m.property⟩)
        (PositiveDegrees.shiftedEndpointRestrict d ℳ p hnK F) Q (d.degreeCutoffIndex n) := by
  classical
  rw [degreeEventEndpointStep_apply, eventEndpointStep_apply]
  apply Finset.sum_congr rfl
  intro b _
  symm
  apply Fintype.sum_of_injective
    (fun m : d.cutoff (d.degree n.val).toNat =>
      (⟨m.val, d.cutoff_mono hnK m.property⟩ : d.cutoff K))
    (fun m m' he => Subtype.ext (congrArg (fun m : d.cutoff K => m.val) he))
  · intro m hm
    have hnot : ¬ d.Precedes m.val n.val := by
      intro hmn
      apply hm
      exact ⟨d.precedingDegreeCutoffIndex n m hmn, Subtype.ext rfl⟩
    simp only [hnot, ↓reduceDIte]
  · intro m
    by_cases hmn : d.Precedes m.val n.val
    · simp only [PositiveDegrees.degreeCutoffIndex, hmn, ↓reduceDIte, degreeEventBlock_def,
        PositiveDegrees.precedingDegreeCutoffIndex, PositiveDegrees.shiftedEndpointRestrict_apply]
    · simp only [hmn, ↓reduceDIte]

/-- A local recurrence assembled from the degree-specific event inventories has
a finite-sum solution whenever nonzero compatible lower-degree blocks read in their domains.
Zero blocks impose no condition on the input point. -/
theorem eqOn_degreeEventEndpointStep_finiteRecursion (K : ℕ)
    (events : (Q : V) → (n : d.cutoff K) →
      Finset (WallEvent (B.active (d.degree n.val).toNat)))
    (point : (n : d.cutoff K) → WallEvent (B.active (d.degree n.val).toNat) →
      V → d.cutoff K → V)
    (Ω : d.cutoff K → Set V)
    (hΩ : ∀ Q n, Q ∈ Ω n → ∀ b ∈ events Q n, ∀ m (hmn : d.Precedes m.val n.val),
      b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + n.val))) =
        b.normal (B.activeNormal (d.degree n.val).toNat) (i (ρ (p + m.val))) →
      degreeEventBlock d ℳ p ℒ H h B K n b m hmn ≠ 0 → point n b Q m ∈ Ω m)
    (a F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V K)
    (hF : ∀ Q n, Q ∈ Ω n → F Q n = a Q n +
      degreeEventEndpointStep d ℳ p ℒ H h B K events point F Q n) :
    ∀ n, EqOn (F · n) ((Module.End.finiteRecursion
      (degreeEventEndpointStep d ℳ p ℒ H h B K events point) (K + 1) a) · n) (Ω n) := by
  classical
  apply PositiveDegrees.eqOn_finiteRecursion_of_shiftedDependentLowerStep_eq_add
    d ℳ p K events (degreeEventBlock d ℳ p ℒ H h B K) point Ω ?_ a F hF
  intro Q n hQ b hb m hmn hblock
  apply hΩ Q n hQ b hb m hmn ?_ hblock
  by_contra hnormal
  exact hblock (by simp only [degreeEventBlock_def, hnormal, ↓reduceIte])

end Mei.ModuleProbe
