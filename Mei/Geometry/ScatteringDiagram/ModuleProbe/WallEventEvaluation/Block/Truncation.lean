/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation.Block
public import Mei.LinearAlgebra.GradedModule.Shifted.EndpointRecursion.Truncation
public import Mei.LinearAlgebra.End.Recursion

/-!
# Cutoff compatibility of the wall-event endpoint operator

The blocks and lower-degree endpoint step of simultaneous wall events commute
with coefficient truncation. The geometric cutoff is held fixed, so every
indexed wall and simultaneous event retains its meaning. Only the coefficient
degrees and the BCH labels are truncated. The event sets and read points on the
smaller coefficient cutoff are restrictions of the original ones.

Consequently the finite nilpotent recursion solutions are compatible even
though their nilpotency bounds differ. This allows degreewise probe and ray
recurrences to be compared on one coefficient quotient. It does not identify
independently chosen geometric event inventories.

We use `PositiveDegrees.labelBlock_truncation`, the restriction theorem for
`shiftedLowerStep`, and `Module.End.comp_finiteRecursion`. The event interpretation
follows Mandel, *Scattering diagrams, theta functions, and refined tropical
curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V ι : Type*} {Γ : Type} {M L : Type u}
  [CommRing R] [Algebra ℚ R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ)
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)

/-- At a fixed geometric cutoff, every retained event block is independent of
the coefficient cutoff. No regular realization of the event is assumed. -/
theorem eventBlock_truncation {k l K : ℕ} (hkl : k ≤ l) (hlK : l ≤ K)
    (b : WallEvent (B.active K)) (n m : d.cutoff k) :
    eventBlock d ℳ p ℒ H h B k K (hkl.trans hlK) b n m =
      eventBlock d ℳ p ℒ H h B l K hlK b
        ⟨n.val, d.cutoff_mono hkl n.property⟩
        ⟨m.val, d.cutoff_mono hkl m.property⟩ := by
  rw [eventBlock_def, eventBlock_def,
    ← PositiveDegrees.labelBlock_truncation d ℳ p ℒ hkl]
  simp only [← MonoidHom.comp_apply, ← LieHom.bchGroupMap_comp,
    d.truncationMap_comp]

/-- Truncating the endpoint step gives the step formed from its retained events
and read points. Higher input degrees contribute zero to retained outputs. -/
theorem shiftedEndpointRestrict_eventEndpointStep {k l K : ℕ} (hkl : k ≤ l)
    (hlK : l ≤ K)
    (events : V → d.cutoff l → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff l) → V)
    (F : PositiveDegrees.ShiftedEndpointFunction d ℳ p V l) :
    d.shiftedEndpointRestrict ℳ p hkl
        (eventEndpointStep d ℳ p ℒ H h B l K hlK events point F) =
      eventEndpointStep d ℳ p ℒ H h B k K (hkl.trans hlK)
        (fun Q n => events Q ⟨n.val, d.cutoff_mono hkl n.property⟩)
        (fun b Q n m => point b Q ⟨n.val, d.cutoff_mono hkl n.property⟩
          ⟨m.val, d.cutoff_mono hkl m.property⟩)
        (d.shiftedEndpointRestrict ℳ p hkl F) := by
  classical
  rw [eventEndpointStep_def,
    PositiveDegrees.shiftedEndpointRestrict_shiftedLowerStep]
  funext Q n
  rw [eventEndpointStep_apply, PositiveDegrees.shiftedLowerStep_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> simp only [eventBlock_truncation d ℳ p ℒ H h B hkl hlK]

/-- The finite recursion solutions commute with coefficient restriction,
using the natural nilpotency bound at each cutoff. The source is any endpoint
function, so this applies before any geometric recursion is established. -/
theorem shiftedEndpointRestrict_eventEndpointStep_finiteRecursion
    {k l K : ℕ} (hkl : k ≤ l) (hlK : l ≤ K)
    (events : V → d.cutoff l → Finset (WallEvent (B.active K)))
    (point : WallEvent (B.active K) → V → (n m : d.cutoff l) → V) :
    (d.shiftedEndpointRestrict (V := V) ℳ p hkl).comp
        (Module.End.finiteRecursion
          (eventEndpointStep d ℳ p ℒ H h B l K hlK events point) (l + 1)) =
      (Module.End.finiteRecursion
        (eventEndpointStep d ℳ p ℒ H h B k K (hkl.trans hlK)
          (fun Q n => events Q ⟨n.val, d.cutoff_mono hkl n.property⟩)
          (fun b Q n m => point b Q ⟨n.val, d.cutoff_mono hkl n.property⟩
            ⟨m.val, d.cutoff_mono hkl m.property⟩)) (k + 1)).comp
        (d.shiftedEndpointRestrict ℳ p hkl) := by
  apply Module.End.comp_finiteRecursion
  · exact LinearMap.ext (shiftedEndpointRestrict_eventEndpointStep
      d ℳ p ℒ H h B hkl hlK events point)
  · exact eventEndpointStep_pow_eq_zero d ℳ p ℒ H h B l K hlK events point
  · exact eventEndpointStep_pow_eq_zero d ℳ p ℒ H h B k K (hkl.trans hlK) _ _

end Mei.ModuleProbe
