/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.BCH

/-!
# Simultaneous-event evaluation as a path evaluation

The weighted evaluation of all finite itineraries of canonical simultaneous wall events
is the common weighted evaluation `pathDecoratedEvaluation` of decorated rays along the
paths of the one-object quiver on the event alphabet, over any finite inventory
containing every path that carries a ray at the endpoint. Every chamber module is the
same shifted finite quotient, and every arrow acts by the truncated BCH action of its
event. The cutoff conditions of the cutoff family hold automatically for these actions.

This identifies the coefficient side of the probe comparison with the common broken-line
construction, by `PositiveDegrees.cutoffDecoratedEvaluation_shiftedBCH_eq_pathDecoratedEvaluation`.
-/

public noncomputable section

open Set Quiver Mei.Convex

namespace Mei.ModuleProbe

universe u

variable {R Λ V E ι : Type*} {Γ : Type} {M L : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup Λ] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) (p : Γ)
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ]
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (B : DirectedDiagram (d := d) h H ι)

omit [IsWallAnnihilating H ℳ] in
/-- Simultaneous-event weighted evaluation is the common weighted evaluation of decorated
rays along the paths of the one-object quiver on the event alphabet, over any finite
inventory exhausting the endpoint fiber. -/
theorem cutoffWallEventEvaluation_eq_pathDecoratedEvaluation (k K : ℕ) (hkK : k ≤ K)
    (a : (d.shiftedQuotientGrading ℳ p k).piece 0) (C : Set V) (Q : V)
    (s : Finset (Path (SingleObj.star (WallEvent (B.active K)))
      (SingleObj.star (WallEvent (B.active K)))))
    (hs : ∀ q, PathDecoratedRay (Q := SingleObj (WallEvent (B.active K)))
      (M := fun _ => (d.shiftedLieFiltration ℒ ℳ p).quotient k) (ι := fun _ => Γ)
      (fun e => wallEventPropagation d ℳ p ℒ H h B k K hkK e)
      (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a (fun _ n => i (ρ (p + n)))
      (fun e => e.normal (B.activeNormal K)) (fun e => e.2)
      (fun e => e.offset (B.activeOffset K)) (fun e => e.support (B.activeSupport K))
      (B.activeSupport K) (fun _ : Unit => singularSupport (B.activeSupport K)) C q Q →
        q ∈ s) :
    cutoffWallEventEvaluation d ℳ p ℒ H h B k K hkK a C Q =
      pathDecoratedEvaluation (Q := SingleObj (WallEvent (B.active K)))
        (M := fun _ => (d.shiftedLieFiltration ℒ ℳ p).quotient k) (ι := fun _ => Γ)
        (fun e => wallEventPropagation d ℳ p ℒ H h B k K hkK e)
        (fun _ => (d.shiftedQuotientGrading ℳ p k).piece) 0 a s (fun _ n => i (ρ (p + n)))
        (fun e => e.normal (B.activeNormal K)) (fun e => e.2)
        (fun e => e.offset (B.activeOffset K)) (fun e => e.support (B.activeSupport K))
        (B.activeSupport K) (fun _ : Unit => singularSupport (B.activeSupport K)) C Q := by
  rw [cutoffWallEventEvaluation_def]
  simp only [wallEventPropagation_def] at hs ⊢
  exact d.cutoffDecoratedEvaluation_shiftedBCH_eq_pathDecoratedEvaluation ℒ ℳ p k
    (fun e => (d.truncationMap ℒ hkK).bchGroupMap (B.wallEventLabel K e)) a
    (fun n => i (ρ (p + n))) (fun e => e.normal (B.activeNormal K))
    (fun e => e.offset (B.activeOffset K)) (fun e => e.2) (fun e => e.support (B.activeSupport K))
    (B.activeSupport K) (fun _ : Unit => singularSupport (B.activeSupport K)) C s hs

end Mei.ModuleProbe
