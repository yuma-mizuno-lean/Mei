/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek V4.1 Flash
-/
module

public import Mei.Geometry.ScatteringDiagram.ModuleProbe.WallEventEvaluation
public import Mei.Algebra.Lie.Filtered.Adapted

/-!
# The backward part of simultaneous wall-event propagation

The canonical simultaneous wall-event propagation of
`Mei.ModuleProbe.WallEventEvaluation` is the truncated BCH action of the event label.
By `Mei.ModuleFiltration.truncatedBCHAction_isAdapted` it is the identity plus a
filtration-raising endomorphism, and its backward operator `1 - propagation` is
nilpotent after `k + 1` steps at coefficient order `k`.

The generic raising/recursion theory supplies its backward operator and geometric
series without duplicating those consequences for each event. No hidden infinite
iteration or arbitrary choice of a proof witness is introduced by naming another wrapper.

Nothing here assumes commutativity of the labels, a nonzero spatial direction, or a
coefficient basis. These are the statements that a last-change decomposition of a
weighted evaluation feeds into.
-/

public noncomputable section

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
  {ρ : Γ →+ Λ} (H : DirectedWallSpaces ρ ℒ) [IsWallAnnihilating H ℳ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  {j : ℤ →+ E} (h' : TauCeti.Toric.IsIntegralLattice j)
  (B : DirectedDiagram (d := d) h H ι)

local notation "A" => d.shiftedLieFiltration ℒ ℳ p

omit [IsWallAnnihilating H ℳ] in
/-- A single simultaneous wall event is the identity plus a filtration-raising part. -/
theorem wallEventPropagation_isAdapted (k K : ℕ) (hkK : k ≤ K)
    (b : WallEvent (B.active K)) :
    Mei.ModuleFiltration.IsAdapted (F := A) k
      (wallEventPropagation d ℳ p ℒ H h B k K hkK b) := by
  rw [wallEventPropagation_def]
  exact Mei.ModuleFiltration.truncatedBCHAction_isAdapted A d ℒ k _

end Mei.ModuleProbe
