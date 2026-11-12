/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pushforward.Consistency
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Uniqueness

/-!
# Outgoing completions under pushforward

Pushforward along a degree-changing graded Lie map with a compatible spatial affine
equivalence preserves outgoingness and consistency. Hence the pushforward of an outgoing
completion is an outgoing completion of the pushed initial walls, even when some labels
die, and every outgoing completion of the pushed initial walls is equivalent to it. The
completions are those of Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, [arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5),
Theorem 2.6.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

open TauCeti (DirectedWallSpaces)

noncomputable section

namespace Mei.DirectedDiagram

universe u

variable {Γ Γ' Λ Λ' R V V' : Type*} {L L' : Type u}
  [AddCommGroup Γ] [AddCommGroup Γ'] [AddCommGroup Λ] [AddCommGroup Λ']
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {ℒ : Γ → Submodule R L} {ℳ : Γ' → Submodule R L'}
  {d : PositiveDegrees Γ} {d' : PositiveDegrees Γ'}
  [DecidableEq Γ] [DecidableEq Γ']
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [GradedLieAlgebra ℳ] [IsPositiveGrading d' ℳ]
  {i : Λ →+ V} {i' : Λ' →+ V'}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {H : DirectedWallSpaces ρ ℒ} {H' : DirectedWallSpaces ρ' ℳ}
  {P : DirectedWall.Pushforward d d' h h' H H'}
  {ι₀ ι' κ' : Type*} {D₀ : ι₀ → DirectedWall (d := d) h H}

/-- The pushforward of an outgoing completion is an outgoing completion of the pushed
initial walls, even when some initial or outgoing labels die. -/
theorem IsOutgoingCompletion.pushforward {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    (hD : IsOutgoingCompletion D₀ D) :
    IsOutgoingCompletion (fun j => (D₀ j).pushforward P) (D.pushforward P) where
  wall_inl j := by rw [pushforward_wall, hD.wall_inl]
  outgoing_inr j := by
    rw [pushforward_wall, DirectedWall.outgoing_pushforward_iff]
    exact hD.outgoing_inr j
  consistent := hD.consistent.pushforward

/-- Outgoing completion commutes with pushforward: every outgoing completion of the pushed
initial walls is equivalent to the pushforward of any outgoing completion of the original
initial walls. -/
theorem IsOutgoingCompletion.equivalent_pushforward
    {D : DirectedDiagram (d := d) h H (ι₀ ⊕ ι')}
    {D' : DirectedDiagram (d := d') h' H' (ι₀ ⊕ κ')} (hD : IsOutgoingCompletion D₀ D)
    (hD' : IsOutgoingCompletion (fun j => (D₀ j).pushforward P) D') :
    D'.Equivalent (D.pushforward P) :=
  outgoingCompletion_unique hD' hD.pushforward

end Mei.DirectedDiagram
