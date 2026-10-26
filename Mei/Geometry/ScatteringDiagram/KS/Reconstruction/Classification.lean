/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Completion
public import Mei.Geometry.ScatteringDiagram.KS.Transport

/-!
# Consistent KS diagrams are reconstructions

Over the continuous-dual KS space `KSSpace.continuousDual h`, every consistent completed
KS diagram is equivalent to the middle-factor reconstruction of its transport from the
positive degree point to the negative one, and to the reconstruction of no other
completed BCH element.

Both statements combine the transport criterion
`CompletedDiagram.equivalent_iff_transport_eq`, which holds for an arbitrary KS space,
with `PositiveDegrees.consistent_reconstruct` and `PositiveDegrees.transport_reconstruct`.
This is the classification of consistent diagrams in
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §3,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416).
-/

public section

noncomputable section

namespace Mei

namespace CompletedDiagram

open PositiveDegrees

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {C : ℕ → FinitePolyhedralComplex h.continuousDual}
  (D : CompletedDiagram (KSSpace.continuousDual h) d ℒ C)

/-- A consistent completed diagram is equivalent to the reconstruction of its transport
from the positive degree point to the negative one. -/
theorem equivalent_reconstruct_transport (hD : D.Consistent) :
    D.Equivalent (d.reconstruct h ℒ (D.transport hD D.degreePoint D.negDegreePoint)) := by
  let g := D.transport hD D.degreePoint D.negDegreePoint
  rw [D.equivalent_iff_transport_eq _ hD (d.consistent_reconstruct h ℒ g),
    d.transport_reconstruct h ℒ g]

/-- Every consistent completed diagram is equivalent to the reconstruction of exactly
one completed BCH group element. -/
theorem existsUnique_equivalent_reconstruct (hD : D.Consistent) :
    ∃! g : d.completedBCHGroup ℒ, D.Equivalent (d.reconstruct h ℒ g) := by
  refine ⟨_, D.equivalent_reconstruct_transport hD,
    fun g (hg : D.Equivalent (d.reconstruct h ℒ g)) => ?_⟩
  rw [D.equivalent_iff_transport_eq _ hD (d.consistent_reconstruct h ℒ g),
    d.transport_reconstruct h ℒ g] at hg
  exact hg.symm

end CompletedDiagram

end Mei

