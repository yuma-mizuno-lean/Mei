/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Reconstruction.Completion
public import Mei.Geometry.ScatteringDiagram.KS.Completion.Map

/-!
# Change of coefficients in completed reconstruction

Mapping the reconstructed diagram of a completed BCH element along a
degree-preserving Lie homomorphism gives the reconstructed diagram of the image
element. This holds as an equality of completed diagrams on the same
bounded-degree arrangements, not merely up to equivalence.

The proof assembles the finite identity `PositiveDegrees.map_reconstructFinite`
order by order, using `GradedLieHom.projection_completedMap_of_le` to compute the
projections of the completed map. No injectivity or surjectivity of the coefficient
map is needed. The reconstruction is that of Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §3.4,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416).
-/

public section

noncomputable section

universe u

namespace Mei.PositiveDegrees

variable {N V R : Type*} {L L' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)
  [CommRing R] [Algebra ℚ R] [DecidableEq N]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]

/-- Completed reconstruction commutes with degree-preserving coefficient changes. -/
@[simp]
theorem mapDiagram_reconstruct (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)
    (g : d.completedBCHGroup ℒ) :
    (d.reconstruct h ℒ g).mapDiagram f = d.reconstruct h ℳ (f.completedMap g) := by
  apply CompletedDiagram.ext
  funext k
  rw [CompletedDiagram.mapDiagram_diagram, reconstruct_diagram, reconstruct_diagram,
    f.projection_completedMap_of_le k (a := k) (by simp)]
  exact d.map_reconstructFinite h ℒ ℳ f (CompletedGroup.projection k g)

end Mei.PositiveDegrees
