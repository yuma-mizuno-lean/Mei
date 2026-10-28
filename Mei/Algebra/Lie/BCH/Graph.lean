/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Graph
public import Mei.Algebra.Lie.BCH.Completion

/-!
# Completed BCH groups under graph regrading

Graph inclusion and projection, acting as identity on the Lie algebra, induce
inverse maps on completed BCH groups. This comparison retains each finite cutoff
and commutes with exponentiation of original Lie elements. It uses
`GradedLieHom.completedMap` and its independence of the choice of degree map.
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {N M R L : Type*} [AddCommMonoid N] [AddCommMonoid M]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N] [DecidableEq M]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L) (f : N →+ M)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Graph reindexing gives a canonical isomorphism of completed BCH groups.
Both directions are induced by identity on the original Lie algebra. -/
def graphBCHGroupEquiv :
    d.completedBCHGroup ℒ ≃* (d.graph f).completedBCHGroup (graphGrading ℒ f) :=
  MonoidHom.toMulEquiv (graphGradedLieHom ℒ f d).completedMap
    (graphProjectionGradedLieHom ℒ f d).completedMap
    (by
      rw [← GradedLieHom.completedMap_comp]
      exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _ (GradedLieHom.id ℒ)
        (by simp)).trans GradedLieHom.completedMap_id)
    (by
      rw [← GradedLieHom.completedMap_comp]
      exact (GradedLieHom.completedMap_eq_of_toLieHom_eq _
        (GradedLieHom.id (graphGrading ℒ f)) (by simp)).trans GradedLieHom.completedMap_id)

/-- The forward comparison is the completed map of graph inclusion. -/
theorem graphBCHGroupEquiv_apply (x : d.completedBCHGroup ℒ) :
    d.graphBCHGroupEquiv ℒ f x = (graphGradedLieHom ℒ f d).completedMap x := (rfl)

/-- The inverse comparison is the completed map of graph projection. -/
theorem graphBCHGroupEquiv_symm_apply
    (x : (d.graph f).completedBCHGroup (graphGrading ℒ f)) :
    (d.graphBCHGroupEquiv ℒ f).symm x =
      (graphProjectionGradedLieHom ℒ f d).completedMap x := (rfl)

/-- Reindexing preserves exponentials of original Lie elements. -/
@[simp]
theorem graphBCHGroupEquiv_expToCompletion (x : L) :
    d.graphBCHGroupEquiv ℒ f (d.expToCompletion ℒ x) =
      (d.graph f).expToCompletion (graphGrading ℒ f) x := by
  rw [graphBCHGroupEquiv_apply, GradedLieHom.completedMap_expToCompletion,
    graphGradedLieHom_apply]

end Mei.PositiveDegrees
