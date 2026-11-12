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
and commutes with exponentiation of original Lie elements. At every cutoff the same
two maps are inverse isomorphisms of the finite BCH groups, and the completed
comparison projects to them. It uses `GradedLieHom.completedMap` and its independence
of the choice of degree map.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap IsPositiveGrading)

noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

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

variable {d ℒ} in
/-- Finite maps of modulus at most the identity, induced by graded Lie homomorphisms whose
completed maps compose to the identity, compose to the identity at every cutoff. -/
private theorem bchGroupMap_truncatedMap_comp_eq_id {M' : Type*} [AddCommMonoid M']
    [DecidableEq M'] {e : PositiveDegrees M'} {ℳ : M' → Submodule R L}
    [GradedLieAlgebra ℳ] [IsPositiveGrading e ℳ] {T : PositiveDegreeMap d e}
    {U : PositiveDegreeMap e d} (F : GradedLieHom T ℒ ℳ) (G : GradedLieHom U ℳ ℒ) (k : ℕ)
    (hF : T.modulus k ≤ k) (hG : U.modulus k ≤ k)
    (h : ∀ x, G.completedMap (F.completedMap x) = x) :
    (G.truncatedMap k hG).bchGroupMap.comp (F.truncatedMap k hF).bchGroupMap =
      MonoidHom.id _ := by
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := CompletedGroup.projection_surjective (d.groupTower ℒ)
    (fun n => d.groupTower_map_surjective ℒ (CategoryTheory.homOfLE (Nat.le_succ n)).op) k y
  have hf := F.projection_completedMap_of_le k hF x
  have hg := G.projection_completedMap_of_le k hG (F.completedMap x)
  rw [h] at hg
  -- Both sides are applications of the composite and identity homomorphisms.
  exact (congrArg _ hf.symm).trans hg.symm

/-- At each cutoff, graph reindexing is an isomorphism of finite BCH groups. Both
directions are induced by identity on the original Lie algebra. -/
def graphTruncatedGroupEquiv (k : ℕ) :
    d.truncatedGroup ℒ k ≃* (d.graph f).truncatedGroup (graphGrading ℒ f) k :=
  MonoidHom.toMulEquiv
    ((graphGradedLieHom ℒ f d).truncatedMap k (d.graphMap_modulus f k).le).bchGroupMap
    ((graphProjectionGradedLieHom ℒ f d).truncatedMap k
      (d.graphProjection_modulus f k).le).bchGroupMap
    (bchGroupMap_truncatedMap_comp_eq_id _ _ k _ _ (d.graphBCHGroupEquiv ℒ f).symm_apply_apply)
    (bchGroupMap_truncatedMap_comp_eq_id _ _ k _ _ (d.graphBCHGroupEquiv ℒ f).apply_symm_apply)

/-- The forward finite comparison is the BCH map of truncated graph inclusion. -/
theorem graphTruncatedGroupEquiv_apply (k : ℕ) (y : d.truncatedGroup ℒ k) :
    d.graphTruncatedGroupEquiv ℒ f k y =
      ((graphGradedLieHom ℒ f d).truncatedMap k (d.graphMap_modulus f k).le).bchGroupMap y :=
  (rfl)

/-- The inverse finite comparison is the BCH map of truncated graph projection. -/
theorem graphTruncatedGroupEquiv_symm_apply (k : ℕ)
    (y : (d.graph f).truncatedGroup (graphGrading ℒ f) k) :
    (d.graphTruncatedGroupEquiv ℒ f k).symm y =
      ((graphProjectionGradedLieHom ℒ f d).truncatedMap k
        (d.graphProjection_modulus f k).le).bchGroupMap y :=
  (rfl)

/-- The completed graph comparison projects to the finite graph comparison at every cutoff. -/
@[simp]
theorem projection_graphBCHGroupEquiv (k : ℕ) (x : d.completedBCHGroup ℒ) :
    CompletedGroup.projection k (d.graphBCHGroupEquiv ℒ f x) =
      d.graphTruncatedGroupEquiv ℒ f k (CompletedGroup.projection k x) :=
  (graphGradedLieHom ℒ f d).projection_completedMap_of_le k (d.graphMap_modulus f k).le x

/-- The inverse completed graph comparison projects to the inverse finite graph comparison
at every cutoff. -/
@[simp]
theorem projection_graphBCHGroupEquiv_symm (k : ℕ)
    (x : (d.graph f).completedBCHGroup (graphGrading ℒ f)) :
    CompletedGroup.projection k ((d.graphBCHGroupEquiv ℒ f).symm x) =
      (d.graphTruncatedGroupEquiv ℒ f k).symm (CompletedGroup.projection k x) :=
  (graphProjectionGradedLieHom ℒ f d).projection_completedMap_of_le k
    (d.graphProjection_modulus f k).le x

end TauCeti.PositiveDegrees
