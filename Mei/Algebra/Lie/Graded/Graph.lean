/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Graph
public import Mei.Algebra.Lie.Graded.PositiveDegreeHom

/-!
# Lie gradings on graphs of degrees

Reindexing a Lie grading by the graph of an additive map preserves the graded
bracket. The graph positive degree data read order from the retained coordinate,
so the regraded Lie algebra has exactly the same degree ideals. Identity Lie maps
in both directions are graded along graph inclusion and projection. Thus the
existing truncation and completed-map constructions apply to this regrading.
-/

public section

namespace Mei

variable {N M R L : Type*} [AddCommMonoid N] [AddCommMonoid M]
  [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : N → Submodule R L) (f : N →+ M)

/-- The graph reindexing of a Lie grading respects the bracket. -/
instance instGradedBracketGraphGrading [SetLike.GradedBracket ℒ ℒ] :
    SetLike.GradedBracket (graphGrading ℒ f) (graphGrading ℒ f) where
  bracket_mem := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ x y hx hy
    by_cases hm : m = f n
    · by_cases hm' : m' = f n'
      · subst m m'
        have hxy : ⁅x, y⁆ ∈ ℒ (n + n') := SetLike.GradedBracket.bracket_mem
          ((graphGrading_apply ℒ f n) ▸ hx) ((graphGrading_apply ℒ f n') ▸ hy)
        simpa only [vadd_eq_add, Prod.mk_add_mk, ← map_add, graphGrading_apply] using hxy
      · rw [graphGrading_eq_bot ℒ f hm'] at hy
        rw [((Submodule.mem_bot R).mp hy), lie_zero]
        exact Submodule.zero_mem _
    · rw [graphGrading_eq_bot ℒ f hm] at hx
      rw [((Submodule.mem_bot R).mp hx), zero_lie]
      exact Submodule.zero_mem _

variable (d : PositiveDegrees N)

/-- Identity on the Lie algebra is graded along graph inclusion. -/
def graphGradedLieHom : GradedLieHom (d.graphMap f) ℒ (graphGrading ℒ f) where
  toLieHom := LieHom.id
  map_mem hx := by simpa using hx

@[simp]
theorem graphGradedLieHom_apply (x : L) : graphGradedLieHom ℒ f d x = x := (rfl)

@[simp]
theorem graphGradedLieHom_toLieHom :
    (graphGradedLieHom ℒ f d).toLieHom = LieHom.id := (rfl)

/-- Identity on the Lie algebra is graded along projection from the graph. -/
def graphProjectionGradedLieHom :
    GradedLieHom (d.graphProjection f) (graphGrading ℒ f) ℒ where
  toLieHom := LieHom.id
  map_mem hx := by simpa using graphGrading_le ℒ f _ hx

@[simp]
theorem graphProjectionGradedLieHom_apply (x : L) :
    graphProjectionGradedLieHom ℒ f d x = x := (rfl)

@[simp]
theorem graphProjectionGradedLieHom_toLieHom :
    (graphProjectionGradedLieHom ℒ f d).toLieHom = LieHom.id := (rfl)

variable [DecidableEq N] [DecidableEq M]

/-- Graph reindexing preserves a graded Lie algebra's internal decomposition. -/
noncomputable instance instGradedLieAlgebraGraphGrading [GradedLieAlgebra ℒ] :
    GradedLieAlgebra (graphGrading ℒ f) where

variable [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

/-- Reindexing on graph degrees preserves the actual Lie ideals defining all
nilpotent truncations, at the same cutoff order. -/
@[simp]
theorem degreeIdeal_graphGrading (k : ℕ) :
    (d.graph f).degreeIdeal (graphGrading ℒ f) k = d.degreeIdeal ℒ k := by
  apply LieSubmodule.toSubmodule_injective
  simp

end Mei
