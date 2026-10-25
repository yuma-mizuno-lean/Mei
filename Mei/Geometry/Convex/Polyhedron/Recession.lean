/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Recession
public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Recession cones of polyhedra

The recession cone of a convex polyhedron is again polyhedral. For nonempty
presentations its inequalities are the linear parts of the original rows;
the empty case gives the whole ambient space.
-/

public section

open Set

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The homogeneous inequalities for a finite affine family are themselves a
convex polyhedron. -/
theorem isConvexPolyhedron_recessionCone_setOf_forall {ι : Type*} [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) (hP : {x : V | ∀ i, g i x ≤ 0}.Nonempty) :
    TauCeti.IsConvexPolyhedron (recessionCone {x : V | ∀ i, g i x ≤ 0} : Set V) := by
  have he := recessionCone_setOf_forall_eq (fun i => (g i).toAffineMap) hP
  simp only [ContinuousAffineMap.coe_toAffineMap] at he
  rw [he]
  simpa only [ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousAffineMap.coe_contLinear]
    using TauCeti.isConvexPolyhedron_setOf_forall
      (fun i => (g i).contLinear.toContinuousAffineMap)

/-- Every convex polyhedron has a convex polyhedral recession cone. The empty
case has recession cone equal to the whole space. -/
theorem isConvexPolyhedron_recessionCone {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    TauCeti.IsConvexPolyhedron (recessionCone P : Set V) := by
  rcases P.eq_empty_or_nonempty with h | hne
  · subst P
    rw [recessionCone_empty]
    exact TauCeti.isConvexPolyhedron_univ
  · obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
    exact isConvexPolyhedron_recessionCone_setOf_forall g hne

end Mei.Convex
