/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Homogenization.Inequalities
public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic

/-!
# Polyhedral homogenization

Homogenizing finitely many affine inequalities produces a convex polyhedron.
For a nonempty base, this is its carrier-defined homogenization, including
when the base is unbounded or has lineality.
-/

public section

open ContinuousAffineMap Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Homogeneous inequalities define a closed convex polyhedron when their
index family is finite. -/
theorem isConvexPolyhedron_homogeneousInequalityCone [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) :
    TauCeti.IsConvexPolyhedron (homogeneousInequalityCone g : Set (V × ℝ)) := by
  have hheight : TauCeti.IsConvexPolyhedron {z : V × ℝ | 0 ≤ z.2} := by
    simpa only [ContinuousAffineMap.neg_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
      ContinuousLinearMap.coe_snd', neg_nonpos] using
      TauCeti.isConvexPolyhedron_setOf_le
        (-(ContinuousLinearMap.snd ℝ V ℝ).toContinuousAffineMap)
  have hrows := TauCeti.isConvexPolyhedron_setOf_forall
    (fun i => (homogenizedInequality (g i)).toContinuousAffineMap)
  have he : (homogeneousInequalityCone g : Set (V × ℝ)) =
      {z | 0 ≤ z.2} ∩ {z | ∀ i, (homogenizedInequality (g i)).toContinuousAffineMap z ≤ 0} := by
    ext z
    simp
  rw [he]
  exact hheight.inter hrows

/-- In particular the actual homogenization of a nonempty convex polyhedron is
again a convex polyhedron, including for unbounded bases with lineality. -/
theorem isConvexPolyhedron_homogenization {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (hne : P.Nonempty) : TauCeti.IsConvexPolyhedron (homogenization P : Set (V × ℝ)) := by
  obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  rw [homogenization_setOf_forall_eq g hne]
  exact isConvexPolyhedron_homogeneousInequalityCone g

end Mei.Convex
