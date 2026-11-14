/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Homogenization

/-!
# Polyhedral homogenization

Homogenizing finitely many affine inequalities produces a convex polyhedron.
For a nonempty base, this is its carrier-defined homogenization, including
when the base is unbounded or has lineality.
-/

public section

open ContinuousAffineMap Set

namespace Mei.Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- In particular the actual homogenization of a nonempty convex polyhedron is
again a convex polyhedron, including for unbounded bases with lineality. -/
theorem isConvexPolyhedron_homogenization {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (hne : P.Nonempty) : TauCeti.IsConvexPolyhedron (homogenization P : Set (V × ℝ)) := by
  obtain ⟨k, g, rfl⟩ := TauCeti.isConvexPolyhedron_iff.mp hP
  rw [homogenization_setOf_forall_eq g hne]
  exact TauCeti.isConvexPolyhedron_homogeneousInequalityCone g

end Mei.Convex
