/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational

/-!
# Rational-normal closed half-spaces

A closed half-space `{x | ℓ x ≤ b}` whose bounding functional `ℓ` is a rational multiple of a
lattice character, with an arbitrary real offset `b`, is a rational-normal polyhedron. It is the
basic building block for explicit planar cells.
-/

public section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- A closed half-space `{x | ℓ x ≤ b}` bounded by a hyperplane with rational normal is a
rational-normal polyhedron, for any real offset `b`. -/
theorem isRationalNormalPolyhedron_setOf_le {h : TauCeti.Toric.IsIntegralLattice i}
    (ℓ : V →L[ℝ] ℝ) (hℓ : Toric.IsRationalFunctional h ℓ.toLinearMap) (b : ℝ) :
    IsRationalNormalPolyhedron h {x | ℓ x ≤ b} := by
  let g : V →ᴬ[ℝ] ℝ := ℓ.toContinuousAffineMap - ContinuousAffineMap.const ℝ V b
  have hg : g.toAffineMap.linear = ℓ.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    simpa [g] using AffineMap.linear_apply_vsub g.toAffineMap v 0
  convert isRationalNormalPolyhedron_setOf_forall (h := h) (ι := Unit) (fun _ => g)
    (fun _ => hg ▸ hℓ) using 1
  ext x
  simp [g]

end Mei
