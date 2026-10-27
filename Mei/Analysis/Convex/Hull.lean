/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mei.Geometry.Affine.Generic

/-!
# Coning a convex hull away from an obstacle

If a convex hull misses a set, adjoining a vertex outside the affine span of
the base and the obstacle preserves disjointness. The obstacle need not be
convex or closed. This gives explicit affine exceptions for choosing cone
vertices while keeping an existing boundary fixed.

The argument uses Mathlib's `convexHull_insert` and the affine line avoidance
lemma `AffineSubspace.lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero`.
-/

public section

open Set

namespace Disjoint

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] {s t : Set V} {z : V}

/-- A vertex outside the affine span of a base and an obstacle cones the base
convex hull without meeting the obstacle. No convexity of the obstacle is required. -/
theorem convexHull_insert_of_notMem_affineSpan
    (hst : Disjoint (convexHull K s) t)
    (hz : z ∉ affineSpan K (s ∪ t)) :
    Disjoint (convexHull K (insert z s)) t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa only [insert_empty_eq, convexHull_singleton, disjoint_singleton_left] using
      (fun ht => hz (subset_affineSpan K _ (Or.inr ht)))
  rw [convexHull_insert hs, convexJoin_comm]
  apply disjoint_left.mpr
  rintro w hw hwt
  obtain ⟨u, hu, z', hz', hwu⟩ := mem_convexJoin.mp hw
  obtain rfl := mem_singleton_iff.mp hz'
  rw [segment_eq_image_lineMap] at hwu
  obtain ⟨a, _, rfl⟩ := hwu
  by_cases ha : a = 0
  · exact disjoint_left.mp hst hu (by simpa only [ha, AffineMap.lineMap_apply_zero] using hwt)
  · let A := affineSpan K (s ∪ t)
    have huA : u ∈ A :=
      (affineSpan_mono K subset_union_left) (convexHull_subset_affineSpan s hu)
    have he : affineSpan K (insert u (A : Set V)) = A := by
      rw [insert_eq_of_mem huA, AffineSubspace.affineSpan_coe]
    exact A.lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero
      (he.symm ▸ hz) ha (subset_affineSpan K _ (Or.inr hwt))

end Disjoint
