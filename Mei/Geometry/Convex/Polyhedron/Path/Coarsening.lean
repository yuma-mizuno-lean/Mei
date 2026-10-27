/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Admissible paths under wall covers

Suppose each closed coarse wall is covered by fine walls contained in it with
the same affine span. Singular support can only increase on passing to the
fine family. Consequently every fine admissible path is a coarse admissible
path with exactly the same vertices. Extra fine walls are allowed, as are
repeated coarse walls; neither family needs to be finite or polyhedral.

This is the geometric passage from paths for a subdividing complex to paths
for its original indexed wall supports. It uses the relative-interior
description of singular support and Mathlib's monotonicity of interior in a
fixed affine span. The path construction follows `WallComplement.restrictPrefunctor`.
-/

public section

open Set

namespace Mei.Convex

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {W' : κ → Set V}
  (hclosed : ∀ j, IsClosed (W j))
  (hcover : ∀ j x, x ∈ W j → ∃ a, x ∈ W' a ∧ W' a ⊆ W j ∧
    affineSpan ℝ (W' a) = affineSpan ℝ (W j))

namespace WallComplement

/-- Forget a wall cover's additional cuts without moving vertices or segments.
Every coarse wall is covered by fine pieces with its affine span. -/
def wallCoverPrefunctor : WallComplement W' ⥤q WallComplement W where
  obj x := ⟨x.val, fun j hx => by
    obtain ⟨a, ha, -, -⟩ := hcover j x.val hx
    exact x.notMem a ha⟩
  map {x y} e := ⟨{
    transverse := by
      rintro j ⟨t, ht, hxj⟩
      obtain ⟨a, ha, -, hspan⟩ := hcover j _ hxj
      rw [← hspan]
      exact e.down.transverse a ⟨t, ht, ha⟩
    regular := fun t ht hs => e.down.regular t ht
      (singularSupport_subset_of_wall_cover hclosed hcover hs) }⟩

/-- Forgetting the additional cuts preserves the ambient point of every vertex. -/
@[simp]
theorem wallCoverPrefunctor_obj_val (x : WallComplement W') :
    ((wallCoverPrefunctor hclosed hcover).obj x).val = x.val := (rfl)

instance : (wallCoverPrefunctor hclosed hcover).MapReverse where
  map_reverse' _ := rfl

end WallComplement

end Mei.Convex
