/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Affine transport of admissible polygonal paths

An affine equivalence carries an admissible chain to an admissible chain for the
image wall family, allowing a bijective change of wall indices. Crossing parameters
are unchanged, and singular support and transversality are preserved. No rationality,
closedness, codimension or finiteness assumption on the walls is needed.

The construction uses Mathlib's `AffineSubspace.map_span`, `Submodule.mem_map_equiv`
and `Prefunctor.mapPath`. Finite dimensionality supplies preservation of relative
frontiers by `AffineEquiv.intrinsicFrontier_image`.
-/

public section

open Set

open Mei.Convex

namespace AffineEquiv

variable {V V' ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V]
  (e : V ≃ᵃ[ℝ] V') (f : ι ≃ κ) (W : ι → Set V) (W' : κ → Set V')
  (hW : ∀ j, W' (f j) = e '' W j)

/-- Transport allowed vertices and their actual admissible affine segments. -/
def imagePrefunctor : WallComplement W ⥤q WallComplement W' where
  obj x := ⟨e x.val, by
    intro j hj
    obtain ⟨j, rfl⟩ := f.surjective j
    rw [hW j] at hj
    exact x.notMem j (e.injective.mem_set_image.mp hj)⟩
  map {x y} a := ⟨{
    transverse j hj := by
      obtain ⟨j, rfl⟩ := f.surjective j
      obtain ⟨t, ht, hti⟩ := hj
      have hi : AffineMap.lineMap x.val y.val t ∈ W j := by
        rw [hW j, ← e.apply_lineMap] at hti
        exact e.injective.mem_set_image.mp hti
      have hd := a.down.transverse j ⟨t, ht, hi⟩
      have hspan : affineSpan ℝ (e '' W j) =
          (affineSpan ℝ (W j)).map e.toAffineMap := by
        simpa only [AffineEquiv.coe_toAffineMap] using
          (AffineSubspace.map_span e.toAffineMap (W j)).symm
      rw [hW j, hspan, AffineSubspace.map_direction,
        AffineEquiv.coe_linear, Submodule.mem_map_equiv]
      have hv : e.linear (y.val - x.val) = e y.val - e x.val :=
        e.toAffineMap.linear_apply_vsub y.val x.val
      simpa only [← hv, LinearEquiv.symm_apply_apply] using hd
    regular t ht := by
      rw [← e.apply_lineMap, Mei.Convex.mem_singularSupport_image_iff e f W W' hW]
      exact a.down.regular t ht }⟩

/-- Transport sends a vertex to its affine image. -/
@[simp]
theorem imagePrefunctor_obj_val (x : WallComplement W) :
    ((imagePrefunctor e f W W' hW).obj x).val = e x.val := (rfl)

/-- Affine transport retains each indexed crossing parameter. -/
@[simp high]
theorem mem_crossings_image (x y : WallComplement W) (j : ι) (t : ℝ) :
    (f j, t) ∈ WallComplement.crossings ((imagePrefunctor e f W W' hW).obj x)
        ((imagePrefunctor e f W W' hW).obj y) ↔ (j, t) ∈ WallComplement.crossings x y := by
  simp only [WallComplement.mem_crossings, imagePrefunctor_obj_val, hW j, ← e.apply_lineMap,
    e.injective.mem_set_image]

end AffineEquiv
