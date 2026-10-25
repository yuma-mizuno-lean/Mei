/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Affine transport of admissible polygonal paths

Continuous affine equivalences, together with a bijection of wall indices,
preserve singular support and admissible segments. The resulting quiver
prefunctor transports polygonal paths using Mathlib's `Prefunctor.mapPath`.
Crossing parameters and wall indices transform exactly, so these maps retain
simultaneous crossings and repeated visits.

The singular-support comparison uses Mathlib's affine-span image formula and
`ContinuousAffineEquiv.intrinsicFrontier_image`; no polyhedrality, finiteness,
or codimension assumption on the walls is needed.
-/

public section

open Set Mei.Convex Mei.Convex.WallComplement

namespace ContinuousAffineEquiv

variable {V V' ι ι' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {W : ι → Set V} {W' : ι' → Set V'}

/-- Affine transport of allowed vertices and admissible segments, with the wall
indices transported by `r`. Use `Prefunctor.mapPath` for polygonal paths. -/
def wallComplementMap (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι')
    (hW : ∀ j, W' (r j) = e '' W j) : WallComplement W ⥤q WallComplement W' where
  obj x := ⟨e x.val, fun j hj => by
    obtain ⟨j, rfl⟩ := r.surjective j
    rw [hW, e.injective.mem_set_image] at hj
    exact x.notMem j hj⟩
  map {x y} a := ⟨{
    transverse := fun j hj => by
      obtain ⟨j, rfl⟩ := r.surjective j
      obtain ⟨t, ht, hj⟩ := hj
      have hline : e (AffineMap.lineMap x.val y.val t) =
          AffineMap.lineMap (e x.val) (e y.val) t := by
        simpa only [ContinuousAffineEquiv.coe_coe] using
          e.toAffineEquiv.apply_lineMap x.val y.val t
      dsimp only at hj ⊢
      have hc : AffineMap.lineMap x.val y.val t ∈ W j := by
        rw [hW, ← hline, e.injective.mem_set_image] at hj
        exact hj
      have hdir : (affineSpan ℝ (W' (r j))).direction =
          ((affineSpan ℝ (W j)).direction).map e.toAffineEquiv.linear.toLinearMap := by
        rw [hW]
        simpa only [AffineSubspace.map_direction, AffineEquiv.linear_toAffineMap,
          AffineEquiv.coe_coe, ContinuousAffineEquiv.coe_coe] using
          congrArg AffineSubspace.direction
            (AffineSubspace.map_span e.toAffineEquiv.toAffineMap (W j)).symm
      have hv : e.toAffineEquiv.linear (y.val - x.val) = e y.val - e x.val := by
        simpa only [AffineEquiv.linear_toAffineMap, AffineEquiv.coe_coe,
          ContinuousAffineEquiv.coe_coe, LinearEquiv.coe_coe, vsub_eq_sub] using
          e.toAffineEquiv.toAffineMap.linear_apply_vsub y.val x.val
      rw [hdir, ← hv]
      intro hm
      obtain ⟨v, hv, he⟩ := Submodule.mem_map.mp hm
      exact a.down.transverse j ⟨t, ht, hc⟩
        (e.toAffineEquiv.linear.injective he ▸ hv)
    regular := fun t ht => by
      have hline : e (AffineMap.lineMap x.val y.val t) =
          AffineMap.lineMap (e x.val) (e y.val) t := by
        simpa only [ContinuousAffineEquiv.coe_coe] using
          e.toAffineEquiv.apply_lineMap x.val y.val t
      dsimp only
      rw [singularSupport_image e r hW, ← hline, e.injective.mem_set_image]
      exact a.down.regular t ht }⟩

@[simp]
theorem wallComplementMap_obj_val (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι')
    (hW : ∀ j, W' (r j) = e '' W j) (x : WallComplement W) :
    ((wallComplementMap e r hW).obj x).val = e x.val := (rfl)

/-- Affine transport preserves reversal of segments and hence of polygonal paths. -/
instance (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι') (hW : ∀ j, W' (r j) = e '' W j) :
    (wallComplementMap e r hW).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- Affine transport preserves each crossing parameter, changing only its wall index. -/
theorem mem_crossings_wallComplementMap (e : V ≃ᴬ[ℝ] V') (r : ι ≃ ι')
    (hW : ∀ j, W' (r j) = e '' W j) (x y : WallComplement W) (j : ι) (t : ℝ) :
    (r j, t) ∈ crossings ((wallComplementMap e r hW).obj x) ((wallComplementMap e r hW).obj y) ↔
      (j, t) ∈ crossings x y := by
  have hline : e (AffineMap.lineMap x.val y.val t) =
      AffineMap.lineMap (e x.val) (e y.val) t := by
    simpa only [ContinuousAffineEquiv.coe_coe] using
      e.toAffineEquiv.apply_lineMap x.val y.val t
  simp only [mem_crossings, wallComplementMap_obj_val, hW, ← hline, e.injective.mem_set_image]

end ContinuousAffineEquiv
