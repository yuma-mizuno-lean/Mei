/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product

/-!
# Projection of paths through cylinder walls

Adding unrestricted spatial coordinates to each wall preserves singular support
and signed crossings. Projection onto the original coordinates carries admissible
polygonal paths and their wall products to the original wall family.
-/

public section
noncomputable section

open Set Mei.Convex

namespace Mei.Convex

variable {V E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace WallComplement

variable (W : ι → Set V)

/-- Forget the unrestricted coordinates of a path through cylinder walls. -/
def cylinderProjection : WallComplement (fun j => W j ×ˢ (univ : Set E)) ⥤q
    WallComplement W where
  obj x := ⟨x.val.1, fun j hj => x.notMem j ⟨hj, mem_univ _⟩⟩
  map {x y} a := ⟨{
    transverse := fun j hj hm => by
      obtain ⟨t, ht, hmem⟩ := hj
      apply a.down.transverse j ⟨t, ht, hmem, mem_univ _⟩
      rw [Mei.direction_affineSpan_prod_univ ⟨_, hmem⟩]
      exact ⟨hm, Submodule.mem_top⟩
    regular := fun t ht hm => by
      apply a.down.regular t ht
      rw [singularSupport_prod_univ W]
      exact ⟨hm, mem_univ _⟩ }⟩

@[simp]
theorem cylinderProjection_obj_val
    (x : WallComplement (fun j => W j ×ˢ (univ : Set E))) :
    ((cylinderProjection W).obj x).val = x.val.1 := by rfl

instance : (cylinderProjection (E := E) W).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- A segment and its projection cross the same walls at the same times. -/
theorem mem_crossings_cylinderProjection
    (x y : WallComplement (fun j => W j ×ˢ (univ : Set E))) (j : ι) (t : ℝ) :
    (j, t) ∈ crossings ((cylinderProjection W).obj x)
      ((cylinderProjection W).obj y) ↔ (j, t) ∈ crossings x y := by
  simp [mem_crossings, AffineMap.lineMap_apply]

variable [Finite ι]
  {x y : WallComplement (fun j => W j ×ˢ (univ : Set E))}

/-- Projection of a cylinder segment preserves its ordered crossing times. -/
@[simp]
theorem orderedCrossingTimes_cylinderProjection (a : x ⟶ y) :
    orderedCrossingTimes ((cylinderProjection W).map a) = orderedCrossingTimes a := by
  apply (pairwise_orderedCrossingTimes _).eq_of_mem_iff (pairwise_orderedCrossingTimes _)
  intro t
  simp

/-- Projection preserves a signed crossing event, using the pulled-back functionals
`ν j ∘ fst` on the cylinder. -/
@[simp]
theorem signedCrossingEvent_cylinderProjection (ν : ι → V →ₗ[ℝ] ℝ) (t : ℝ) :
    signedCrossingEvent ν ((cylinderProjection W).obj x)
      ((cylinderProjection W).obj y) t =
    signedCrossingEvent (fun j => (ν j).comp (LinearMap.fst ℝ V E)) x y t := by
  ext ⟨j, s⟩
  simp

/-- Projection preserves segment crossing events, using the pulled-back functionals
`ν j ∘ fst` on the cylinder. -/
@[simp]
theorem segmentCrossingEvents_cylinderProjection (ν : ι → V →ₗ[ℝ] ℝ) (a : x ⟶ y) :
    segmentCrossingEvents ν ((cylinderProjection W).map a) =
      segmentCrossingEvents (fun j => (ν j).comp (LinearMap.fst ℝ V E)) a := by
  simp only [segmentCrossingEvents_def, orderedCrossingTimes_cylinderProjection]
  apply List.map_congr_left
  intro t _
  exact signedCrossingEvent_cylinderProjection W ν t

end WallComplement
end Mei.Convex

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (W : ι → Set V) [Finite ι]
  {x y : WallComplement (fun j => W j ×ˢ (univ : Set E))}

/-- Projecting a cylinder path preserves its signed crossing events, measured on the
cylinder by the pulled-back functionals `ν j ∘ fst`. -/
@[simp]
theorem signedCrossingEvents_cylinderProjection (ν : ι → V →ₗ[ℝ] ℝ)
    (p : AdmissiblePLPath x y) :
    ((cylinderProjection W).mapPath p).signedCrossingEvents ν =
      p.signedCrossingEvents (fun j => (ν j).comp (LinearMap.fst ℝ V E)) := by
  induction p with
  | nil => simp
  | cons p a ih => simp [ih]

/-- The product along a cylinder path is the product along its spatial projection. -/
theorem wallPathProduct_cylinderProjection {G : Type*} [Group G]
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
    (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (p : AdmissiblePLPath x y) :
    ((cylinderProjection W).mapPath p).wallPathProduct ν label comm =
      p.wallPathProduct (fun j => (ν j).comp (LinearMap.fst ℝ V E)) label
        (fun i j h => comm i j ((Mei.affineSpan_prod_univ_eq_iff (W i) (W j)).mp h)) := by
  rw [wallPathProduct_eq_prod_signedCrossingEvents,
    wallPathProduct_eq_prod_signedCrossingEvents, signedCrossingEvents_cylinderProjection]

end Quiver.Path
