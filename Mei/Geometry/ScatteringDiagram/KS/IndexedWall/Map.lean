/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.IndexedWall
public import Mei.Algebra.Lie.BCH.Ray.Map
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Coefficient maps of indexed KS wall presentations

A degree-preserving Lie homomorphism maps the completed labels of an indexed wall
presentation while retaining its rays, supports and indices. Finite activity is preserved,
but a noninjective map can remove active walls. Forgetting those walls carries an original
admissible path to the same ambient path in the image presentation, and its product is the
image of the original product. Neither consistency nor injectivity is required.

This is the coefficient-change operation for the abelian-ray presentations in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2). The construction uses
`GradedLieHom.completedMap_mem_completedRaySubgroup` and
`GradedLieHom.hasFiniteSupport_completedMap`. The product calculation uses
`Quiver.Path.map_wallPathProduct_restrict`, as in
`DirectedDiagram.levelPathProduct_mapPathPrefunctor`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

universe u

variable {N V R : Type*} {L L' L'' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [LieRing L''] [LieAlgebra R L''] [LieAlgebra ℚ L''] [IsScalarTower ℚ R L'']
  [DecidableEq N] {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'} {ℋ : N → Submodule R L''}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ] [GradedLieAlgebra ℋ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ] [IsPositiveGrading d ℋ]

namespace IndexedWall

variable (W : IndexedWall s d ℒ) (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Apply a degree-preserving Lie homomorphism to a wall label, retaining its geometry. -/
def map : IndexedWall s d ℳ where
  ray := W.ray
  support := W.support
  isCone := W.isCone
  rational_support := W.rational_support
  direction_support := W.direction_support
  label := f.completedMap W.label
  label_mem := f.completedMap_mem_completedRaySubgroup
    (fun _ hn => by simpa only [PositiveDegreeMap.id_apply] using hn) W.label_mem

@[simp]
theorem map_ray : (W.map f).ray = W.ray := (rfl)

@[simp]
theorem map_support : (W.map f).support = W.support := (rfl)

@[simp]
theorem map_label : (W.map f).label = f.completedMap W.label := (rfl)

/-- The identity coefficient map fixes every indexed wall. -/
@[simp]
theorem map_id : W.map (GradedLieHom.id ℒ) = W := by
  apply IndexedWall.ext <;> simp

/-- Successive coefficient maps agree with the composite on indexed walls. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (W.map f).map g = W.map (g.compId f) := by
  apply IndexedWall.ext
  · rfl
  · rfl
  · simp only [map_label, GradedLieHom.completedMap_compId, MonoidHom.comp_apply]

end IndexedWall

namespace IndexedWallPresentation

variable {ι : Type*} (D : IndexedWallPresentation s d ℒ ι)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Change every completed label, retaining repeated supports and original indices. -/
def map : IndexedWallPresentation s d ℳ ι where
  wall j := (D.wall j).map f
  finite_active := by
    simpa only [IndexedWall.map_label] using f.hasFiniteSupport_completedMap D.finite_active

@[simp]
theorem map_wall (j : ι) : (D.map f).wall j = (D.wall j).map f := (rfl)

/-- A mapped index is active exactly when its projected label has nonidentity image. -/
@[simp↓]
theorem mem_active_map (k : ℕ) (j : ι) :
    j ∈ (D.map f).active k ↔
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap
        (CompletedGroup.projection k (D.wall j).label) ≠ 1 := by
  rw [mem_active, map_wall, IndexedWall.map_label,
    f.projection_completedMap_of_le k (a := k) (by simp)]
  -- The tower-group identity is definitionally the concrete BCH-group identity.
  rfl

/-- Coefficient change can only remove active walls. -/
theorem active_map_subset (k : ℕ) : (D.map f).active k ⊆ D.active k := by
  simpa only [Set.subset_def, mem_active, Function.mem_mulSupport, map_wall,
    IndexedWall.map_label] using
    f.mulSupport_projection_completedMap_subset (fun j => (D.wall j).label) k (a := k) (by simp)

/-- The identity coefficient map fixes the whole presentation. -/
@[simp]
theorem map_id : D.map (GradedLieHom.id ℒ) = D := by
  apply IndexedWallPresentation.ext
  funext j
  simp

/-- Successive coefficient changes agree with the composite on presentations. -/
@[simp]
theorem map_map (g : GradedLieHom (PositiveDegreeMap.id d) ℳ ℋ) :
    (D.map f).map g = D.map (g.compId f) := by
  apply IndexedWallPresentation.ext
  funext j
  simp only [map_wall, IndexedWall.map_map]

/-- Forget exactly the source-active walls killed by the coefficient map. -/
def mapPathPrefunctor (k : ℕ) :
    WallComplement (fun j : D.active k => (D.wall j).support) ⥤q
      WallComplement (fun j : (D.map f).active k => ((D.map f).wall j).support) :=
  WallComplement.restrictPrefunctor (fun j : D.active k => (D.wall j).support)
    (Set.inclusion (D.active_map_subset f k))

@[simp]
theorem mapPathPrefunctor_obj_val (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    ((D.mapPathPrefunctor f k).obj x).val = x.val := (rfl)

/-- Forgetting killed walls preserves every ambient vertex. -/
theorem vertices_mapPathPrefunctor (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    ((D.mapPathPrefunctor f k).mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    mapPathPrefunctor_obj_val]

variable [Module.Free ℤ N] [IsAbelianRays d ℒ] [IsAbelianRays d ℳ]

/-- Coefficient change commutes with transport along the same ambient path, including
simultaneous crossings and labels that become trivial. -/
@[simp]
theorem levelPathProduct_mapPathPrefunctor (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (D.map f).levelPathProduct k ((D.mapPathPrefunctor f k).mapPath p) =
      (f.truncatedMap (a := k) k (by simp)).bchGroupMap (D.levelPathProduct k p) := by
  -- Fix the concrete tower-group instances before composing geometric products.
  let F : d.truncatedGroup ℒ k →* d.truncatedGroup ℳ k :=
    (f.truncatedMap (a := k) k (by simp)).bchGroupMap
  have hlabel (j : ι) : CompletedGroup.projection k ((D.wall j).map f).label =
      F (CompletedGroup.projection k (D.wall j).label) := by
    rw [IndexedWall.map_label,
      f.projection_completedMap_of_le k (a := k) (by simp)]
  have hm := p.map_wallPathProduct_restrict (fun j => (D.wall j).support)
    (fun j => s.normal (D.wall j).ray.generator)
    (fun j => CompletedGroup.projection k (D.wall j).label)
    (D.active k) ((D.map f).active k) (D.active_map_subset f k)
    (D.activeLabels_commute k) F (D.mem_active_map f k)
  calc
    _ = _ := (D.map f).levelPathProduct_eq_wallPathProduct k _
      ((D.map f).activeLabels_commute k)
    _ = _ := by
      -- The same labels use the categorical group's inherited instances on the left.
      convert hm using 1
      simp only [Function.comp_def, Set.coe_inclusion, map_wall, IndexedWall.map_ray,
        hlabel, mapPathPrefunctor]
      rfl
    _ = _ := congrArg F (D.levelPathProduct_eq_wallPathProduct k p
      (D.activeLabels_commute k)).symm

end IndexedWallPresentation

end Mei
