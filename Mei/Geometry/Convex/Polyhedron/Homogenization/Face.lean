/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Cone.Slice
public import Mei.Geometry.Convex.Homogenization.Face
public import Mei.Geometry.Convex.Polyhedron.Homogenization.Inequalities
public import Mei.Geometry.Convex.Polyhedron.Face
public import Mathlib.Geometry.Convex.Cone.Face.Lattice

/-!
# Faces and actual homogenization

Nonempty exposed faces of a polyhedron correspond to the faces of its actual
closed homogenization that meet height one. The correspondence sends a face to
its carrier-defined homogenization and takes the height-one slice in reverse.
Faces entirely at height zero are excluded. Lineality is allowed; finite
generation and finite dimensionality are not assumed.
-/

public section

open Set ContinuousAffineMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace PointedCone.IsFaceOf

/-- A cone face of a polyhedral homogenization has an exposed height-one slice. -/
theorem isExposed_slice_one_of_homogenization {P : Set V} {G : PointedCone ℝ (V × ℝ)}
    (hG : G.IsFaceOf (Set.homogenization P)) (hP : TauCeti.IsConvexPolyhedron P) :
    IsExposed ℝ P {x : V | (x, (1 : ℝ)) ∈ G} := by
  have hslice : {x : V | (x, (1 : ℝ)) ∈ Set.homogenization P} = P := by
    ext x
    exact hP.convex.mem_homogenization_one_iff hP.isClosed
  have hext := hG.isExtreme_slice_one
  rw [hslice] at hext
  have hconv : Convex ℝ {x : V | (x, (1 : ℝ)) ∈ G} :=
    G.convex.affine_preimage ((AffineMap.id ℝ V).prod (AffineMap.const ℝ V (1 : ℝ)))
  exact hext.isExposed_of_isConvexPolyhedron hP hconv

/-- Faces meeting height one are closed because they are convex extreme
subsets of a polyhedral cone. No finite-generation assumption is needed. -/
theorem isClosed_of_homogenization {P : Set V} {G : PointedCone ℝ (V × ℝ)}
    (hG : G.IsFaceOf (Set.homogenization P)) (hP : TauCeti.IsConvexPolyhedron P)
    (hne : {x : V | (x, (1 : ℝ)) ∈ G}.Nonempty) : IsClosed (G : Set (V × ℝ)) := by
  obtain ⟨p, hp⟩ := hne
  have hPne : P.Nonempty :=
    ⟨p, (hP.convex.mem_homogenization_one_iff hP.isClosed).mp (hG.le hp)⟩
  exact (hG.isExtreme.isConvexPolyhedron
    (Mei.Convex.isConvexPolyhedron_homogenization hP hPne) G.convex).isClosed

end PointedCone.IsFaceOf

namespace Mei.Convex

/-- Nonempty exposed faces of a polyhedron correspond, in their actual inclusion
orders, to the faces of its closed homogenization that meet height one.

The maps are actual homogenization and height-one slicing. Empty affine faces
and cone faces entirely at height zero are excluded; no salience assumption is made. -/
def nonemptyExposedFaceOrderIso {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    {F : Set V // F.Nonempty ∧ IsExposed ℝ P F} ≃o
      {G : (homogenization P).Face // {x : V | (x, (1 : ℝ)) ∈ G}.Nonempty} where
  toFun F :=
    ⟨⟨homogenization F.val,
      F.property.2.homogenization_isFaceOf hP.convex hP.isClosed F.property.1⟩,
      by
        obtain ⟨p, hp⟩ := F.property.1
        exact ⟨p, mem_homogenization_one hp⟩⟩
  invFun G :=
    ⟨{x : V | (x, (1 : ℝ)) ∈ G.val}, G.property,
      G.val.isFaceOf.isExposed_slice_one_of_homogenization hP⟩
  left_inv F := by
    apply Subtype.ext
    ext x
    exact (F.property.2.convex hP.convex).mem_homogenization_one_iff
      (F.property.2.isClosed hP.isClosed)
  right_inv G := by
    apply Subtype.ext
    apply PointedCone.Face.ext
    intro z
    have heq := G.val.toPointedCone.homogenization_slice_one
      (G.val.isFaceOf.isClosed_of_homogenization hP G.property)
      (fun w hw => homogenization_height_nonneg (G.val.isFaceOf.le hw)) G.property
    simpa only [← PointedCone.Face.mem_toPointedCone] using SetLike.ext_iff.mp heq z
  map_rel_iff' := by
    intro F F'
    -- Reduce the subtype orders and the bundled face order to cone inclusion.
    -- The order isomorphism is still being constructed, so its evaluation lemmas
    -- are not yet available to rewrite these projections.
    change homogenization F.val ≤ homogenization F'.val ↔ F.val ⊆ F'.val
    constructor
    · intro h x hx
      exact ((F'.property.2.convex hP.convex).mem_homogenization_one_iff
        (F'.property.2.isClosed hP.isClosed)).mp (h (mem_homogenization_one hx))
    · exact homogenization_mono

/-- The order correspondence sends a face to its actual carrier-defined homogenization. -/
@[simp]
theorem nonemptyExposedFaceOrderIso_apply {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (F : {F : Set V // F.Nonempty ∧ IsExposed ℝ P F}) :
    ((nonemptyExposedFaceOrderIso hP F).val).toPointedCone = homogenization F.val :=
  Eq.trans rfl rfl

/-- The inverse order correspondence takes the exact height-one slice. -/
@[simp]
theorem nonemptyExposedFaceOrderIso_symm_apply {P : Set V} (hP : TauCeti.IsConvexPolyhedron P)
    (G : {G : (homogenization P).Face // {x : V | (x, (1 : ℝ)) ∈ G}.Nonempty}) :
    ((nonemptyExposedFaceOrderIso hP).symm G).val = {x : V | (x, (1 : ℝ)) ∈ G.val} :=
  Eq.trans rfl rfl

end Mei.Convex
