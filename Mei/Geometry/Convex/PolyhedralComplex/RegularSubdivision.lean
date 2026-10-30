/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.RegularLocus
public import Mei.Geometry.Convex.PolyhedralComplex.Subdivision
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Regular loci under subdivision

Subdivision can add singular strata, while every old singular point remains
singular. The fine regular locus therefore embeds openly in the coarse one.
Off-wall coefficient points map to the coarse complex without changing their
ambient coordinates. Images of convex regular charts
are again convex regular charts.

These comparisons do not require the complexes to cover the ambient space.
-/

public noncomputable section

open Set CategoryTheory TopologicalSpace Topology Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C D E : FinitePolyhedralComplex h}

namespace IsSubdivision

variable (hCD : C.IsSubdivision D)

include hCD

/-- Every coarse singular point remains singular after subdivision.
No ambient-coverage hypothesis is needed. -/
theorem singularSupport_subset :
    singularSupport (fun P : D.walls => (P : Set V)) ⊆
      singularSupport (fun Q : C.walls => (Q : Set V)) :=
  singularSupport_subset_of_wall_cover
    (fun P => (D.isConvexPolyhedron (D.mem_cells_of_mem_walls P.property)).isClosed)
    hCD.exists_mem_walls_subset_affineSpan_eq

/-- A point regular for the fine complex is regular for the coarse complex. -/
theorem regularLocus_subset : C.regularLocus ⊆ D.regularLocus :=
  Set.compl_subset_compl.mpr hCD.singularSupport_subset

/-- The canonical inclusion of the fine regular locus in the coarse one. -/
def regularInclusion : C.regularSpace ⟶ D.regularSpace :=
  TopCat.ofHom ⟨Set.inclusion hCD.regularLocus_subset,
    continuous_subtype_val.subtype_mk _⟩

/-- Regular-locus inclusion leaves ambient coordinates unchanged. -/
@[simp]
theorem regularInclusion_val (x : C.regularSpace) :
    (hCD.regularInclusion x).val = x.val := (rfl)

/-- The regular-locus map is an open embedding for the inherited topologies. -/
theorem isOpenEmbedding_regularInclusion : IsOpenEmbedding hCD.regularInclusion :=
  IsOpenEmbedding.inclusion hCD.regularLocus_subset
    (C.isOpen_regularLocus.preimage continuous_subtype_val)

omit hCD in
/-- Inclusion for the reflexive subdivision is the identity map. -/
@[simp]
theorem regularInclusion_refl :
    (IsSubdivision.refl C).regularInclusion = 𝟙 C.regularSpace := by
  ext x
  rfl

/-- Inclusions compose without making any new geometric choices. -/
theorem regularInclusion_trans (hDE : D.IsSubdivision E) :
    (hCD.trans hDE).regularInclusion = hCD.regularInclusion ≫ hDE.regularInclusion := by
  ext x
  rfl

/-- Fine off-wall coefficient points remain off every coarse wall. -/
def coefficientPointMap (x : C.coefficientPoints) : D.coefficientPoints :=
  ⟨hCD.regularInclusion x.val, fun P hx => by
    obtain ⟨Q, hxQ, _, _⟩ := hCD.exists_mem_walls_subset_affineSpan_eq P x.val.val hx
    exact x.property Q hxQ⟩

/-- The underlying regular point is the canonical regular-locus inclusion. -/
@[simp]
theorem coefficientPointMap_val (x : C.coefficientPoints) :
    (hCD.coefficientPointMap x).val = hCD.regularInclusion x.val := (rfl)

omit hCD in
/-- Reflexive subdivision fixes every coefficient point. -/
@[simp]
theorem coefficientPointMap_refl (x : C.coefficientPoints) :
    (IsSubdivision.refl C).coefficientPointMap x = x := (rfl)

/-- Fine coefficient-point inclusions compose. -/
theorem coefficientPointMap_trans (hDE : D.IsSubdivision E) (x : C.coefficientPoints) :
    (hCD.trans hDE).coefficientPointMap x =
      hDE.coefficientPointMap (hCD.coefficientPointMap x) := (rfl)

/-- The open image of a fine regular open in the coarse regular space. -/
abbrev regularOpenImage (U : Opens C.regularSpace) : Opens D.regularSpace :=
  hCD.isOpenEmbedding_regularInclusion.functor.obj U

/-- A coarse regular point lies in the open image exactly when it comes from the fine open. -/
theorem mem_regularOpenImage_iff (U : Opens C.regularSpace) (y : D.regularSpace) :
    y ∈ hCD.regularOpenImage U ↔ ∃ x ∈ U, hCD.regularInclusion x = y := (Iff.rfl)

/-- Regular-locus inclusion reflects membership in open images. -/
@[simp]
theorem regularInclusion_mem_regularOpenImage_iff (U : Opens C.regularSpace)
    (x : C.regularSpace) : hCD.regularInclusion x ∈ hCD.regularOpenImage U ↔ x ∈ U :=
  hCD.isOpenEmbedding_regularInclusion.injective.mem_set_image

/-- Coefficient-point inclusion reflects membership in open images. -/
theorem coefficientPointMap_mem_regularOpenImage_iff (U : Opens C.regularSpace)
    (x : C.coefficientPoints) :
    (hCD.coefficientPointMap x).val ∈ hCD.regularOpenImage U ↔ x.val ∈ U := by
  rw [coefficientPointMap_val, regularInclusion_mem_regularOpenImage_iff]

/-- A fine coefficient point maps into the image of every regular open containing it. -/
theorem coefficientPointMap_mem_regularOpenImage (U : Opens C.regularSpace)
    (x : C.coefficientPoints) (hx : x.val ∈ U) :
    (hCD.coefficientPointMap x).val ∈ hCD.regularOpenImage U :=
  (hCD.coefficientPointMap_mem_regularOpenImage_iff U x).mpr hx

omit hCD in
/-- Reflexive subdivision fixes each regular open. -/
@[simp]
theorem regularOpenImage_refl (U : Opens C.regularSpace) :
    (IsSubdivision.refl C).regularOpenImage U = U := by
  apply Opens.ext
  -- The open embedding's image functor has the defining carrier given by set image.
  change (IsSubdivision.refl C).regularInclusion '' (U : Set C.regularSpace) = _
  rw [regularInclusion_refl, TopCat.coe_id, Set.image_id]

/-- Open images compose along successive subdivisions. -/
theorem regularOpenImage_trans (hDE : D.IsSubdivision E) (U : Opens C.regularSpace) :
    (hCD.trans hDE).regularOpenImage U = hDE.regularOpenImage (hCD.regularOpenImage U) := by
  apply Opens.ext
  -- The open embedding functors define their carriers as set images.
  change (hCD.trans hDE).regularInclusion '' (U : Set C.regularSpace) =
    hDE.regularInclusion '' (hCD.regularInclusion '' (U : Set C.regularSpace))
  rw [regularInclusion_trans, TopCat.coe_comp, Set.image_comp]

/-- Passing to the open image does not change the represented ambient set. -/
theorem regularOpenImage_ambient (U : Opens C.regularSpace) :
    Subtype.val '' (hCD.regularOpenImage U : Set D.regularSpace) =
      Subtype.val '' (U : Set C.regularSpace) := by
  -- Expose the image carrier before composing the inclusion with ambient projection.
  change Subtype.val '' (hCD.regularInclusion '' (U : Set C.regularSpace)) = _
  have hval : Subtype.val ∘ hCD.regularInclusion = (Subtype.val : C.regularSpace → V) :=
    funext hCD.regularInclusion_val
  rw [← Set.image_comp, hval]

/-- The image of a convex fine regular chart is a convex coarse regular chart. -/
theorem coefficientChart_regularOpenImage {U : Opens C.regularSpace}
    (hU : U ∈ C.coefficientCharts) : hCD.regularOpenImage U ∈ D.coefficientCharts := by
  rw [mem_coefficientCharts, hCD.regularOpenImage_ambient]
  exact (C.mem_coefficientCharts U).mp hU

end IsSubdivision
end Mei.FinitePolyhedralComplex
