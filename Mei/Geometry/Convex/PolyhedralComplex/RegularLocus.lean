/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Chamber
public import Mei.Geometry.Convex.PolyhedralComplex.Subdivision
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# The regular locus of an ambient polyhedral complex

For a finite polyhedral complex covering the ambient space, its walls cover the
positive-codimension skeleton, and their singular support is exactly the
codimension-at-least-two skeleton. Thus admissible wall paths avoid every joint
and every higher stratum. Their edges meet the avoidance hypothesis for polygonal
cone fillings of the complement of the higher skeleton. Coverage of the ambient
space is essential for these skeleton identifications.

For any finite complex, convex regular opens form a basis, with dense off-wall
points and admissible segments between them. Cells may be unbounded and have lineality.
-/

public section

open Set Mei.Convex CategoryTheory TopologicalSpace Topology

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)

/-- Every point of an ambient complex lies in a full-dimensional cell, including
points on its boundary strata. -/
theorem exists_mem_cellsOfCodimension_zero (hC : C.support = univ) (x : V) :
    ∃ P ∈ C.cellsOfCodimension 0, x ∈ P := by
  -- The full-dimensional covering uses
  -- `FinitePolyhedralComplex.exists_mem_cells_subset_finrank_eq_of_cover`.
  have := h.finiteDimensional
  obtain ⟨P, hP, -, hxP, hdim⟩ := C.exists_mem_cells_subset_finrank_eq_of_cover (P := univ)
    convex_univ (fun y _ => by
      obtain ⟨Q, hQ, hyQ⟩ := mem_support.mp (hC ▸ mem_univ y)
      exact ⟨Q, hQ, subset_univ Q, hyQ⟩) (mem_univ x)
  refine ⟨P, (C.mem_cellsOfCodimension 0 P).mpr ⟨hP, ?_⟩, hxP⟩
  rw [AffineSubspace.span_univ ℝ V V, AffineSubspace.direction_top, finrank_top] at hdim
  simpa only [add_zero] using hdim

/-- In an ambient complex, the walls cover the entire positive-codimension
skeleton, including cells of smaller dimension. -/
theorem support_codimensionAtLeast_one_eq_iUnion_walls (hC : C.support = univ) :
    (C.codimensionAtLeast 1).support = ⋃ W : C.walls, (W : Set V) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨P, hP, hxP⟩ := C.exists_mem_cellsOfCodimension_zero hC x
    have hnot : x ∉ interior P := fun hxi =>
      C.interior_subset_compl_support_codimensionAtLeast_one hP hxi hx
    have hPC := ((C.mem_cellsOfCodimension 0 P).mp hP).1
    -- Boundary points lie on actual facets by
    -- `FinitePolyhedralComplex.exists_mem_wall_of_mem_frontier`.
    obtain ⟨W, hW, hxW, -⟩ := C.exists_mem_wall_of_mem_frontier hP (by
      rw [frontier, (C.isConvexPolyhedron hPC).isClosed.closure_eq]
      exact ⟨hxP, hnot⟩)
    exact mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  · intro x hx
    obtain ⟨W, hxW⟩ := mem_iUnion.mp hx
    exact mem_support.mpr
      ⟨W, C.cellsOfCodimension_subset_codimensionAtLeast_cells 1 W.property, hxW⟩

/-- For a finite complex covering the ambient space, wall singular support is
precisely the skeleton of codimension at least two. The equality includes lower
strata even when several walls have the same supporting hyperplane. -/
theorem singularSupport_walls_eq_support_codimensionAtLeast_two (hC : C.support = univ) :
    singularSupport (fun W : C.walls => (W : Set V)) =
      (C.codimensionAtLeast 2).support := by
  have := h.finiteDimensional
  apply Subset.antisymm C.singularSupport_walls_subset_support_codimensionAtLeast
  intro x hx
  by_contra hregular
  have hxone : x ∈ (C.codimensionAtLeast 1).support := by
    obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
    exact mem_support.mpr
      ⟨P, C.codimensionAtLeast_cells_antitone (by omega : 1 ≤ 2) hP, hxP⟩
  rw [C.support_codimensionAtLeast_one_eq_iUnion_walls hC] at hxone
  obtain ⟨W, hxW⟩ := mem_iUnion.mp hxone
  obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
  obtain ⟨hPC, hdimP⟩ := (C.mem_codimensionAtLeast_cells 2 P).mp hP
  -- Common-face incidence prevents a regular interior point of a wall from
  -- also lying in a cell of smaller dimension.
  have hWP := C.subset_of_mem_intrinsicInterior (C.mem_cells_of_mem_walls W.property)
    hPC (mem_intrinsicInterior_of_notMem_singularSupport hxW hregular) hxP
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hWP))
  have hdimW := C.finrank_direction_add_one_of_mem_walls W.property
  omega

/-- Every admissible edge for an ambient complex misses the skeleton of
codimension at least `k`, for any `k ≥ 2`. This applies to the fixed edges in
polygonal cone fillings, without perturbing those edges. -/
theorem disjoint_segment_support_codimensionAtLeast (hC : C.support = univ)
    {x y : WallComplement (fun W : C.walls => (W : Set V))}
    (e : x ⟶ y) {k : ℕ} (hk : 2 ≤ k) :
    Disjoint (segment ℝ x.val y.val) (C.codimensionAtLeast k).support := by
  apply disjoint_left.mpr
  intro z hz hzk
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  apply e.down.regular t ht
  rw [C.singularSupport_walls_eq_support_codimensionAtLeast_two hC]
  obtain ⟨P, hP, hzP⟩ := mem_support.mp hzk
  exact mem_support.mpr ⟨P, C.codimensionAtLeast_cells_antitone hk hP, hzP⟩

/-- The open locus obtained by removing wall boundaries and joints. -/
abbrev regularLocus : Set V :=
  (singularSupport (fun P : C.walls => (P : Set V)))ᶜ

/-- The regular locus is open, even for unbounded walls with lineality. -/
theorem isOpen_regularLocus : IsOpen C.regularLocus := by
  have := h.finiteDimensional
  exact (isClosed_singularSupport _ (fun P =>
    (C.isConvexPolyhedron (C.mem_cells_of_mem_walls P.property)).isClosed)).isOpen_compl

/-- The regular locus as the base space of the coefficient sheaf. -/
abbrev regularSpace : TopCat := TopCat.of C.regularLocus

/-- Coefficient values are recorded at the off-wall points of the regular locus. -/
abbrev coefficientPoints : Set C.regularSpace :=
  {x | ∀ P : C.walls, x.val ∉ (P : Set V)}

/-- Off-wall coefficient points are dense in the full regular locus. -/
theorem dense_coefficientPoints : Dense C.coefficientPoints := by
  have := h.finiteDimensional
  have hd := AffineSubspace.dense_genericLocus
    (fun P : C.walls => affineSpan ℝ (P : Set V))
    (fun P => (affineSpan ℝ (P : Set V)).ne_top_of_finrank_direction_add_one_eq
      (C.finrank_direction_add_one_of_mem_walls P.property))
  have hd' : Dense (((↑) : C.regularSpace → V) ⁻¹'
      AffineSubspace.genericLocus (fun P : C.walls => affineSpan ℝ (P : Set V))) :=
    hd.preimage C.isOpen_regularLocus.isOpenMap_subtype_val
  apply hd'.mono
  exact fun x hx P hP => (AffineSubspace.mem_genericLocus.mp hx) P (subset_affineSpan ℝ _ hP)

/-- Convex ambient images of regular opens are the segment-transport charts. -/
def coefficientCharts : Set (Opens C.regularSpace) :=
  {U | Convex ℝ (Subtype.val '' (U : Set C.regularSpace))}

/-- A coefficient chart is exactly a regular open with convex ambient image. -/
@[simp]
theorem mem_coefficientCharts (U : Opens C.regularSpace) :
    U ∈ C.coefficientCharts ↔ Convex ℝ (Subtype.val '' (U : Set C.regularSpace)) := Iff.rfl

/-- Convex regular opens form a basis, by taking small ambient balls. -/
theorem coefficientCharts_isBasis : Opens.IsBasis C.coefficientCharts := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have ho : IsOpen (Subtype.val '' (U : Set C.regularSpace)) :=
    C.isOpen_regularLocus.isOpenMap_subtype_val _ U.isOpen
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp ho x.val ⟨x, hx, rfl⟩
  let B : Opens C.regularSpace :=
    ⟨Subtype.val ⁻¹' Metric.ball x.val ε, Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hB : Subtype.val '' (B : Set C.regularSpace) = Metric.ball x.val ε := by
    exact Set.image_preimage_eq_of_subset (hεU.trans (Set.image_subset_range _ _))
  refine ⟨B, ?_, Metric.mem_ball_self hε, ?_⟩
  · simpa only [coefficientCharts, mem_ofPred_eq, hB] using convex_ball x.val ε
  · intro y hy
    obtain ⟨z, hz, he⟩ := hεU hy
    exact (Subtype.ext he) ▸ hz

/-- Every transport chart is preconnected in the regular locus. -/
theorem coefficientChart_preconnected {U : Opens C.regularSpace}
    (hU : U ∈ C.coefficientCharts) : IsPreconnected (U : Set C.regularSpace) :=
  IsInducing.subtypeVal.isPreconnected_image.mp hU.isPreconnected

/-- A segment in a convex regular chart is admissible. -/
def coefficientSegment (U : Opens C.regularSpace) (hU : U ∈ C.coefficientCharts)
    (x y : C.coefficientPoints) (hx : x.val ∈ U) (hy : y.val ∈ U) :
    (⟨x.val.val, x.property⟩ : WallComplement (fun P : C.walls => (P : Set V))) ⟶
      ⟨y.val.val, y.property⟩ :=
  ⟨hU.admissibleSegment_of_disjoint_singularSupport
    (Set.disjoint_left.mpr (by rintro _ ⟨z, _, rfl⟩ hz; exact z.property hz))
    ⟨x.val, hx, rfl⟩ ⟨y.val, hy, rfl⟩⟩

end Mei.FinitePolyhedralComplex
