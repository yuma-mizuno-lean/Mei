/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Strata
public import Mei.Geometry.Convex.Polyhedron.Face.Facet

/-!
# Chambers of finite polyhedral complexes

The interior of a full-dimensional cell is a connected component of the complement
of the positive-codimension skeleton. If the complex covers the ambient space,
these interiors partition that complement. Thus the finite full-dimensional cells
give the actual chambers on which one can choose transport potentials.

The argument uses `FinitePolyhedralComplex.intrinsicFrontier_subset_support_codimensionAtLeast`
and Mathlib's `IsPreconnected.subset_of_closure_inter_subset`: a chamber cannot leave
its closed cell without passing through the skeleton. Unbounded cells and lineality
are allowed, and the component identification does not require a full ambient cover.
The wall-avoidance criterion uses actual facets supplied by
`TauCeti.IsConvexPolyhedron.exists_facet_of_mem_intrinsicFrontier`.
-/

public section

open Set

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} (C : FinitePolyhedralComplex h)

/-- A full-dimensional cell spans the ambient affine space. -/
theorem affineSpan_eq_top_of_mem_cellsOfCodimension_zero {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) : affineSpan ℝ P = ⊤ := by
  have := h.finiteDimensional
  obtain ⟨hPC, hdim⟩ := (C.mem_cellsOfCodimension 0 P).mp hP
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty
    ((C.nonempty P hPC).mono (subset_affineSpan ℝ P))).mp
  exact Submodule.eq_top_of_finrank_eq (by simpa using hdim)

/-- A full-dimensional cell has nonempty ordinary interior. -/
theorem interior_nonempty_of_mem_cellsOfCodimension_zero {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) : (interior P).Nonempty := by
  have := h.finiteDimensional
  exact (C.isConvexPolyhedron ((C.mem_cellsOfCodimension 0 P).mp hP).1).convex
    |>.interior_nonempty_iff_affineSpan_eq_top.mpr
      (C.affineSpan_eq_top_of_mem_cellsOfCodimension_zero hP)

/-- A full cell's interior misses every cell of positive codimension. -/
theorem interior_subset_compl_support_codimensionAtLeast_one {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) :
    interior P ⊆ (C.codimensionAtLeast 1).supportᶜ := by
  have := h.finiteDimensional
  obtain ⟨hPC, hdimP⟩ := (C.mem_cellsOfCodimension 0 P).mp hP
  intro x hx hxs
  obtain ⟨Q, hQ, hxQ⟩ := mem_support.mp hxs
  obtain ⟨hQC, hdimQ⟩ := (C.mem_codimensionAtLeast_cells 1 Q).mp hQ
  have hPQ := C.subset_of_mem_intrinsicInterior hPC hQC
    (interior_subset_intrinsicInterior hx) hxQ
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPQ))
  omega

/-- Removing the positive-codimension skeleton from a full cell leaves its interior. -/
@[simp]
theorem inter_compl_support_codimensionAtLeast_one {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) :
    P ∩ (C.codimensionAtLeast 1).supportᶜ = interior P := by
  obtain ⟨hPC, hdim⟩ := (C.mem_cellsOfCodimension 0 P).mp hP
  have hi := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    (C.affineSpan_eq_top_of_mem_cellsOfCodimension_zero hP)
  refine Subset.antisymm (fun x hx => ?_)
    (fun x hx => ⟨interior_subset hx, C.interior_subset_compl_support_codimensionAtLeast_one hP hx⟩)
  by_contra hxi
  have hxf : x ∈ intrinsicFrontier ℝ P := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hx.1, by simpa only [hi] using hxi⟩
  exact hx.2 (C.intrinsicFrontier_subset_support_codimensionAtLeast hPC 0 (by omega) hxf)

/-- Each full cell interior is a chamber of the skeleton complement. -/
theorem connectedComponentIn_compl_support_codimensionAtLeast_one {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) {x : V} (hx : x ∈ interior P) :
    connectedComponentIn (C.codimensionAtLeast 1).supportᶜ x = interior P := by
  have hPC := ((C.mem_cellsOfCodimension 0 P).mp hP).1
  have hconv := (C.isConvexPolyhedron hPC).convex
  have hsub := C.interior_subset_compl_support_codimensionAtLeast_one hP
  refine Subset.antisymm ?_ (hconv.interior.isPreconnected.subset_connectedComponentIn hx hsub)
  apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset isOpen_interior
    ⟨x, mem_connectedComponentIn (hsub hx), hx⟩
  intro y hy
  have hyP := closure_minimal interior_subset (C.isConvexPolyhedron hPC).isClosed hy.1
  exact C.inter_compl_support_codimensionAtLeast_one hP ▸
    ⟨hyP, connectedComponentIn_subset _ _ hy.2⟩

/-- In an ambient complex, each point off the skeleton belongs to exactly one
full-dimensional cell interior. -/
theorem exists_unique_mem_interior_cellsOfCodimension_zero (hC : C.support = univ)
    {x : V} (hx : x ∉ (C.codimensionAtLeast 1).support) :
    ∃! P : Set V, P ∈ C.cellsOfCodimension 0 ∧ x ∈ interior P := by
  have := h.finiteDimensional
  obtain ⟨P, hP, hxP⟩ := mem_support.mp (hC ▸ mem_univ x)
  have hdim : Module.finrank ℝ (affineSpan ℝ P).direction = Module.finrank ℝ V := by
    have hle := Submodule.finrank_le (affineSpan ℝ P).direction
    by_contra hne
    exact hx (mem_support.mpr ⟨P,
      (C.mem_codimensionAtLeast_cells 1 P).mpr ⟨hP, by omega⟩, hxP⟩)
  have hP0 : P ∈ C.cellsOfCodimension 0 := (C.mem_cellsOfCodimension 0 P).mpr
    ⟨hP, by simpa using hdim⟩
  refine ⟨P, ⟨hP0, ?_⟩, fun Q hQ => ?_⟩
  · rw [← C.inter_compl_support_codimensionAtLeast_one hP0]
    exact ⟨hxP, hx⟩
  · have hxPi : x ∈ interior P := by
      rw [← C.inter_compl_support_codimensionAtLeast_one hP0]
      exact ⟨hxP, hx⟩
    exact C.eq_of_mem_intrinsicInterior ((C.mem_cellsOfCodimension 0 Q).mp hQ.1).1 hP
      (interior_subset_intrinsicInterior hQ.2) (interior_subset_intrinsicInterior hxPi)

/-- Every boundary point of a full-dimensional cell lies on a wall of the
complex. The wall can be chosen to be a facet of that cell. -/
theorem exists_mem_wall_of_mem_frontier {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) {x : V} (hx : x ∈ frontier P) :
    ∃ W ∈ C.walls, x ∈ W ∧ W ⊆ P := by
  have := h.finiteDimensional
  have hPC := ((C.mem_cellsOfCodimension 0 P).mp hP).1
  have hfront : intrinsicFrontier ℝ P = frontier P := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior, intrinsicClosure_eq_closure,
      Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
        (C.affineSpan_eq_top_of_mem_cellsOfCodimension_zero hP), frontier]
  obtain ⟨W, hW, hxW, hdim⟩ :=
    (C.isConvexPolyhedron hPC).exists_facet_of_mem_intrinsicFrontier (hfront.symm ▸ hx)
  refine ⟨W, (C.mem_cellsOfCodimension 1 W).mpr ⟨?_, ?_⟩, hxW, hW.subset⟩
  · exact C.face_closed P hPC W (isPolyhedralFace_iff.mpr ⟨⟨x, hxW⟩, hW⟩)
  · rw [← direction_affineSpan, ← direction_affineSpan] at hdim
    have hd := ((C.mem_cellsOfCodimension 0 P).mp hP).2
    omega

/-- A preconnected set avoiding the walls cannot leave a full cell's interior
once it meets that interior. No coverage assumption on the complex is needed. -/
theorem subset_interior_of_isPreconnected_of_disjoint_walls {P S : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) (hS : IsPreconnected S)
    (hmeet : (S ∩ interior P).Nonempty) (havoid : ∀ W ∈ C.walls, Disjoint S W) :
    S ⊆ interior P := by
  apply hS.subset_of_closure_inter_subset isOpen_interior hmeet
  intro x hx
  by_contra hnot
  have hxP : x ∈ closure P := closure_mono interior_subset hx.1
  obtain ⟨W, hW, hxW, -⟩ := C.exists_mem_wall_of_mem_frontier hP
    (by rw [frontier]; exact ⟨hxP, hnot⟩)
  exact Set.disjoint_left.mp (havoid W hW) hx.2 hxW

end Mei.FinitePolyhedralComplex
