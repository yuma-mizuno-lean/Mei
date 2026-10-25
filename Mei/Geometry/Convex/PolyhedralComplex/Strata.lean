/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import Mei.Geometry.Convex.Polyhedron.SingularSupport
public import Mei.Geometry.Convex.Polyhedron.Face

/-!
# Walls, joints and regular points of finite polyhedral complexes

Filter actual cell carriers by their ambient codimension. Walls have codimension
one, joints have codimension two, and the cells of codimension at least `k` form
a subcomplex. The singular support of the wall family is contained in the
codimension-at-least-two subcomplex. Outside singular support a point belongs
to at most one wall, so a transverse crossing has an unambiguous wall index.

All cells may be unbounded and may have lineality.

## References

* Mathlib's `IsExposed` common-face condition and relative interiors.
* Mei's `Mei.Convex.intrinsicFrontier_eq_iUnion_active` and
  `AffineMap.finrank_direction_inter_zero_lt`.
* Mei's `AffineSubspace.finrank_direction_inf_add_one_lt`.
-/

public section

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The finite collection of cells of ambient codimension exactly `k`. -/
noncomputable def cellsOfCodimension (C : FinitePolyhedralComplex h) (k : ℕ) :
    Finset (Set V) := by
  classical
  exact C.cells.filter fun P =>
    Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V

/-- Membership records both the original cell and its exact codimension. -/
@[simp]
theorem mem_cellsOfCodimension (C : FinitePolyhedralComplex h) (k : ℕ) (P : Set V) :
    P ∈ C.cellsOfCodimension k ↔ P ∈ C.cells ∧
      Module.finrank ℝ (affineSpan ℝ P).direction + k = Module.finrank ℝ V := by
  classical
  simp [cellsOfCodimension]

/-- Walls are the codimension-one cells. -/
noncomputable abbrev walls (C : FinitePolyhedralComplex h) : Finset (Set V) :=
  C.cellsOfCodimension 1

/-- Every wall is a cell of the complex. -/
theorem mem_cells_of_mem_walls (C : FinitePolyhedralComplex h) {P : Set V}
    (hP : P ∈ C.walls) : P ∈ C.cells :=
  ((C.mem_cellsOfCodimension 1 P).mp hP).1

/-- The direction dimension of a wall is one less than the ambient dimension. -/
theorem finrank_direction_add_one_of_mem_walls (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.walls) :
    Module.finrank ℝ (affineSpan ℝ P).direction + 1 = Module.finrank ℝ V :=
  ((C.mem_cellsOfCodimension 1 P).mp hP).2

/-- Joints are the codimension-two cells. -/
noncomputable abbrev joints (C : FinitePolyhedralComplex h) : Finset (Set V) :=
  C.cellsOfCodimension 2

/-- The subcomplex consisting of all cells of ambient codimension at least `k`.
The dimension inequality also gives the empty complex when `k` exceeds the ambient dimension. -/
noncomputable def codimensionAtLeast (C : FinitePolyhedralComplex h) (k : ℕ) :
    FinitePolyhedralComplex h := by
  classical
  have := h.finiteDimensional
  refine
    { cells := C.cells.filter fun P =>
        Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V
      nonempty := ?_
      rational := ?_
      face_closed := ?_
      inter_face := ?_ }
  · intro P hP
    exact C.nonempty P (Finset.mem_filter.mp hP).1
  · intro P hP
    exact C.rational P (Finset.mem_filter.mp hP).1
  · intro P hP F hF
    obtain ⟨hPC, hdim⟩ := Finset.mem_filter.mp hP
    refine Finset.mem_filter.mpr ⟨C.face_closed P hPC F hF, ?_⟩
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le
      (affineSpan_mono ℝ (isPolyhedralFace_iff.mp hF).2.subset))
    exact (Nat.add_le_add_right hle k).trans hdim
  · intro P hP Q hQ hne
    exact C.inter_face P (Finset.mem_filter.mp hP).1 Q (Finset.mem_filter.mp hQ).1 hne

/-- Membership in the codimension subcomplex is the corresponding dimension inequality. -/
@[simp]
theorem mem_codimensionAtLeast_cells (C : FinitePolyhedralComplex h) (k : ℕ) (P : Set V) :
    P ∈ (C.codimensionAtLeast k).cells ↔ P ∈ C.cells ∧
      Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V := by
  classical
  simp [codimensionAtLeast]

/-- The codimension bound zero retains the entire complex. -/
@[simp]
theorem codimensionAtLeast_zero (C : FinitePolyhedralComplex h) :
    C.codimensionAtLeast 0 = C := by
  have := h.finiteDimensional
  apply ext
  ext P
  simp [Submodule.finrank_le]

/-- Every exact-codimension cell belongs to the corresponding codimension subcomplex. -/
theorem cellsOfCodimension_subset_codimensionAtLeast_cells
    (C : FinitePolyhedralComplex h) (k : ℕ) :
    C.cellsOfCodimension k ⊆ (C.codimensionAtLeast k).cells := by
  intro P hP
  obtain ⟨hPC, hdim⟩ := (C.mem_cellsOfCodimension k P).mp hP
  exact (C.mem_codimensionAtLeast_cells k P).mpr ⟨hPC, hdim.le⟩

/-- Increasing the codimension bound gives a subcomplex of the previous one. -/
theorem codimensionAtLeast_cells_antitone (C : FinitePolyhedralComplex h) :
    Antitone (fun k => (C.codimensionAtLeast k).cells) := by
  intro k l hkl P hP
  obtain ⟨hPC, hdim⟩ := (C.mem_codimensionAtLeast_cells l P).mp hP
  exact (C.mem_codimensionAtLeast_cells k P).mpr
    ⟨hPC, (Nat.add_le_add_left hkl _).trans hdim⟩

/-- Every codimension subcomplex is a weak refinement of the original complex. -/
theorem codimensionAtLeast_isWeakRefinement (C : FinitePolyhedralComplex h) (k : ℕ) :
    (C.codimensionAtLeast k).IsWeakRefinement C := by
  apply isWeakRefinement_iff.mpr
  intro P hP
  exact ⟨P, ((C.mem_codimensionAtLeast_cells k P).mp hP).1, Set.Subset.rfl⟩

/-- The relative boundary of a cell of codimension at least `k` lies in the
subcomplex of codimension at least `k + 1`. -/
theorem intrinsicFrontier_subset_support_codimensionAtLeast (C : FinitePolyhedralComplex h)
    {P : Set V} (hP : P ∈ C.cells) (k : ℕ)
    (hdim : Module.finrank ℝ (affineSpan ℝ P).direction + k ≤ Module.finrank ℝ V) :
    intrinsicFrontier ℝ P ⊆ (C.codimensionAtLeast (k + 1)).support := by
  have := h.finiteDimensional
  obtain ⟨n, g, hpres⟩ := TauCeti.isConvexPolyhedron_iff.mp (C.isConvexPolyhedron hP)
  intro x hx
  rw [Mei.Convex.intrinsicFrontier_eq_iUnion_active g hpres] at hx
  obtain ⟨j, ⟨p, hp, hgp⟩, hxP, hgx⟩ := Set.mem_iUnion₂.mp hx
  let F := {y ∈ P | g j y = 0}
  have hxF : x ∈ F := ⟨hxP, hgx⟩
  have hex : IsExposed ℝ P F := by
    dsimp only [F]
    rw [hpres]
    simpa using Mei.Convex.isExposed_setOf_active g {j}
  have hlt : Module.finrank ℝ (affineSpan ℝ F).direction <
      Module.finrank ℝ (affineSpan ℝ P).direction :=
    (g j).toAffineMap.finrank_direction_inter_zero_lt ⟨x, hxP, hgx⟩ ⟨p, hp, hgp.ne⟩
  apply mem_support.mpr
  refine ⟨F, (C.mem_codimensionAtLeast_cells (k + 1) F).mpr
    ⟨C.face_closed P hP F (isPolyhedralFace_iff.mpr ⟨⟨x, hxF⟩, hex⟩), ?_⟩, hxF⟩
  omega

/-- The singular support of the wall family lies in the support of the subcomplex
of cells of codimension at least two. -/
theorem singularSupport_walls_subset_support_codimensionAtLeast (C : FinitePolyhedralComplex h) :
    Mei.Convex.singularSupport (fun W : C.walls => (W : Set V)) ⊆
      (C.codimensionAtLeast 2).support := by
  have := h.finiteDimensional
  intro x hx
  rcases Mei.Convex.mem_singularSupport.mp hx with ⟨P, hxP⟩ | ⟨P, Q, hne, hxP, hxQ⟩
  · exact C.intrinsicFrontier_subset_support_codimensionAtLeast
      (C.mem_cells_of_mem_walls P.property) 1
      (C.finrank_direction_add_one_of_mem_walls P.property).le hxP
  · have hdimP := C.finrank_direction_add_one_of_mem_walls P.property
    have hdimQ := C.finrank_direction_add_one_of_mem_walls Q.property
    have hlt := (affineSpan ℝ (P : Set V)).finrank_direction_inf_add_one_lt
      (affineSpan ℝ (Q : Set V)) hdimP hdimQ hne
    have hle := Submodule.finrank_mono (AffineSubspace.direction_le
      (le_inf (affineSpan_mono ℝ Set.inter_subset_left)
        (affineSpan_mono ℝ Set.inter_subset_right) :
          affineSpan ℝ ((P : Set V) ∩ Q) ≤ affineSpan ℝ (P : Set V) ⊓ affineSpan ℝ (Q : Set V)))
    apply mem_support.mpr
    refine ⟨(P : Set V) ∩ Q, (C.mem_codimensionAtLeast_cells 2 _).mpr
      ⟨C.inter_mem_cells (C.mem_cells_of_mem_walls P.property)
        (C.mem_cells_of_mem_walls Q.property) ⟨x, hxP, hxQ⟩, ?_⟩, hxP, hxQ⟩
    omega

/-- Away from the singular support there is at most one incident wall, including
when different walls have the same supporting hyperplane. -/
theorem eq_of_mem_wall_of_notMem_singularSupport (C : FinitePolyhedralComplex h)
    {P Q : C.walls} {x : V} (hxP : x ∈ (P : Set V)) (hxQ : x ∈ (Q : Set V))
    (hx : x ∉ Mei.Convex.singularSupport (fun W : C.walls => (W : Set V))) : P = Q := by
  apply Subtype.ext
  exact C.eq_of_mem_intrinsicInterior
    (C.mem_cells_of_mem_walls P.property) (C.mem_cells_of_mem_walls Q.property)
    (Mei.Convex.mem_intrinsicInterior_of_notMem_singularSupport hxP hx)
    (Mei.Convex.mem_intrinsicInterior_of_notMem_singularSupport hxQ hx)

end Mei.FinitePolyhedralComplex
