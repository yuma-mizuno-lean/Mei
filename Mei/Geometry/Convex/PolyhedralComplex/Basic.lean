/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mathlib.Analysis.Convex.Exposed

/-! # Finite rational-normal polyhedral complexes

Cells are actual nonempty closed rational-normal polyhedra. Every nonempty
exposed face is retained, and nonempty pairwise intersections are common faces.
No boundedness, full-dimensionality, or salience condition is imposed.
-/

public section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- A nonempty exposed face, with the nonempty convention used for cells. -/
def IsPolyhedralFace (P F : Set V) : Prop := F.Nonempty ∧ IsExposed ℝ P F

/-- A polyhedral face is precisely a nonempty exposed subset. -/
theorem isPolyhedralFace_iff {P F : Set V} :
    IsPolyhedralFace P F ↔ F.Nonempty ∧ IsExposed ℝ P F := Iff.rfl

/-- A finite complex of actual rational-normal polyhedra, allowing unbounded cells and lineality. -/
structure FinitePolyhedralComplex (h : TauCeti.Toric.IsIntegralLattice i) where
  /-- The finite collection of closed cell carriers. -/
  cells : Finset (Set V)
  /-- Empty cells are excluded. -/
  nonempty : ∀ P ∈ cells, P.Nonempty
  /-- Every cell admits a rational-normal finite affine presentation. -/
  rational : ∀ P ∈ cells, IsRationalNormalPolyhedron h P
  /-- Every nonempty exposed face of every cell is a cell. -/
  face_closed : ∀ P ∈ cells, ∀ F, IsPolyhedralFace P F → F ∈ cells
  /-- Nonempty intersections are exposed faces of the first cell; swapping cells gives the other. -/
  inter_face : ∀ P ∈ cells, ∀ Q ∈ cells, (P ∩ Q).Nonempty → IsExposed ℝ P (P ∩ Q)

namespace FinitePolyhedralComplex

variable {h : TauCeti.Toric.IsIntegralLattice i}

/-- The collection of actual carriers determines a complex. -/
@[ext (iff := false)]
theorem ext {C D : FinitePolyhedralComplex h} (hcells : C.cells = D.cells) : C = D := by
  cases C
  cases D
  cases hcells
  rfl

/-- The support of a complex is the union of its cell carriers. -/
def support (C : FinitePolyhedralComplex h) : Set V := ⋃ P ∈ C.cells, P

/-- A point lies in the support exactly when it lies in one cell. -/
@[simp]
theorem mem_support {C : FinitePolyhedralComplex h} {x : V} :
    x ∈ C.support ↔ ∃ P ∈ C.cells, x ∈ P := by simp [support]

/-- Each cell is a convex polyhedron in the existing supplier's sense. -/
theorem isConvexPolyhedron (C : FinitePolyhedralComplex h) {P : Set V} (hP : P ∈ C.cells) :
    TauCeti.IsConvexPolyhedron P := by
  obtain ⟨Q, rfl⟩ := isRationalNormalPolyhedron_iff.mp (C.rational P hP)
  exact Q.isConvexPolyhedron

/-- A cell contained in another cell is a nonempty face of that cell. -/
theorem face_of_subset (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hPQ : P ⊆ Q) : IsPolyhedralFace Q P := by
  have heq : Q ∩ P = P := Set.inter_eq_right.mpr hPQ
  have hne : (Q ∩ P).Nonempty := by rw [heq]; exact C.nonempty P hP
  refine ⟨C.nonempty P hP, ?_⟩
  simpa only [heq] using C.inter_face Q hQ P hP hne

/-- Weak refinement means every new cell is contained in an old cell. -/
def IsWeakRefinement (C D : FinitePolyhedralComplex h) : Prop :=
  ∀ P ∈ C.cells, ∃ Q ∈ D.cells, P ⊆ Q

/-- The public cellwise characterization of weak refinement. -/
theorem isWeakRefinement_iff {C D : FinitePolyhedralComplex h} :
    C.IsWeakRefinement D ↔ ∀ P ∈ C.cells, ∃ Q ∈ D.cells, P ⊆ Q := Iff.rfl

/-- A subdivision is a weak refinement with unchanged support. -/
def IsSubdivision (C D : FinitePolyhedralComplex h) : Prop :=
  C.IsWeakRefinement D ∧ C.support = D.support

/-- The public characterization of subdivision. -/
theorem isSubdivision_iff {C D : FinitePolyhedralComplex h} :
    C.IsSubdivision D ↔ C.IsWeakRefinement D ∧ C.support = D.support := Iff.rfl

/-- Every complex weakly refines itself. -/
theorem IsWeakRefinement.refl (C : FinitePolyhedralComplex h) : C.IsWeakRefinement C :=
  fun P hP => ⟨P, hP, Set.Subset.rfl⟩

/-- Cellwise weak refinement is transitive. -/
theorem IsWeakRefinement.trans {C D E : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) (hDE : D.IsWeakRefinement E) : C.IsWeakRefinement E := by
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := hCD P hP
  obtain ⟨R, hR, hQR⟩ := hDE Q hQ
  exact ⟨R, hR, hPQ.trans hQR⟩

/-- Weak refinement includes the support of the finer complex in that of the coarser one. -/
theorem IsWeakRefinement.support_subset {C D : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) : C.support ⊆ D.support := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := mem_support.mp hx
  obtain ⟨Q, hQ, hPQ⟩ := hCD P hP
  exact mem_support.mpr ⟨Q, hQ, hPQ hxP⟩

/-- Mutual weak refinement forces equality because both complexes contain all faces. -/
theorem IsWeakRefinement.antisymm {C D : FinitePolyhedralComplex h}
    (hCD : C.IsWeakRefinement D) (hDC : D.IsWeakRefinement C) : C = D := by
  have hsubset {C D : FinitePolyhedralComplex h}
      (hCD : C.IsWeakRefinement D) (hDC : D.IsWeakRefinement C) : C.cells ⊆ D.cells := by
    intro P hP
    obtain ⟨Q, hQ, hPQ⟩ := hCD P hP
    obtain ⟨R, hR, hQR⟩ := hDC Q hQ
    have hface := C.face_of_subset hP hR (hPQ.trans hQR)
    have hexposed : IsExposed ℝ Q P := by
      simpa only [Set.inter_eq_right.mpr hQR] using hface.2.inter_left hPQ
    exact D.face_closed Q hQ P ⟨hface.1, hexposed⟩
  exact ext (Finset.Subset.antisymm (hsubset hCD hDC) (hsubset hDC hCD))

/-- Subdivision is reflexive. -/
theorem IsSubdivision.refl (C : FinitePolyhedralComplex h) : C.IsSubdivision C :=
  ⟨IsWeakRefinement.refl C, rfl⟩

/-- Subdivisions compose. -/
theorem IsSubdivision.trans {C D E : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) (hDE : D.IsSubdivision E) : C.IsSubdivision E :=
  ⟨hCD.1.trans hDE.1, hCD.2.trans hDE.2⟩

/-- Mutual subdivision forces equality of the complexes. -/
theorem IsSubdivision.antisymm {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) (hDC : D.IsSubdivision C) : C = D :=
  hCD.1.antisymm hDC.1

end FinitePolyhedralComplex

end Mei
