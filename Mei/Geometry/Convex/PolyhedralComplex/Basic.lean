/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Analysis.Convex.Exposed
public import Mathlib.Geometry.Convex.Cone.Pointed

/-! # Finite rational-normal polyhedral complexes

Cells are actual nonempty closed rational-normal polyhedra. Every nonempty
exposed face is retained, and nonempty pairwise intersections are common faces.
Relative interiors of distinct cells are disjoint.
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

/-- A nonempty intersection of two cells is again a cell. -/
theorem inter_mem_cells (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hne : (P ∩ Q).Nonempty) :
    P ∩ Q ∈ C.cells :=
  C.face_closed P hP (P ∩ Q) (isPolyhedralFace_iff.mpr ⟨hne, C.inter_face P hP Q hQ hne⟩)

/-- Cells with a common relative-interior point are equal, without a dimension assumption. -/
theorem eq_of_mem_intrinsicInterior (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) {x : V}
    (hxP : x ∈ intrinsicInterior ℝ P) (hxQ : x ∈ intrinsicInterior ℝ Q) : P = Q := by
  have hx : x ∈ P ∩ Q := ⟨intrinsicInterior_subset hxP, intrinsicInterior_subset hxQ⟩
  have hleft := (C.inter_face P hP Q hQ ⟨x, hx⟩).eq_of_mem_intrinsicInterior hx hxP
  have hright := (C.inter_face Q hQ P hP ⟨x, hx.2, hx.1⟩).eq_of_mem_intrinsicInterior
    ⟨hx.2, hx.1⟩ hxQ
  exact hleft.symm.trans ((Set.inter_comm P Q).trans hright)

/-- The relative interiors of distinct cells are disjoint. -/
theorem disjoint_intrinsicInterior (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hne : P ≠ Q) :
    Disjoint (intrinsicInterior ℝ P) (intrinsicInterior ℝ Q) := by
  rw [Set.disjoint_left]
  exact fun x hxP hxQ => hne (C.eq_of_mem_intrinsicInterior hP hQ hxP hxQ)

/-- A cell contained in another cell is a nonempty face of that cell. -/
theorem face_of_subset (C : FinitePolyhedralComplex h) {P Q : Set V}
    (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hPQ : P ⊆ Q) : IsPolyhedralFace Q P := by
  have heq : Q ∩ P = P := Set.inter_eq_right.mpr hPQ
  have hne : (Q ∩ P).Nonempty := by rw [heq]; exact C.nonempty P hP
  refine ⟨C.nonempty P hP, ?_⟩
  simpa only [heq] using C.inter_face Q hQ P hP hne

/-- Every cell is the carrier of a pointed cone with apex zero. -/
def IsConical (C : FinitePolyhedralComplex h) : Prop :=
  ∀ P ∈ C.cells, ∃ σ : PointedCone ℝ V, (σ : Set V) = P

/-- Conicality means that each actual cell carrier is a cone. -/
theorem isConical_iff (C : FinitePolyhedralComplex h) :
    C.IsConical ↔ ∀ P ∈ C.cells, ∃ σ : PointedCone ℝ V, (σ : Set V) = P := Iff.rfl

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

/-- In a subdivision every point of an old cell lies in a new cell contained in it. -/
theorem IsSubdivision.exists_mem_cells_subset {C D : FinitePolyhedralComplex h}
    (hCD : C.IsSubdivision D) {P : Set V}
    (hP : P ∈ D.cells) {x : V} (hx : x ∈ P) : ∃ Q ∈ C.cells, Q ⊆ P ∧ x ∈ Q := by
  obtain ⟨hrefine, hsupport⟩ := isSubdivision_iff.mp hCD
  obtain ⟨Q, hQ, hxQ⟩ := mem_support.mp (hsupport ▸ mem_support.mpr ⟨P, hP, hx⟩)
  obtain ⟨R, hR, hQR⟩ := isWeakRefinement_iff.mp hrefine Q hQ
  have hF : IsExposed ℝ Q ((R ∩ P) ∩ Q) := by
    simpa only [Set.inter_eq_right.mpr hQR] using
      (D.inter_face R hR P hP ⟨x, hQR hxQ, hx⟩).inter_inter (IsExposed.refl (𝕜 := ℝ) Q)
  exact ⟨(R ∩ P) ∩ Q, C.face_closed Q hQ _ (isPolyhedralFace_iff.mpr ⟨⟨x, ⟨hQR hxQ, hx⟩, hxQ⟩, hF⟩),
    fun _ hy => hy.1.2, ⟨hQR hxQ, hx⟩, hxQ⟩

/-- Weak refinement carries a partial-order structure on actual complexes. -/
@[instance_reducible]
def weakRefinementPartialOrder : PartialOrder (FinitePolyhedralComplex h) where
  le := IsWeakRefinement
  le_refl := IsWeakRefinement.refl
  le_trans _ _ _ := IsWeakRefinement.trans
  le_antisymm _ _ := IsWeakRefinement.antisymm

/-- Subdivision carries its own partial-order structure, with support equality built in. -/
@[instance_reducible]
def subdivisionPartialOrder : PartialOrder (FinitePolyhedralComplex h) where
  le := IsSubdivision
  le_refl := IsSubdivision.refl
  le_trans _ _ _ := IsSubdivision.trans
  le_antisymm _ _ := IsSubdivision.antisymm

end FinitePolyhedralComplex

end Mei
