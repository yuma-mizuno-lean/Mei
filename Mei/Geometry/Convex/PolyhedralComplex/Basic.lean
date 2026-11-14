/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Basic
public import Mei.Geometry.Convex.Polyhedron.Face
public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Analysis.Convex.Exposed
public import Mathlib.Geometry.Convex.Cone.Pointed

/-! # Finite rational-normal polyhedral complexes

Cells are actual nonempty closed rational-normal polyhedra. Every nonempty
exposed face is retained, and nonempty pairwise intersections are common faces.
Relative interiors of distinct cells are disjoint. A cell containing a relative
interior point of another contains that entire cell; this incidence condition
holds uniformly for all cells encountered in a neighborhood of the point.
No boundedness, full-dimensionality, or salience condition is imposed.
-/

public section

open TauCeti (IsRationalNormalPolyhedron)

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V}

/-- A polyhedral face is precisely a nonempty exposed subset. -/
theorem isPolyhedralFace_iff {P F : Set V} :
    IsPolyhedralFace P F ↔ F.Nonempty ∧ IsExposed ℝ P F :=
  ⟨fun h => ⟨h.nonempty, h.isExposed⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A convex polyhedron has finitely many nonempty exposed faces. -/
theorem finite_isPolyhedralFace {P : Set V} (hP : TauCeti.IsConvexPolyhedron P) :
    {F : Set V | IsPolyhedralFace P F}.Finite :=
  hP.finite_setOf_isExposed.subset fun _ hF => (isPolyhedralFace_iff.mp hF).2

namespace FinitePolyhedralComplex

variable {h : TauCeti.Toric.IsIntegralLattice i}

open Filter Topology in
/-- Near a relative interior point of a cell, every cell encountered contains
that entire cell. This is uniform over the finite complex. -/
theorem eventually_subset_of_mem_cell (C : FinitePolyhedralComplex h) {P : Set V}
    (hP : P ∈ C.cells) {x : V} (hx : x ∈ intrinsicInterior ℝ P) :
    ∀ᶠ y in 𝓝 x, ∀ Q ∈ C.cells, y ∈ Q → P ⊆ Q := by
  have hnear := (locallyFinite_of_finite (fun Q : C.cells => (Q : Set V))).eventually_subset
    (fun Q => (C.isConvexPolyhedron Q.property).isClosed) x
  filter_upwards [hnear] with y hy Q hQ hyQ
  exact C.subset_of_mem_intrinsicInterior hP hQ hx (hy (a := ⟨Q, hQ⟩) hyQ)

open Set in
/-- Two distinct cells with a common facet meet exactly in that facet.
The dimension condition is relative, so the cells need not be full dimensional. -/
theorem inter_eq_of_common_facet (C : FinitePolyhedralComplex h)
    {P Q Q' : Set V} (hP : P ∈ C.cells) (hQ : Q ∈ C.cells) (hQ' : Q' ∈ C.cells)
    (hPQ : P ⊆ Q) (hPQ' : P ⊆ Q') (hne : Q ≠ Q')
    (hdim : Module.finrank ℝ (affineSpan ℝ Q).direction =
      Module.finrank ℝ (affineSpan ℝ P).direction + 1)
    (hdim' : Module.finrank ℝ (affineSpan ℝ Q').direction =
      Module.finrank ℝ (affineSpan ℝ P).direction + 1) : Q ∩ Q' = P := by
  let := h.finiteDimensional
  have hPI : P ⊆ Q ∩ Q' := subset_inter hPQ hPQ'
  have hIne := (C.nonempty P hP).mono hPI
  have hI := C.inter_mem_cells hQ hQ' hIne
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le
    (affineSpan_mono ℝ inter_subset_left : affineSpan ℝ (Q ∩ Q') ≤ affineSpan ℝ Q))
  have hlt : Module.finrank ℝ (affineSpan ℝ (Q ∩ Q')).direction <
      Module.finrank ℝ (affineSpan ℝ Q).direction := by
    apply lt_of_le_of_ne hle
    intro he
    have heQ := (C.inter_face Q hQ Q' hQ' hIne).eq_of_finrank_vectorSpan_eq hIne
      (by rw [← direction_affineSpan, ← direction_affineSpan]; exact he)
    have heQ' := (C.isPolyhedralFace_of_subset hI hQ' inter_subset_right).isExposed
      |>.eq_of_finrank_vectorSpan_eq hIne
        (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)
    exact hne (heQ.symm.trans heQ')
  have hge := Submodule.finrank_mono (AffineSubspace.direction_le (affineSpan_mono ℝ hPI))
  exact ((C.isPolyhedralFace_of_subset hP hI hPI).isExposed.eq_of_finrank_vectorSpan_eq
    (C.nonempty P hP) (by rw [← direction_affineSpan, ← direction_affineSpan]; omega)).symm

/-- Every cell is the carrier of a pointed cone with apex zero. -/
def IsConical (C : FinitePolyhedralComplex h) : Prop :=
  ∀ P ∈ C.cells, ∃ σ : PointedCone ℝ V, (σ : Set V) = P

/-- Conicality means that each actual cell carrier is a cone. -/
theorem isConical_iff (C : FinitePolyhedralComplex h) :
    C.IsConical ↔ ∀ P ∈ C.cells, ∃ σ : PointedCone ℝ V, (σ : Set V) = P := Iff.rfl

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

end TauCeti
