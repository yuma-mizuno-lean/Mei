/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.Basic
public import Mei.Geometry.Convex.Polyhedron.CommonPath

/-!
# Completed KS diagrams and transport

A `CompletedDiagram` labels a sequence of finite conical complexes. Successive
cutoffs agree on common admissible vertex lists after projecting the labels;
the complexes need not stabilize or refine one another. All-order paths use
`CommonWallComplement`, so that each segment is admissible separately at every
cutoff. Their finite products assemble to the existing completed BCH group.

For a diagram consistent at every order, transport between common allowed
points is independent of the all-order path and projects to the product on
any finite-order admissible path. Common paths exist by the countable-family
Baire argument. In particular, both degree points are allowed at all orders.

This follows the compatible finite-diagram description in Tom Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), Definition 2.3 and §§2.9–2.11.
It uses `KSComplex`, `FiniteWallDiagram.pathProduct`,
`CommonWallComplement.exists_length_eq_two` and the compatible-family carrier
`Mei.completedGroup` obtained from Mathlib's `GrpCat.sectionsSubgroup`.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (s : KSSpace h) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (C : ℕ → FinitePolyhedralComplex h)

/-- A sequence of KS complexes agreeing at successive orders on every common
admissible vertex list. No stabilization or refinement of the complexes is required. -/
structure CompletedDiagram where
  /-- The finite KS diagram at each cutoff. -/
  diagram : ∀ k, KSComplex s d ℒ (C k) k
  /-- Projecting a higher product agrees with the lower product on a common path. -/
  compatible : ∀ k
    {x y : WallComplement (fun P : (C k).walls => (P : Set V))}
    {x' y' : WallComplement (fun P : (C (k + 1)).walls => (P : Set V))}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y'),
    p.vertices.map WallComplement.val = q.vertices.map WallComplement.val →
      (d.truncationMap ℒ (Nat.le_succ k)).bchGroupMap
        ((diagram (k + 1)).toFiniteWallDiagram.pathProduct q) =
          (diagram k).toFiniteWallDiagram.pathProduct p

namespace CompletedDiagram

variable {s d ℒ C}

/-- The finite KS diagrams determine a completed diagram. -/
@[ext]
theorem ext {D E : CompletedDiagram s d ℒ C}
    (hdiagram : D.diagram = E.diagram) : D = E := by
  cases D
  cases E
  cases hdiagram
  rfl

/-- A point off every wall at every cutoff. The geometry depends only on the
sequence of complexes, so the same path types can be used for different labels. -/
abbrev Point (C : ℕ → FinitePolyhedralComplex h) :=
  CommonWallComplement (fun k => fun P : (C k).walls => (P : Set V))

variable (D : CompletedDiagram s d ℒ C)

omit [DecidableEq N] in
/-- Common allowed endpoints admit a single path admissible at every order. -/
theorem exists_path (x y : Point C) : Nonempty (Quiver.Path x y) := by
  classical
  let := h.finiteDimensional
  obtain ⟨p, _⟩ := CommonWallComplement.exists_length_eq_two
    (fun k P => (C k).isConvexPolyhedron ((C k).mem_cells_of_mem_walls P.property))
    (fun k P => (C k).finrank_direction_add_one_of_mem_walls P.property) x y
  exact ⟨p⟩

/-- The degree point is allowed simultaneously at all cutoffs. -/
def degreePoint : Point C :=
  ⟨s.degreePoint d, fun k P => (D.diagram k).degreePoint_not_mem P⟩

@[simp]
theorem degreePoint_val : D.degreePoint.val = s.degreePoint d := (rfl)

/-- The negative degree point is also allowed simultaneously at all cutoffs. -/
def negDegreePoint : Point C :=
  ⟨-s.degreePoint d, fun k P => (D.diagram k).neg_degreePoint_not_mem P⟩

@[simp]
theorem negDegreePoint_val : D.negDegreePoint.val = -s.degreePoint d := (rfl)

variable {x y z : Point C}

/-- Products on an all-order path are compatible with every cutoff transition. -/
theorem truncation_pathProduct (p : Quiver.Path x y) {k l : ℕ} (hkl : k ≤ l) :
    (d.truncationMap ℒ hkl).bchGroupMap
      ((D.diagram l).toFiniteWallDiagram.pathProduct
        ((CommonWallComplement.projectionPrefunctor l).mapPath p)) =
      (D.diagram k).toFiniteWallDiagram.pathProduct
        ((CommonWallComplement.projectionPrefunctor k).mapPath p) := by
  induction l with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hkl
    simp
  | succ l ih =>
    by_cases h : k ≤ l
    · rw [← d.truncationMap_comp ℒ h (Nat.le_succ l), LieHom.bchGroupMap_comp,
        MonoidHom.comp_apply]
      have hs := D.compatible l
        ((CommonWallComplement.projectionPrefunctor l).mapPath p)
        ((CommonWallComplement.projectionPrefunctor (l + 1)).mapPath p)
        ((CommonWallComplement.vertices_projection l p).trans
          (CommonWallComplement.vertices_projection (l + 1) p).symm)
      rw [hs, ih h]
    · obtain rfl : k = l + 1 := by omega
      simp

/-- The complete path product, with the first crossing rightmost. -/
def pathProduct (p : Quiver.Path x y) : d.completedBCHGroup ℒ :=
  ⟨fun k => (D.diagram k).toFiniteWallDiagram.pathProduct
      ((CommonWallComplement.projectionPrefunctor k).mapPath p),
    (mem_completedGroup_iff _ _).mpr (fun _ _ hkl => D.truncation_pathProduct p hkl)⟩

/-- Projection recovers exactly the existing geometric finite-order product. -/
@[simp]
theorem projection_pathProduct (k : ℕ) (p : Quiver.Path x y) :
    CompletedGroup.projection k (D.pathProduct p) =
      (D.diagram k).toFiniteWallDiagram.pathProduct
        ((CommonWallComplement.projectionPrefunctor k).mapPath p) := by
  rw [CompletedGroup.projection_apply]
  rfl

-- In the next three proofs, the final reflexivity computes the categorical
-- tower group operations as the concrete BCH group operations.
@[simp]
theorem pathProduct_nil : D.pathProduct (Quiver.Path.nil : Quiver.Path x x) = 1 := by
  apply CompletedGroup.ext
  intro k
  simp
  rfl

/-- Concatenation puts the later path's product on the left. -/
@[simp]
theorem pathProduct_comp (p : Quiver.Path x y) (q : Quiver.Path y z) :
    D.pathProduct (p.comp q) = D.pathProduct q * D.pathProduct p := by
  apply CompletedGroup.ext
  intro k
  simp
  rfl

/-- Reversal inverts the complete path product. -/
@[simp]
theorem pathProduct_reverse (p : Quiver.Path x y) :
    D.pathProduct p.reverse = (D.pathProduct p)⁻¹ := by
  apply CompletedGroup.ext
  intro k
  simp
  rfl

/-- Consistency of a completed diagram is consistency at every finite order. -/
def Consistent : Prop := ∀ k, (D.diagram k).toFiniteWallDiagram.Consistent

/-- The finite-order characterization of completed consistency. -/
theorem consistent_iff : D.Consistent ↔
    ∀ k, (D.diagram k).toFiniteWallDiagram.Consistent := Iff.rfl

variable {D}

/-- Finite-order consistency makes complete products depend only on endpoints. -/
theorem Consistent.pathProduct_eq (hD : D.Consistent) (p q : Quiver.Path x y) :
    D.pathProduct p = D.pathProduct q := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_pathProduct]
  exact (FiniteWallDiagram.consistent_def _).mp (hD k) _ _

variable (D)

/-- Endpoint transport in a diagram consistent at every order. -/
def transport (_hD : D.Consistent) (x y : Point C) : d.completedBCHGroup ℒ :=
  D.pathProduct (exists_path x y).some

/-- Transport equals the complete product on any all-order admissible path. -/
theorem transport_eq_pathProduct (hD : D.Consistent) (p : Quiver.Path x y) :
    D.transport hD x y = D.pathProduct p := by
  rw [transport]
  exact hD.pathProduct_eq _ p

/-- At a finite cutoff, transport can be computed with any admissible path,
including one that is not admissible at the other orders. -/
theorem projection_transport (hD : D.Consistent) (k : ℕ)
    (p : AdmissiblePLPath (CommonWallComplement.projection k x)
      (CommonWallComplement.projection k y)) :
    CompletedGroup.projection k (D.transport hD x y) =
      (D.diagram k).toFiniteWallDiagram.pathProduct p := by
  rw [transport, projection_pathProduct]
  exact (FiniteWallDiagram.consistent_def _).mp (hD k) _ _

@[simp]
theorem transport_self (hD : D.Consistent) (x : Point C) : D.transport hD x x = 1 := by
  rw [D.transport_eq_pathProduct hD Quiver.Path.nil, pathProduct_nil]

/-- Transport composes in traversal order. -/
theorem transport_comp (hD : D.Consistent) (x y z : Point C) :
    D.transport hD x z = D.transport hD y z * D.transport hD x y := by
  obtain ⟨p⟩ := exists_path x y
  obtain ⟨q⟩ := exists_path y z
  rw [D.transport_eq_pathProduct hD (p.comp q), pathProduct_comp,
    D.transport_eq_pathProduct hD p, D.transport_eq_pathProduct hD q]

/-- Interchanging the endpoints inverts transport. -/
theorem transport_swap (hD : D.Consistent) (x y : Point C) :
    D.transport hD y x = (D.transport hD x y)⁻¹ := by
  obtain ⟨p⟩ := exists_path x y
  rw [D.transport_eq_pathProduct hD p.reverse, pathProduct_reverse,
    D.transport_eq_pathProduct hD p]

end CompletedDiagram
end Mei
