/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel.Homogeneous
public import Mei.Geometry.ScatteringDiagram.KS.Completion.Map

/-!
# Coefficient naturality of homogeneous KS representatives

Extracting the homogeneous indexed walls of a completed KS diagram commutes
with a degree-preserving Lie homomorphism. This is an equality of presentations
on the original degree-and-wall indices, retaining supports and primitive rays
even when coefficients vanish. Neither consistency nor abelian rays is required.

The finite wall realizations choose completed lifts independently. Their
homogeneous factors at retained degrees are nevertheless canonical:
`CompletedDiagram.homogeneousWall_label_eq` compares any two such lifts, and
`GradedLieHom.completedMap_homogeneousFactor` maps the resulting factors.
Thus naturality does not require functorial choices of completed lifts.

This is the coefficient compatibility of the homogeneous wall description in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), using the finite-order complexes of Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, §§2–3
(arXiv:1603.00416v4).
-/

public noncomputable section

namespace Mei.CompletedDiagram

universe u

variable {N V R : Type*} {L L' : Type u} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRing L'] [LieAlgebra R L'] [LieAlgebra ℚ L'] [IsScalarTower ℚ R L']
  [DecidableEq N] [Module.Free ℤ N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N}
  {ℒ : N → Submodule R L} {ℳ : N → Submodule R L'}
  [GradedLieAlgebra ℒ] [GradedLieAlgebra ℳ]
  [IsPositiveGrading d ℒ] [IsPositiveGrading d ℳ]
  {C : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)
  (f : GradedLieHom (PositiveDegreeMap.id d) ℒ ℳ)

/-- Homogeneous wall extraction commutes with coefficient change as an equality
of indexed walls, despite the independent choices of finite-label lifts. -/
@[simp]
theorem homogeneousWall_mapDiagram (a : HomogeneousWallIndex d C) :
    (D.mapDiagram f).homogeneousWall a = (D.homogeneousWall a).map f := by
  apply IndexedWall.ext
  · simp only [homogeneousWall_ray, mapDiagram_diagram, KSComplex.wallRay_map,
      IndexedWall.map_ray]
  · simp only [homogeneousWall_support, IndexedWall.map_support]
  · calc
      _ = d.homogeneousFactor ℳ
          (f.completedMap ((D.diagram (d.degree a.1.val).toNat).indexedWall a.2).label)
          a.1.val := by
        apply (D.mapDiagram f).homogeneousWall_label_eq a
        rw [f.projection_completedMap_of_le (d.degree a.1.val).toNat
          (a := (d.degree a.1.val).toNat) (by simp),
          KSComplex.projection_indexedWall_label, mapDiagram_diagram, KSComplex.map_label]
      _ = _ := by
        simp only [IndexedWall.map_label, homogeneousWall_label,
          f.completedMap_homogeneousFactor]

/-- The chosen homogeneous presentation is natural on the same index type.
Specialization may remove active indices, but no reindexing is necessary. -/
@[simp]
theorem homogeneousPresentation_mapDiagram :
    (D.mapDiagram f).homogeneousPresentation = D.homogeneousPresentation.map f := by
  apply IndexedWallPresentation.ext
  funext a
  simp only [homogeneousPresentation_wall, IndexedWallPresentation.map_wall,
    homogeneousWall_mapDiagram]

end Mei.CompletedDiagram
