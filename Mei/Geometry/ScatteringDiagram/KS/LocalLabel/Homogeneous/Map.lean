/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel.Homogeneous
public import Mei.Geometry.ScatteringDiagram.KS.Presentation.Map

/-!
# Coefficient naturality of homogeneous KS presentations

Extracting the homogeneous indexed walls of a completed KS diagram commutes
with a degree-preserving Lie homomorphism as an equality of presentations.
Although the finite ray representatives use chosen completed lifts, their
homogeneous coefficients at the retained degree are independent of those choices.
Consequently converting the homogeneous presentation after coefficient change
gives a completed diagram equivalent to the coefficient change of its conversion.
Neither consistency nor injectivity of the coefficient map is required; labels
killed by the map are retained as identity-labelled indexed walls.

The central formal inputs are `CompletedDiagram.homogeneousWall_label_eq`,
`GradedLieHom.completedMap_homogeneousFactor` and
`IndexedWallPresentation.toCompletedDiagram_map_equivalent`.
This is coefficient compatibility of the homogeneous wall description in
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), using the finite complexes of Bridgeland,
*Scattering diagrams, Hall algebras and stability conditions*, Definition 2.3
(arXiv:1603.00416v4).
-/

public noncomputable section

open Set Mei.Convex

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

/-- Each extracted homogeneous wall commutes with coefficient change, despite
the independent choices of completed lifts in the finite ray representatives. -/
@[simp]
theorem homogeneousWall_mapDiagram (a : HomogeneousWallIndex d C) :
    (D.mapDiagram f).homogeneousWall a = (D.homogeneousWall a).map f := by
  apply IndexedWall.ext
  · simp
  · simp
  · rw [IndexedWall.map_label, D.homogeneousWall_label,
      f.completedMap_homogeneousFactor]
    exact (D.mapDiagram f).homogeneousWall_label_eq a _ (by
      rw [f.projection_completedMap_of_le _ (a := (d.degree a.1.val).toNat) (by simp),
        KSComplex.projection_indexedWall_label, mapDiagram_diagram, KSComplex.map_label])

/-- Extracting the homogeneous presentation and changing coefficients commute
as an equality on the same actual-degree and finite-wall indices. No abelian-ray
hypothesis is needed. -/
@[simp]
theorem homogeneousPresentation_mapDiagram :
    (D.mapDiagram f).homogeneousPresentation = D.homogeneousPresentation.map f := by
  apply IndexedWallPresentation.ext
  funext a
  simp

/-- Conversion of the extracted homogeneous presentation is natural up to
completed path-product equivalence. Coefficient maps may kill arbitrary labels,
so the auxiliary subdivisions of the converted diagrams may differ. -/
theorem toCompletedDiagram_homogeneousPresentation_mapDiagram_equivalent
    [IsAbelianRays d ℒ] [IsAbelianRays d ℳ] :
    (D.mapDiagram f).homogeneousPresentation.toCompletedDiagram.Equivalent
      (D.homogeneousPresentation.toCompletedDiagram.mapDiagram f) := by
  rw [homogeneousPresentation_mapDiagram]
  exact D.homogeneousPresentation.toCompletedDiagram_map_equivalent f

end Mei.CompletedDiagram
