/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel.Product
public import Mei.Geometry.ScatteringDiagram.KS.LocalLabel.Equivalence
public import Mei.Geometry.ScatteringDiagram.KS.Presentation.LocalLabel
public import Mei.Geometry.ScatteringDiagram.KS.Presentation.Equivalence

/-!
# Recovering completed KS diagrams from indexed walls

For a completed KS diagram with abelian rays, converting its homogeneous indexed
wall presentation back to a completed diagram gives an equivalent diagram.
Consequently every completed KS diagram has an indexed representative, and two
completed diagrams are equivalent exactly when their homogeneous presentations
are equivalent. Together with preservation and reflection of presentation
equivalence by conversion, this identifies the two descriptions modulo their
original path-product equivalence relations, without a consistency assumption.

The proof combines `CompletedDiagram.projection_germLabel_eq_noncommProd_homogeneousWall`,
`IndexedWallPresentation.localLabel_toKSComplex` and
`CompletedDiagram.equivalent_of_germLabel_eq`. The complexes may change at every
cutoff; no common subdivision of the entire tower is required.

The indexed-wall description follows Gross–Hacking–Keel–Kontsevich,
*Canonical bases for cluster algebras*, §1.1 (arXiv:1411.1394v2), compared with
Bridgeland's finite-complex description in *Scattering diagrams, Hall algebras
and stability conditions*, Definition 2.3 (arXiv:1603.00416v4).
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.CompletedDiagram

variable {N V R L : Type*} [AddCommGroup N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq N]
  {i : (N →+ ℤ) →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {s : KSSpace h} {d : PositiveDegrees N} {ℒ : N → Submodule R L}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ] [Module.Free ℤ N]
  [IsAbelianRays d ℒ]
  {C E : ℕ → FinitePolyhedralComplex h} (D : CompletedDiagram s d ℒ C)

/-- Conversion of the homogeneous presentation recovers the entire completed
local label at every point regular for both sequences of finite complexes. -/
theorem germLabel_homogeneousPresentation (θ : V)
    (hθ : ∀ k, θ ∉ singularSupport (fun P : (C k).walls => (P : Set V)))
    (hθ' : ∀ k, θ ∉ singularSupport
      (fun P : (D.homogeneousPresentation.levelComplex k).walls => (P : Set V))) :
    D.homogeneousPresentation.toCompletedDiagram.germLabel θ hθ' = D.germLabel θ hθ := by
  apply CompletedGroup.ext
  intro k
  rw [projection_germLabel, IndexedWallPresentation.toCompletedDiagram_diagram,
    IndexedWallPresentation.localLabel_toKSComplex]
  exact (D.projection_germLabel_eq_noncommProd_homogeneousWall θ hθ k).symm

/-- Every completed KS diagram with abelian rays is recovered, up to its original
finite common-path equivalence, from its actual homogeneous indexed walls. -/
theorem toCompletedDiagram_homogeneousPresentation_equivalent :
    D.homogeneousPresentation.toCompletedDiagram.Equivalent D := by
  apply equivalent_of_germLabel_eq
  intro θ hθ' hθ
  exact D.germLabel_homogeneousPresentation θ hθ hθ'

/-- The homogeneous indexed representative is consistent exactly when the
original completed diagram is consistent. -/
@[simp]
theorem consistent_homogeneousPresentation_iff :
    D.homogeneousPresentation.toCompletedDiagram.Consistent ↔ D.Consistent := by
  have hrec := D.toCompletedDiagram_homogeneousPresentation_equivalent
  simp only [equivalent_iff, ← FiniteWallDiagram.equivalent_def] at hrec
  rw [consistent_iff, consistent_iff]
  exact forall_congr' fun k => (hrec k).consistent_iff

/-- An arbitrary indexed presentation represents a completed diagram exactly
when it is equivalent to that diagram's homogeneous presentation. This compares
presentations with different index types and retains repeated wall supports. -/
theorem toCompletedDiagram_equivalent_iff_homogeneousPresentation {ι : Type*}
    (P : IndexedWallPresentation s d ℒ ι) :
    P.toCompletedDiagram.Equivalent D ↔ P.Equivalent D.homogeneousPresentation := by
  rw [P.equivalent_iff_toCompletedDiagram D.homogeneousPresentation]
  have hrec := D.toCompletedDiagram_homogeneousPresentation_equivalent
  simp only [equivalent_iff, ← FiniteWallDiagram.equivalent_def] at hrec ⊢
  constructor
  · intro hPD k
    exact (hPD k).trans (hrec k).symm
  · intro hPD k
    exact (hPD k).trans (hrec k)

/-- The homogeneous presentation construction preserves and reflects equivalence
of arbitrary completed KS diagrams, without requiring consistency. -/
@[simp]
theorem homogeneousPresentation_equivalent_iff (F : CompletedDiagram s d ℒ E) :
    D.homogeneousPresentation.Equivalent F.homogeneousPresentation ↔ D.Equivalent F := by
  rw [← F.toCompletedDiagram_equivalent_iff_homogeneousPresentation D.homogeneousPresentation]
  have hrec := D.toCompletedDiagram_homogeneousPresentation_equivalent
  simp only [equivalent_iff, ← FiniteWallDiagram.equivalent_def] at hrec ⊢
  constructor
  · intro hDF k
    exact (hrec k).symm.trans (hDF k)
  · intro hDF k
    exact (hrec k).trans (hDF k)

end Mei.CompletedDiagram
