/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Incidence
public import Mei.Geometry.Convex.PolyhedralCochain.Pairing

/-!
# Signed boundary pairings at an isolated joint

An isolating triangular meridian of a finite polyhedral complex is a transverse
test for every oriented joint cell, hence for every signed boundary facet of
every wall cell. Its pairing with the signed boundary of a wall presentation
is exactly the sum of the incidences supported on the isolated joint. Each
incidence retains its own conormal sign and its parent's coefficient.

This identifies the boundary side of the comparison between joint holonomy
and central crossing defects. It uses actual geometric meridians, without
requiring a Stokes identity or a coboundary on cochain classes.

The geometric inputs are
`FinitePolyhedralComplex.exists_positive_isolating_joint_triangle` and
`OrientedCell.isTransverse_of_isCompl`; the finite sum uses
`PolyhedralCochain.coboundaryPresentation` and
`OrientedCell.intersectionPairing`. No choice of a common orientation on all
joint cells is required.
-/

public section

noncomputable section

open Set Module

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

namespace OrientedCell

variable {k : ℕ}

/-- A simplex complementary to an isolated cell is transverse to every cell
of the same codimension in the complex, regardless of its orientation. -/
theorem isTransverse_of_isolating_simplex (σ : OrientedCell h k)
    (C : FinitePolyhedralComplex h) (hσ : σ.carrier ∈ C.cellsOfCodimension k)
    {J : Set V} (s : Affine.Simplex ℝ V k)
    (hc : IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)))
    (hf : Disjoint (convexHull ℝ (range s.points)) (intrinsicFrontier ℝ J))
    (ho : ∀ Q ∈ C.cellsOfCodimension k, Q ≠ J →
      Disjoint (convexHull ℝ (range s.points)) Q) :
    σ.IsTransverse s.points := by
  by_cases he : σ.carrier = J
  · exact σ.isTransverse_of_isCompl s (he ▸ hc) (he ▸ hf)
  · exact σ.isTransverse_of_disjoint (ho σ.carrier hσ he)

end OrientedCell

namespace PolyhedralCochain

variable {k : ℕ} {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The signed boundary presentation of cells on a complex is transverse to
an isolating simplex of codimension one higher. Cancellation of repeated
oriented facets in the presentation causes no additional condition. -/
theorem isTransverse_coboundaryPresentation (C : FinitePolyhedralComplex h)
    (f : OrientedCell h k →₀ E) (hfold : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    {J : Set V} (s : Affine.Simplex ℝ V (k + 1))
    (hc : IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)))
    (hf : Disjoint (convexHull ℝ (range s.points)) (intrinsicFrontier ℝ J))
    (ho : ∀ Q ∈ C.cellsOfCodimension (k + 1), Q ≠ J →
      Disjoint (convexHull ℝ (range s.points)) Q) :
    ∀ τ ∈ (coboundaryPresentation (R := R) f).support, τ.IsTransverse s.points := by
  classical
  rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, coboundaryPresentation_single]
  intro τ hτ
  obtain ⟨σ, hσ, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
  obtain ⟨υ, hυ, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
  obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hτ
  exact τ.isTransverse_of_isolating_simplex C
    (σ.mem_cellsOfCodimension_of_mem_boundaryFacets C (hfold σ hσ) hυ) s hc hf ho

/-- Pairing a signed boundary with an isolating test retains precisely the
incidences on the isolated cell. The conormal signs are evaluated on
the test frame, with no determinant magnitude or merging of parent indices.
The test may be degenerate; transversality is supplied separately by
`isTransverse_coboundaryPresentation` for complementary simplices. -/
theorem intersectionPairing_coboundaryPresentation_eq_sum_incident
    (C : FinitePolyhedralComplex h) (f : OrientedCell h k →₀ E)
    (hf : ∀ σ ∈ f.support, σ.carrier ∈ C.cells)
    {J : Set V} {v : Fin (k + 2) → V} (hmeet : (convexHull ℝ (range v) ∩ J).Nonempty)
    (ho : ∀ Q ∈ C.cellsOfCodimension (k + 1), Q ≠ J →
      Disjoint (convexHull ℝ (range v)) Q) :
    OrientedCell.intersectionPairing (R := R) v (coboundaryPresentation (R := R) f) =
      ∑ σ ∈ f.support, ∑ τ ∈ σ.boundaryFacets with τ.carrier = J,
        (τ.orientation.evalSign (fun j : Fin (k + 1) => v j.succ - v 0) : ℤ) • f σ := by
  classical
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, coboundaryPresentation_single,
    OrientedCell.intersectionPairing_single]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro τ hτ
  by_cases he : τ.carrier = J
  · rw [ite_eq_left he, OrientedCell.intersectionIndex_of_nonempty (he ▸ hmeet)]
  · rw [ite_eq_right he, OrientedCell.intersectionIndex_of_disjoint
      (ho τ.carrier (σ.mem_cellsOfCodimension_of_mem_boundaryFacets C (hf σ hσ) hτ) he),
      zero_smul]

end PolyhedralCochain

end Mei
