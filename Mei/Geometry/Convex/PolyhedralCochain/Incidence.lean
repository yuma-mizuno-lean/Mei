/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Cancellation
public import Mei.Geometry.Convex.PolyhedralComplex.Basic

/-!
# Cancellation at common facets of a polyhedral complex

Distinct, equally oriented cells in a common affine span induce opposite signed
orientations on every common facet. Consequently the two occurrences of that
facet cancel from their signed boundary sums. This supplies internal-facet
cancellation for subdivisions whose adjacent cells need not be the two pieces
of a single hyperplane cut.

`OrientedCell.boundaryFacet_eq_reverse_of_common_facet` identifies the opposite
signed orientations. The intersection is identified geometrically by
`FinitePolyhedralComplex.inter_eq_of_common_facet`. Arbitrary codimension,
real offsets, unbounded cells, lineality and arbitrary-ring module coefficients
are allowed.
-/

public section

noncomputable section

open Set Module

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

namespace FinitePolyhedralComplex

/-- A common geometric facet of two distinct, equally oriented cells of a
complex has opposite signed orientations in their boundary families. -/
theorem eq_reverse_of_mem_boundaryFacets (C : FinitePolyhedralComplex h)
    {σ τ : OrientedCell h k} (hσ : σ.carrier ∈ C.cells) (hτ : τ.carrier ∈ C.cells)
    (hne : σ.carrier ≠ τ.carrier)
    (hspan : affineSpan ℝ σ.carrier = affineSpan ℝ τ.carrier)
    (ho : σ.orientation = τ.orientation)
    {υ ω : OrientedCell h (k + 1)} (hυ : υ ∈ σ.boundaryFacets)
    (hω : ω ∈ τ.boundaryFacets) (hc : υ.carrier = ω.carrier) : υ = ω.reverse := by
  obtain ⟨F, hF, hFne, hFdim, rfl⟩ := (σ.mem_boundaryFacets υ).mp hυ
  obtain ⟨G, hG, hGne, hGdim, rfl⟩ := (τ.mem_boundaryFacets ω).mp hω
  simp only [OrientedCell.boundaryFacet_carrier] at hc
  subst G
  have hcell : F ∈ C.cells := C.face_closed σ.carrier hσ F (isPolyhedralFace_iff.mpr ⟨hFne, hF⟩)
  have hinter : σ.carrier ∩ τ.carrier = F :=
    C.inter_eq_of_common_facet hcell hσ hτ hF.subset hG.subset hne
      (by rw [direction_affineSpan, direction_affineSpan]; exact hFdim.symm)
      (by rw [direction_affineSpan, direction_affineSpan]; exact hGdim.symm)
  exact σ.boundaryFacet_eq_reverse_of_common_facet τ hF hG hFne hFdim hspan ho hinter

open Classical in
/-- The common signed facet cancels from the sum of the boundaries of two
distinct, equally oriented cells of a complex. The other facets retain their
multiplicity, even if some of their supports coincide. -/
theorem cellCoboundary_add_eq_sum_erase (C : FinitePolyhedralComplex h)
    {σ τ : OrientedCell h k} (hσ : σ.carrier ∈ C.cells) (hτ : τ.carrier ∈ C.cells)
    (hne : σ.carrier ≠ τ.carrier)
    (hspan : affineSpan ℝ σ.carrier = affineSpan ℝ τ.carrier)
    (ho : σ.orientation = τ.orientation)
    {υ ω : OrientedCell h (k + 1)} (hυ : υ ∈ σ.boundaryFacets)
    (hω : ω ∈ τ.boundaryFacets) (hc : υ.carrier = ω.carrier)
    {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] (c : E) :
    σ.cellCoboundary (R := R) c + τ.cellCoboundary c =
      (∑ ξ ∈ σ.boundaryFacets.erase υ, PolyhedralCochain.mk ξ c) +
        ∑ ξ ∈ τ.boundaryFacets.erase ω, PolyhedralCochain.mk ξ c := by
  classical
  have he : ω = υ.reverse := by
    simpa only [OrientedCell.reverse_reverse] using congrArg OrientedCell.reverse
      (C.eq_reverse_of_mem_boundaryFacets hσ hτ hne hspan ho hυ hω hc).symm
  subst ω
  exact σ.cellCoboundary_add_eq_sum_erase τ hυ hω c

end FinitePolyhedralComplex

end Mei
