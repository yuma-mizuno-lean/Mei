/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary

/-!
# Cancellation of internal boundary facets

Two cells with the same conormal orientation induce opposite boundary
orientations on a common facet exposed by opposite functionals. In particular,
the internal facet introduced by a hyperplane cut cancels from the sum of the
two signed boundaries. The remaining terms are precisely the other signed
facets of the two pieces. This is the internal-face cancellation needed for
compatibility of the polyhedral coboundary with subdivision.

The geometric matching is supplied by `OrientedCell.exists_boundaryFacet_cut_reverse`;
coefficient cancellation uses `PolyhedralCochain.mk_reverse`.
It applies in arbitrary codimension, with real offsets, unbounded cells and
lineality. It proves cancellation of the internal facet; identifying the
remaining facets with a subdivision of the original boundary is a further step.
-/

public section

noncomputable section

open Module Set

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

open Classical in
/-- A pair of oppositely oriented boundary facets cancels from the two complete
signed facet sums, leaving every other occurrence unchanged. -/
theorem cellCoboundary_add_eq_sum_erase (σ τ : OrientedCell h k)
    {υ : OrientedCell h (k + 1)} (hυ : υ ∈ σ.boundaryFacets)
    (hυr : υ.reverse ∈ τ.boundaryFacets)
    {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] (c : E) :
    σ.cellCoboundary (R := R) c + τ.cellCoboundary c =
      (∑ ξ ∈ σ.boundaryFacets.erase υ, PolyhedralCochain.mk ξ c) +
        ∑ ξ ∈ τ.boundaryFacets.erase υ.reverse, PolyhedralCochain.mk ξ c := by
  classical
  rw [cellCoboundary_apply, cellCoboundary_apply,
    ← Finset.add_sum_erase _ (fun ξ => PolyhedralCochain.mk ξ c) hυ,
    ← Finset.add_sum_erase _ (fun ξ => PolyhedralCochain.mk ξ c) hυr,
    PolyhedralCochain.mk_reverse]
  abel

open Classical in
/-- In a hyperplane cut into equally oriented cells of the original codimension,
the internal facet cancels from the sum of their signed boundaries, leaving
precisely the other facets of the two pieces. -/
theorem exists_cellCoboundary_cut_add_eq (σ σ₁ σ₂ : OrientedCell h k)
    (l : V →L[ℝ] ℝ) (a : ℝ)
    (hminus : σ₁.carrier = σ.carrier ∩ {x | l x ≤ a})
    (hplus : σ₂.carrier = σ.carrier ∩ {x | a ≤ l x})
    (ho : σ₁.orientation = σ₂.orientation)
    (hne : (σ.carrier ∩ {x | l x = a}).Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (σ.carrier ∩ {x | l x = a})) + 1 =
      finrank ℝ (vectorSpan ℝ σ.carrier))
    {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] (c : E) :
    ∃ υ ∈ σ₁.boundaryFacets, υ.carrier = σ.carrier ∩ {x | l x = a} ∧
      υ.reverse ∈ σ₂.boundaryFacets ∧
      σ₁.cellCoboundary (R := R) c + σ₂.cellCoboundary c =
        (∑ τ ∈ σ₁.boundaryFacets.erase υ, PolyhedralCochain.mk τ c) +
        ∑ τ ∈ σ₂.boundaryFacets.erase υ.reverse, PolyhedralCochain.mk τ c := by
  classical
  obtain ⟨υ, hυ, hcarrier, hυr⟩ := σ.exists_boundaryFacet_cut_reverse σ₁ σ₂ l a
    hminus hplus ho hne hdim
  exact ⟨υ, hυ, hcarrier, hυr, σ₁.cellCoboundary_add_eq_sum_erase σ₂ hυ hυr c⟩

end Mei.OrientedCell
