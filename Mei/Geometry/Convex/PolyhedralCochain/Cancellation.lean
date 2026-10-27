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

The argument uses `IsExposed.facetOrientation_eq_neg_wedgeCovector` to compute
the boundary orientation from the actual cutting functional, and
`OrientedCell.boundaryFacet_orientation` to identify the signed cells.
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

/-- Equally oriented cells with the same tangent direction induce opposite
signed orientations on a facet exposed by opposite functionals. -/
theorem boundaryFacet_eq_reverse_of_toExposed (σ τ : OrientedCell h k)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hG : IsExposed ℝ τ.carrier F)
    (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hd : vectorSpan ℝ σ.carrier = vectorSpan ℝ τ.carrier)
    (ho : σ.orientation = τ.orientation)
    (l : V →L[ℝ] ℝ) (hl : F = l.toExposed σ.carrier)
    (hm : F = (-l).toExposed τ.carrier) :
    σ.boundaryFacet hF hne hdim =
      (τ.boundaryFacet hG hne (by rw [← hd]; exact hdim)).reverse := by
  have := h.finiteDimensional
  have hlW : ∃ n ∈ vectorSpan ℝ σ.carrier, l n ≠ 0 := by
    by_contra hn
    apply l.comp_vectorSpan_ne_zero (hl ▸ hne) (by
      rw [← hl]
      intro he
      rw [he] at hdim
      omega)
    ext v
    simpa only [ContinuousLinearMap.coe_coe, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.zero_apply] using
      not_not.mp (fun hv => hn ⟨v, v.property, hv⟩)
  have hmW : ∃ n ∈ vectorSpan ℝ τ.carrier, (-l) n ≠ 0 := by
    simpa only [← hd, neg_apply, neg_ne_zero] using hlW
  have hk := (σ.boundaryFacet hF hne hdim).finrank_quotient_direction
  rw [boundaryFacet_carrier, direction_affineSpan] at hk
  apply OrientedCell.ext (by simp only [boundaryFacet_carrier, reverse_carrier])
  rw [reverse_orientation, σ.boundaryFacet_orientation, τ.boundaryFacet_orientation,
    hF.facetOrientation_eq_neg_wedgeCovector hne hdim σ.orientation
      (by simpa only [direction_affineSpan] using σ.isConormal) hk l hl hlW,
    hG.facetOrientation_eq_neg_wedgeCovector hne (by rw [← hd]; exact hdim) τ.orientation
      (by simpa only [direction_affineSpan] using τ.isConormal) hk (-l) hm hmW]
  simp only [← ho, ← hd, ContinuousLinearMap.toLinearMap_neg]
  rw [Module.Ray.wedgeCovector_neg_right, neg_neg]

/-- The common slice of a hyperplane cut occurs in both signed facet families,
with opposite orientations, when the two pieces have the same orientation. -/
theorem exists_boundaryFacet_cut_reverse (σ σ₁ σ₂ : OrientedCell h k)
    (l : V →L[ℝ] ℝ) (a : ℝ)
    (hminus : σ₁.carrier = σ.carrier ∩ {x | l x ≤ a})
    (hplus : σ₂.carrier = σ.carrier ∩ {x | a ≤ l x})
    (ho : σ₁.orientation = σ₂.orientation)
    (hne : (σ.carrier ∩ {x | l x = a}).Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (σ.carrier ∩ {x | l x = a})) + 1 =
      finrank ℝ (vectorSpan ℝ σ.carrier)) :
    ∃ υ ∈ σ₁.boundaryFacets, υ.carrier = σ.carrier ∩ {x | l x = a} ∧
      υ.reverse ∈ σ₂.boundaryFacets := by
  have := h.finiteDimensional
  have hdminus : vectorSpan ℝ σ₁.carrier = vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using
      σ₁.direction_eq_of_subset σ (by rw [hminus]; exact inter_subset_left)
  have hdplus : vectorSpan ℝ σ₂.carrier = vectorSpan ℝ σ.carrier := by
    simpa only [direction_affineSpan] using
      σ₂.direction_eq_of_subset σ (by rw [hplus]; exact inter_subset_left)
  let F := σ.carrier ∩ {x | l x = a}
  have hl : F = l.toExposed σ₁.carrier := by
    rw [hminus, l.toExposed_inter_le σ.carrier a hne]
  have hm : F = (-l).toExposed σ₂.carrier := by
    have hne' : (σ.carrier ∩ {x | (-l) x = -a}).Nonempty := by
      simpa only [neg_apply, neg_inj] using hne
    have he := (-l).toExposed_inter_le σ.carrier (-a) hne'
    simpa only [neg_apply, neg_le_neg_iff, neg_inj, ← hplus] using he.symm
  have hF : IsExposed ℝ σ₁.carrier F := by
    rw [hl]
    exact ContinuousLinearMap.toExposed.isExposed
  have hG : IsExposed ℝ σ₂.carrier F := by
    rw [hm]
    exact ContinuousLinearMap.toExposed.isExposed
  have hdm : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ₁.carrier) := by
    rw [hdminus]
    exact hdim
  have hdp : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ₂.carrier) := by
    rw [hdplus]
    exact hdim
  let υ := σ₁.boundaryFacet hF hne hdm
  have hυ : υ ∈ σ₁.boundaryFacets := σ₁.boundaryFacet_mem_boundaryFacets hF hne hdm
  have he : σ₂.boundaryFacet hG hne hdp = υ.reverse := by
    have hr := σ₁.boundaryFacet_eq_reverse_of_toExposed σ₂ hF hG hne hdm
      (hdminus.trans hdplus.symm) ho l hl hm
    simpa only [reverse_reverse] using congrArg reverse hr.symm
  have hυr : υ.reverse ∈ σ₂.boundaryFacets := by
    rw [← he]
    exact σ₂.boundaryFacet_mem_boundaryFacets hG hne hdp
  exact ⟨υ, hυ, by simp only [υ, boundaryFacet_carrier, F], hυr⟩

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
  refine ⟨υ, hυ, hcarrier, hυr, ?_⟩
  rw [cellCoboundary_apply, cellCoboundary_apply,
    ← Finset.add_sum_erase _ (fun τ => PolyhedralCochain.mk τ c) hυ,
    ← Finset.add_sum_erase _ (fun τ => PolyhedralCochain.mk τ c) hυr,
    PolyhedralCochain.mk_reverse]
  abel

end Mei.OrientedCell
