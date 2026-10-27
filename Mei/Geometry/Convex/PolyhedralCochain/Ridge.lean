/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Facet
public import Mei.Analysis.Convex.Exposed.Ridge

/-!
# Cancellation at a common boundary ridge

A common ridge of two signed boundary facets inherits opposite orientations
through the two facets. Consequently, a ridge generator in one facet boundary
occurs reversed in the other boundary and their cochain contributions cancel.
This supplies the orientation comparison for the square of the coboundary;
counting the facets incident to each ridge remains a separate step.

The comparison uses `IsExposed.facetOrientation_inter_eq_neg`, the canonical
`OrientedCell.boundaryFacet`, and the orientation reversal relation
`PolyhedralCochain.mk_reverse`. Arbitrary codimension, unbounded cells and
lineality are allowed.
-/

public section

noncomputable section

open Module Set

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- Taking the signed boundary orientation along two intersecting facets in
opposite orders reverses the resulting oriented ridge. -/
theorem boundaryFacet_boundaryFacet_inter_eq_reverse (σ : OrientedCell h k)
    {F G : Set V} (hF : IsExposed ℝ σ.carrier F) (hG : IsExposed ℝ σ.carrier G)
    (hne : (F ∩ G).Nonempty)
    (hFdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hGdim : finrank ℝ (vectorSpan ℝ G) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hRdim : finrank ℝ (vectorSpan ℝ (F ∩ G)) + 1 = finrank ℝ (vectorSpan ℝ F)) :
    let τ := σ.boundaryFacet hF (hne.mono inter_subset_left) hFdim
    let υ := σ.boundaryFacet hG (hne.mono inter_subset_right) hGdim
    let hRF := (hF.inter hG).mono hF.subset inter_subset_left
    let hRG := (hF.inter hG).mono hG.subset inter_subset_right
    τ.boundaryFacet (by simpa only [τ, boundaryFacet_carrier] using hRF) hne
      (by dsimp only [τ]; rw [boundaryFacet_carrier]; exact hRdim) =
      (υ.boundaryFacet (by simpa only [υ, boundaryFacet_carrier] using hRG) hne
      (by dsimp only [υ]; rw [boundaryFacet_carrier]; omega)).reverse := by
  have := h.finiteDimensional
  dsimp only
  apply OrientedCell.ext (by simp only [boundaryFacet_carrier, reverse_carrier])
  simp only [boundaryFacet_orientation, reverse_orientation]
  simp_rw [boundaryFacet_carrier]
  exact hF.facetOrientation_inter_eq_neg hG hne hFdim hGdim hRdim σ.orientation
    (by simpa only [direction_affineSpan] using σ.isConormal)
    (by
      have hk := σ.finrank_quotient_direction
      rw [direction_affineSpan] at hk
      exact hk)

/-- If a signed facet of a boundary facet is the intersection with another
boundary facet, its reversal belongs to that other facet's signed boundary.
The codimension conditions are supplied by the actual signed facet memberships. -/
theorem reverse_mem_boundaryFacets_of_carrier_eq_inter (σ : OrientedCell h k)
    {τ υ : OrientedCell h (k + 1)} (hτ : τ ∈ σ.boundaryFacets)
    (hυ : υ ∈ σ.boundaryFacets) {r : OrientedCell h (k + 1 + 1)}
    (hr : r ∈ τ.boundaryFacets) (hcarrier : r.carrier = τ.carrier ∩ υ.carrier) :
    r.reverse ∈ υ.boundaryFacets := by
  have := h.finiteDimensional
  obtain ⟨F, hF, hFn, hFd, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
  obtain ⟨G, hG, hGn, hGd, rfl⟩ := (σ.mem_boundaryFacets υ).mp hυ
  obtain ⟨Q, hQ, hQn, hQd, rfl⟩ := mem_boundaryFacets _ _ |>.mp hr
  simp only [boundaryFacet_carrier] at hcarrier
  rw [boundaryFacet_carrier] at hQd
  subst Q
  have hne : (F ∩ G).Nonempty := hQn
  have he := σ.boundaryFacet_boundaryFacet_inter_eq_reverse hF hG hne hFd hGd hQd
  have hRG := (hF.inter hG).mono hG.subset inter_subset_right
  -- Exposure and dimension certificates are propositions; the canonical facet
  -- depends only on its parent and support, so either certificate gives this cell.
  have he' : ((σ.boundaryFacet hF hFn hFd).boundaryFacet hQ hQn
      (by rw [boundaryFacet_carrier]; exact hQd)).reverse =
      (σ.boundaryFacet hG hGn hGd).boundaryFacet
        (by simpa only [boundaryFacet_carrier] using hRG) hne (by
        rw [boundaryFacet_carrier]
        omega) := by
    exact (congrArg reverse he).trans (reverse_reverse _)
  rw [he']
  exact boundaryFacet_mem_boundaryFacets _ _ _ _

end Mei.OrientedCell
