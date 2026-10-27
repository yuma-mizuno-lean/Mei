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
Each nonempty codimension-two face lies in at most two boundary facets.
In particular, a ridge of one boundary facet has at most one other incident
facet, and its induced orientation there is reversed. This supplies the
uniqueness and sign of the partner needed to cancel iterated boundary terms;
existence of that partner remains a separate geometric step.

The comparison uses `IsExposed.facetOrientation_inter_eq_neg`, the canonical
`OrientedCell.boundaryFacet`, and the orientation reversal relation
`PolyhedralCochain.mk_reverse`. The incidence bound uses
`IsExposed.inter_eq_of_common_facet` and the fact that an orientation is distinct
from its negative (`Module.Ray.ne_neg_self`). Arbitrary codimension, unbounded
cells and lineality are allowed.
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

/-- If a ridge of one signed boundary facet is contained in a distinct boundary
facet, it occurs there with the opposite orientation. No intersection equality
or orientation agreement is assumed. -/
theorem reverse_mem_boundaryFacets_of_subset (σ : OrientedCell h k)
    {τ υ : OrientedCell h (k + 1)} (hτ : τ ∈ σ.boundaryFacets)
    (hυ : υ ∈ σ.boundaryFacets) (hne : τ ≠ υ)
    {r : OrientedCell h (k + 1 + 1)} (hr : r ∈ τ.boundaryFacets)
    (hsub : r.carrier ⊆ υ.carrier) : r.reverse ∈ υ.boundaryFacets := by
  have := h.finiteDimensional
  obtain ⟨F, hF, hFn, hFd, hτF⟩ := (σ.mem_boundaryFacets τ).mp hτ
  obtain ⟨G, hG, hGn, hGd, hυG⟩ := (σ.mem_boundaryFacets υ).mp hυ
  obtain ⟨Q, hQ, hQn, hQd, hrQ⟩ := (τ.mem_boundaryFacets r).mp hr
  have hcτ : τ.carrier = F := by rw [hτF, boundaryFacet_carrier]
  have hcυ : υ.carrier = G := by rw [hυG, boundaryFacet_carrier]
  have hcr : r.carrier = Q := by rw [hrQ, boundaryFacet_carrier]
  have hFG : F ≠ G := by
    intro he
    apply hne
    exact σ.carrier_injOn_boundaryFacets hτ hυ (hcτ.trans (he.trans hcυ.symm))
  have hQF : IsExposed ℝ F Q := by rwa [hcτ] at hQ
  have he := hF.inter_eq_of_common_facet hG hQF hQn
    (by rwa [hcr, hcυ] at hsub) hFG (by omega) (by rwa [hcτ] at hQd)
  exact σ.reverse_mem_boundaryFacets_of_carrier_eq_inter hτ hυ hr
    (by rw [hcr, hcτ, hcυ, he])

/-- A ridge of a signed boundary facet has at most one other incident boundary
facet. -/
theorem eq_of_ridge_subset_of_ne (σ : OrientedCell h k)
    {τ υ η : OrientedCell h (k + 1)} (hτ : τ ∈ σ.boundaryFacets)
    (hυ : υ ∈ σ.boundaryFacets) (hη : η ∈ σ.boundaryFacets)
    (hτυ : τ ≠ υ) (hτη : τ ≠ η)
    {r : OrientedCell h (k + 1 + 1)} (hr : r ∈ τ.boundaryFacets)
    (hrυ : r.carrier ⊆ υ.carrier) (hrη : r.carrier ⊆ η.carrier) : υ = η := by
  by_contra hυη
  have hrevυ := σ.reverse_mem_boundaryFacets_of_subset hτ hυ hτυ hr hrυ
  have hrevη := σ.reverse_mem_boundaryFacets_of_subset hτ hη hτη hr hrη
  have hrr := σ.reverse_mem_boundaryFacets_of_subset hυ hη hυη hrevυ
    (by simpa only [reverse_carrier] using hrη)
  rw [reverse_reverse] at hrr
  exact r.reverse_ne_self (η.carrier_injOn_boundaryFacets hrevη hrr (reverse_carrier r))

open Classical in
/-- Every nonempty exposed face of relative codimension two is contained in at
most two signed boundary facets. This includes unbounded faces and lineality;
it does not assert existence of either incident facet. -/
theorem card_boundaryFacets_containing_le_two (σ : OrientedCell h k) {Q : Set V}
    (hQ : IsExposed ℝ σ.carrier Q) (hne : Q.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ Q) + 2 =
      finrank ℝ (vectorSpan ℝ σ.carrier)) :
    (σ.boundaryFacets.filter (fun τ => Q ⊆ τ.carrier)).card ≤ 2 := by
  classical
  have := h.finiteDimensional
  by_contra! hcard
  obtain ⟨τ, hτ, υ, hυ, η, hη, hτυ, hτη, hυη⟩ := Finset.two_lt_card.mp hcard
  obtain ⟨hτ, hQτ⟩ := Finset.mem_filter.mp hτ
  obtain ⟨hυ, hQυ⟩ := Finset.mem_filter.mp hυ
  obtain ⟨hη, hQη⟩ := Finset.mem_filter.mp hη
  have hsub := σ.carrier_subset_of_mem_boundaryFacets hτ
  have he : IsExposed ℝ τ.carrier Q := hQ.mono hsub hQτ
  have hd : finrank ℝ (vectorSpan ℝ Q) + 1 =
      finrank ℝ (vectorSpan ℝ τ.carrier) := by
    have hσdim := σ.finrank_direction_add
    have hτdim := τ.finrank_direction_add
    rw [direction_affineSpan] at hσdim hτdim
    omega
  let r := τ.boundaryFacet he hne hd
  have hr : r ∈ τ.boundaryFacets := τ.boundaryFacet_mem_boundaryFacets he hne hd
  exact hυη (σ.eq_of_ridge_subset_of_ne hτ hυ hη hτυ hτη hr
    (by simpa only [r, boundaryFacet_carrier] using hQυ)
    (by simpa only [r, boundaryFacet_carrier] using hQη))

end Mei.OrientedCell
