/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Facet
public import Mei.Geometry.Convex.Polyhedron.Face.Facet

/-!
# Internal and external boundary subcells

The supports of the signed boundary facets cover exactly the relative frontier
of a cell. A codimension-one subcell contained in a parent is either internal,
with its relative interior in the parent's relative interior, or external,
contained in a unique signed boundary facet of the parent. This classifies
the refined boundary summands that must be matched or cancelled when comparing
facet sums under subdivision. No complex incidence hypothesis is required.

The covering uses `TauCeti.IsConvexPolyhedron.exists_facet_of_mem_intrinsicFrontier`.
Containment follows by intersecting an exposed facet with the subcell and
applying `IsExposed.eq_of_mem_intrinsicInterior`. Uniqueness uses exposed-face
dimension comparisons and `OrientedCell.carrier_injOn_boundaryFacets`.
-/

public section

open Set Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- The signed boundary facets cover precisely the relative frontier of the
cell, including all their own lower-dimensional faces. -/
theorem intrinsicFrontier_eq_biUnion_boundaryFacets (σ : OrientedCell h k) :
    intrinsicFrontier ℝ σ.carrier = ⋃ τ ∈ σ.boundaryFacets, τ.carrier := by
  have := h.finiteDimensional
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  have hpoly : TauCeti.IsConvexPolyhedron σ.carrier := hP ▸ P.isConvexPolyhedron
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨F, hF, hxF, hFd⟩ := hpoly.exists_facet_of_mem_intrinsicFrontier hx
    have hFn : F.Nonempty := ⟨x, hxF⟩
    refine Set.mem_iUnion₂.mpr ⟨σ.boundaryFacet hF hFn hFd,
      σ.boundaryFacet_mem_boundaryFacets hF hFn hFd, ?_⟩
    rw [boundaryFacet_carrier]
    exact hxF
  · intro x hx
    obtain ⟨τ, hτ, hxτ⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨F, hF, hFn, hFd, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
    rw [boundaryFacet_carrier] at hxτ
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    refine ⟨subset_intrinsicClosure (hF.subset hxτ), fun hxint => ?_⟩
    have he := hF.eq_of_mem_intrinsicInterior hxτ hxint
    rw [he] at hFd
    omega

/-- Near a relative interior point of a facet, all other signed boundary
facets of the parent are absent. The radius is independent of any transverse test. -/
theorem exists_ball_disjoint_other_boundaryFacets (σ : OrientedCell h k)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hp : p ∈ intrinsicInterior ℝ F) :
    ∃ ε > 0, ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (Metric.ball p ε) τ.carrier := by
  classical
  have := h.finiteDimensional
  let S := σ.boundaryFacets.filter (fun τ => τ.carrier ≠ F)
  have hpnot : p ∉ ⋃ τ ∈ S, τ.carrier := by
    intro hm
    obtain ⟨τ, hτ, hpτ⟩ := mem_iUnion₂.mp hm
    obtain ⟨hτ, hn⟩ := Finset.mem_filter.mp hτ
    obtain ⟨G, hG, hGn, hGd, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
    simp only [boundaryFacet_carrier] at hpτ hn
    have hinter : IsExposed ℝ F (F ∩ G) := by
      simpa only [inter_eq_left.mpr hF.subset] using (IsExposed.refl F).inter_inter hG
    have hFG : F ⊆ G := inter_eq_left.mp
      (hinter.eq_of_mem_intrinsicInterior ⟨intrinsicInterior_subset hp, hpτ⟩ hp)
    exact hn (hF.eq_of_subset_of_finrank_add_one ⟨p, intrinsicInterior_subset hp⟩ hdim
      hG hFG (by intro he; rw [he] at hGd; omega)).symm
  have hc : IsClosed (⋃ τ ∈ S, τ.carrier) :=
    S.finite_toSet.isClosed_biUnion fun τ _ => τ.isClosed_carrier
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl p hpnot
  refine ⟨ε, hε, fun τ hτ hn => disjoint_left.mpr fun z hz hzτ => ?_⟩
  exact hball hz (mem_iUnion₂.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hn⟩, hzτ⟩)

/-- A codimension-one subcell contained in a parent is internal, with all its
relative interior in the parent's relative interior, or it is contained in a
unique signed boundary facet. This applies to boundary facets of arbitrary
subdivision pieces, without requiring a chosen containing complex. -/
theorem boundary_subcell_internal_or_external (σ : OrientedCell h k)
    (τ : OrientedCell h (k + 1)) (hτσ : τ.carrier ⊆ σ.carrier) :
    intrinsicInterior ℝ τ.carrier ⊆ intrinsicInterior ℝ σ.carrier ∨
      ∃! υ : OrientedCell h (k + 1), υ ∈ σ.boundaryFacets ∧ τ.carrier ⊆ υ.carrier := by
  have := h.finiteDimensional
  by_cases hinter : intrinsicInterior ℝ τ.carrier ⊆ intrinsicInterior ℝ σ.carrier
  · exact Or.inl hinter
  right
  obtain ⟨x, hxτ, hxσ⟩ := Set.not_subset.mp hinter
  have hxfront : x ∈ intrinsicFrontier ℝ σ.carrier := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure (hτσ (intrinsicInterior_subset hxτ)), hxσ⟩
  rw [σ.intrinsicFrontier_eq_biUnion_boundaryFacets] at hxfront
  obtain ⟨υ, hυ, hxυ⟩ := Set.mem_iUnion₂.mp hxfront
  obtain ⟨F, hF, hFn, hFd, hυeq⟩ := (σ.mem_boundaryFacets υ).mp hυ
  have hυcarrier : υ.carrier = F := by rw [hυeq, boundaryFacet_carrier]
  have hτF : τ.carrier ⊆ F := by
    have he : IsExposed ℝ τ.carrier (τ.carrier ∩ F) := by
      simpa only [Set.inter_eq_left.mpr hτσ] using
        (IsExposed.refl τ.carrier).inter_inter hF
    have hwhole := he.eq_of_mem_intrinsicInterior ⟨intrinsicInterior_subset hxτ,
      hυcarrier ▸ hxυ⟩ hxτ
    exact fun y hy => (hwhole.symm ▸ hy).2
  refine ⟨υ, ⟨hυ, hυcarrier ▸ hτF⟩, ?_⟩
  rintro ω ⟨hω, hτω⟩
  obtain ⟨G, hG, hGn, hGd, hωeq⟩ := (σ.mem_boundaryFacets ω).mp hω
  have hωcarrier : ω.carrier = G := by rw [hωeq, boundaryFacet_carrier]
  rw [hωcarrier] at hτω
  have hsub : τ.carrier ⊆ F ∩ G := fun y hy => ⟨hτF hy, hτω hy⟩
  have hlow := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  have hupp := Submodule.finrank_mono (vectorSpan_mono ℝ
    (inter_subset_left : F ∩ G ⊆ F))
  have hτdim := τ.finrank_direction_add
  have hσdim := σ.finrank_direction_add
  rw [direction_affineSpan] at hτdim hσdim
  have he : F ∩ G = F :=
    ((hF.inter hG).mono hF.subset inter_subset_left).eq_of_finrank_vectorSpan_eq
      (τ.nonempty.mono fun y hy => ⟨hτF hy, hτω hy⟩) (by omega)
  have hFG : F = G := hF.eq_of_subset_of_finrank_add_one hFn hFd hG
    (he ▸ inter_subset_right) (by intro hGP; rw [hGP] at hGd; omega)
  apply σ.carrier_injOn_boundaryFacets hω hυ
  exact hωcarrier.trans (hFG.symm.trans hυcarrier.symm)

end Mei.OrientedCell
