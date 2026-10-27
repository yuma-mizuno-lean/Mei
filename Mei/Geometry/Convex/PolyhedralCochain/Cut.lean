/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Facet
public import Mei.Analysis.Convex.Halfspace

/-!
# External facets under a hyperplane cut

Restricting an oriented cell to a piece of the same dimension preserves the
boundary orientation on every surviving facet piece. In particular, when a
hyperplane splits an external facet into two full-dimensional pieces, the
signed facets of the two cut cells form an oriented subdivision of the original
facet. Their classes therefore add to its class in polyhedral cochains.

This supplies the external-facet comparison in the compatibility of signed
facet sums with cuts. It uses `OrientedCell.eq_boundaryFacet_iff`, the outward
contraction characterization of boundary orientations, and the subdivision
relation `PolyhedralCochain.mk_eq_sum_of_isOrientedSubdivision`. Unbounded cells,
lineality and arbitrary real offsets are allowed.
-/

public section

noncomputable section

open Module Set

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- A facet meeting the strict side of a halfspace cut survives as a facet of
the cut cell, with its inherited boundary orientation. -/
theorem exists_boundaryFacet_inter_le (σ π : OrientedCell h k)
    (g : V →ᵃ[ℝ] ℝ) (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F) (hFne : F.Nonempty)
    (hFd : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hstrict : ∃ x ∈ F, g x < 0) :
    ∃ τ ∈ π.boundaryFacets, τ.carrier = F ∩ {x | g x ≤ 0} ∧
      τ.orientation = (σ.boundaryFacet hF hFne hFd).orientation := by
  have := h.finiteDimensional
  have hconv : Convex ℝ F := by
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    exact hF.convex (hP ▸ P.convex)
  have hface : IsExposed ℝ π.carrier (F ∩ {x | g x ≤ 0}) := by
    rw [hπ]
    exact hF.inter_inter (IsExposed.refl _)
  have hne : (F ∩ {x | g x ≤ 0}).Nonempty := by
    obtain ⟨x, hx, hgx⟩ := hstrict
    exact ⟨x, hx, hgx.le⟩
  have hspan := congrArg AffineSubspace.direction (g.affineSpan_inter_le_eq hconv hstrict)
  rw [direction_affineSpan, direction_affineSpan] at hspan
  have hd : finrank ℝ (vectorSpan ℝ (F ∩ {x | g x ≤ 0})) + 1 =
      finrank ℝ (vectorSpan ℝ π.carrier) := by
    have hσk := σ.finrank_direction_add
    have hπk := π.finrank_direction_add
    rw [direction_affineSpan] at hσk hπk
    rw [hspan]
    omega
  refine ⟨π.boundaryFacet hface hne hd, π.boundaryFacet_mem_boundaryFacets _ _ _,
    boundaryFacet_carrier _ _ _ _, ?_⟩
  exact σ.boundaryFacet_orientation_eq_of_subset π
    (hπ ▸ inter_subset_left) ho hF hface hFne hne hFd hd inter_subset_left

open Classical in
/-- If a hyperplane crosses an external facet on both strict sides, its two
pieces are actual signed facets of the cut cells and subdivide the original
signed facet. The strict-side witnesses supply the dimension of both pieces. -/
theorem exists_boundaryFacet_cut_subdivision (σ π μ : OrientedCell h k)
    (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (hμ : μ.carrier = σ.carrier ∩ {x | 0 ≤ g x})
    (hoπ : π.orientation = σ.orientation) (hoμ : μ.orientation = σ.orientation)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hFne : F.Nonempty)
    (hFd : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (hneg : ∃ x ∈ F, g x < 0) (hpos : ∃ x ∈ F, 0 < g x) :
    ∃ τ ∈ π.boundaryFacets, ∃ υ ∈ μ.boundaryFacets,
      τ.carrier = F ∩ {x | g x ≤ 0} ∧ υ.carrier = F ∩ {x | 0 ≤ g x} ∧
      τ ≠ υ ∧
      IsOrientedSubdivision (σ.boundaryFacet hF hFne hFd) {τ, υ} := by
  classical
  obtain ⟨τ, hτ, hcτ, hoτ⟩ := σ.exists_boundaryFacet_inter_le π g hπ hoπ hF hFne hFd hneg
  have hμ' : μ.carrier = σ.carrier ∩ {x | (-g) x ≤ 0} := by simpa using hμ
  have hpos' : ∃ x ∈ F, (-g) x < 0 := by simpa using hpos
  obtain ⟨υ, hυ, hcυ, hoυ⟩ :=
    σ.exists_boundaryFacet_inter_le μ (-g) hμ' hoμ hF hFne hFd hpos'
  have hcυ' : υ.carrier = F ∩ {x | 0 ≤ g x} := by simpa using hcυ
  have hdis : Disjoint (intrinsicInterior ℝ τ.carrier) (intrinsicInterior ℝ υ.carrier) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hstrict : ∃ y ∈ τ.carrier, g y < 0 := by
      obtain ⟨y, hy, hgy⟩ := hneg
      exact ⟨y, hcτ ▸ ⟨hy, hgy.le⟩, hgy⟩
    have hlt := g.lt_zero_of_mem_intrinsicInterior
      (fun y hy => (hcτ ▸ hy).2) hstrict hx
    exact (not_le_of_gt hlt) ((hcυ' ▸ intrinsicInterior_subset hy).2)
  have hne : τ ≠ υ := by
    intro he
    obtain ⟨x, hx, hgx⟩ := hneg
    have hxτ : x ∈ τ.carrier := hcτ ▸ ⟨hx, hgx.le⟩
    exact (not_le_of_gt hgx) ((hcυ' ▸ he ▸ hxτ).2)
  refine ⟨τ, hτ, υ, hυ, hcτ, hcυ', hne, ?_, ?_, ?_⟩
  · ext x
    simp only [Finset.set_biUnion_insert, Finset.set_biUnion_singleton,
      boundaryFacet_carrier, hcτ, hcυ', mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      rcases le_total (g x) 0 with hg | hg
      · exact Or.inl ⟨hx, hg⟩
      · exact Or.inr ⟨hx, hg⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hab rfl).elim
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hoτ
    · exact Finset.mem_singleton.mp ha ▸ hoυ

end Mei.OrientedCell
