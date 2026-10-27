/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Cut.Basic
public import Mei.Geometry.Convex.PolyhedralCochain.Cancellation

/-!
# Signed boundaries of hyperplane cuts

The signed boundary of a cell is the sum of the signed boundaries of its two
equally oriented halfspace pieces. The common cutting facet cancels, while each
original facet is either retained on one side or subdivided between the two sides.
The equality holds in polyhedral cochains, so subdivisions of the external facets
are already identified. It allows arbitrary codimension, unbounded cells,
lineality and real offsets.

The proof assembles `OrientedCell.carrier_eq_cut_zero_or_inter_boundaryFacet`,
`OrientedCell.exists_boundaryFacet_inter_le`,
`OrientedCell.exists_boundaryFacet_cut_subdivision` and
`OrientedCell.cellCoboundary_add_eq_sum_erase`. In particular, every facet of each
piece is counted, including facets that the cutting hyperplane only touches.
-/

public section

noncomputable section

open Module Set

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

private def cutFacet (σ π : OrientedCell h k) (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) (η : OrientedCell h (k + 1))
    (hη : η ∈ σ.boundaryFacets) (hn : ∃ x ∈ η.carrier, g x < 0) :
    OrientedCell h (k + 1) :=
  Classical.choose (p := fun τ : OrientedCell h (k + 1) =>
    τ ∈ π.boundaryFacets ∧ τ.carrier = η.carrier ∩ {x | g x ≤ 0} ∧
      τ.orientation = η.orientation) (by
    obtain ⟨F, hF, hne, hd, rfl⟩ := (σ.mem_boundaryFacets η).mp hη
    simpa only [boundaryFacet_carrier] using
      σ.exists_boundaryFacet_inter_le π g hπ ho hF hne hd
        (by simpa only [boundaryFacet_carrier] using hn))

private theorem cutFacet_spec (σ π : OrientedCell h k) (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) (η : OrientedCell h (k + 1))
    (hη : η ∈ σ.boundaryFacets) (hn : ∃ x ∈ η.carrier, g x < 0) :
    cutFacet σ π g hπ ho η hη hn ∈ π.boundaryFacets ∧
      (cutFacet σ π g hπ ho η hη hn).carrier = η.carrier ∩ {x | g x ≤ 0} ∧
      (cutFacet σ π g hπ ho η hη hn).orientation = η.orientation := by
  unfold cutFacet
  exact Classical.choose_spec (p := fun τ : OrientedCell h (k + 1) =>
    τ ∈ π.boundaryFacets ∧ τ.carrier = η.carrier ∩ {x | g x ≤ 0} ∧
      τ.orientation = η.orientation) _

private theorem cutFacet_injective (σ π : OrientedCell h k) (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) (η ξ : OrientedCell h (k + 1))
    (hη : η ∈ σ.boundaryFacets) (hξ : ξ ∈ σ.boundaryFacets)
    (hnη : ∃ x ∈ η.carrier, g x < 0) (hnξ : ∃ x ∈ ξ.carrier, g x < 0)
    (he : cutFacet σ π g hπ ho η hη hnη = cutFacet σ π g hπ ho ξ hξ hnξ) : η = ξ := by
  have := h.finiteDimensional
  have hc := congrArg carrier he
  rw [(cutFacet_spec σ π g hπ ho η hη hnη).2.1,
    (cutFacet_spec σ π g hπ ho ξ hξ hnξ).2.1] at hc
  obtain ⟨F, hF, hFne, hFd, rfl⟩ := (σ.mem_boundaryFacets η).mp hη
  obtain ⟨G, hG, hGne, hGd, rfl⟩ := (σ.mem_boundaryFacets ξ).mp hξ
  simp only [boundaryFacet_carrier] at hc hnη hnξ
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  have hspan := congrArg AffineSubspace.direction
    (g.affineSpan_inter_le_eq (hF.convex (hP ▸ P.convex)) hnη)
  simp only [direction_affineSpan] at hspan
  have hsub : F ∩ {x | g x ≤ 0} ⊆ F ∩ G := by
    intro x hx
    exact ⟨hx.1, (hc ▸ hx).1⟩
  have hlo := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  rw [hspan] at hlo
  have hhi := Submodule.finrank_mono
    (vectorSpan_mono ℝ (inter_subset_left : F ∩ G ⊆ F))
  have hne : (F ∩ G).Nonempty := by
    obtain ⟨x, hx, hnx⟩ := hnη
    exact ⟨x, hsub ⟨hx, hnx.le⟩⟩
  have heF := (hF.inter hG).mono hF.subset inter_subset_left
  have heF := heF.eq_of_finrank_vectorSpan_eq hne
    (by omega)
  have heG := (hF.inter hG).mono hG.subset inter_subset_right
  have heG := heG.eq_of_finrank_vectorSpan_eq hne
    (by omega)
  have heFG := heF.symm.trans heG
  subst G
  rfl

private theorem exists_neg_of_ne_cutFacet (σ π : OrientedCell h k)
    (g : V →ᵃ[ℝ] ℝ) (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    {υ ζ : OrientedCell h (k + 1)} (hυ : υ ∈ π.boundaryFacets)
    (hcυ : υ.carrier = σ.carrier ∩ {x | g x = 0})
    (hζ : ζ ∈ π.boundaryFacets) (hne : ζ ≠ υ) :
    ∃ x ∈ ζ.carrier, g x < 0 := by
  classical
  have := h.finiteDimensional
  by_contra! hn
  have hsub : ζ.carrier ⊆ υ.carrier := by
    intro x hx
    have hxπ := π.carrier_subset_of_mem_boundaryFacets hζ hx
    rw [hπ] at hxπ
    exact hcυ ▸ ⟨hxπ.1, le_antisymm hxπ.2 (hn x hx)⟩
  obtain ⟨F, hF, hFne, hFd, heF⟩ := (π.mem_boundaryFacets ζ).mp hζ
  obtain ⟨G, hG, hGne, hGd, heG⟩ := (π.mem_boundaryFacets υ).mp hυ
  have hFG : F ⊆ G := by simpa only [heF, heG, boundaryFacet_carrier] using hsub
  have he := (hF.mono hG.subset hFG).eq_of_finrank_vectorSpan_eq hFne (by omega)
  exact hne (π.carrier_injOn_boundaryFacets hζ hυ
    (by simpa only [heF, heG, boundaryFacet_carrier] using he))

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

open Classical in
private def cutContribution (σ π : OrientedCell h k) (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) (η : OrientedCell h (k + 1))
    (hη : η ∈ σ.boundaryFacets) (c : E) : PolyhedralCochain R h E (k + 1) :=
  if hn : ∃ x ∈ η.carrier, g x < 0 then
    PolyhedralCochain.mk (cutFacet σ π g hπ ho η hη hn) c else 0

open Classical in
private theorem sum_cutContribution (σ π : OrientedCell h k) (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) {υ : OrientedCell h (k + 1)}
    (hυ : υ ∈ π.boundaryFacets) (hcυ : υ.carrier = σ.carrier ∩ {x | g x = 0}) (c : E) :
    (∑ η : σ.boundaryFacets, cutContribution (R := R) σ π g hπ ho η.val η.property c) =
      ∑ ζ ∈ π.boundaryFacets.erase υ, PolyhedralCochain.mk (R := R) ζ c := by
  classical
  have := h.finiteDimensional
  let S := Finset.univ.filter fun η : σ.boundaryFacets => ∃ x ∈ η.val.carrier, g x < 0
  -- Discard original facets missing the strict halfspace, then reindex all
  -- remaining facets by their restrictions.
  have hsum : (∑ η : σ.boundaryFacets, cutContribution (R := R) σ π g hπ ho η.val η.property c) =
      ∑ η ∈ S, cutContribution (R := R) σ π g hπ ho η.val η.property c := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro η _ hη
    have hn : ¬ ∃ x ∈ η.val.carrier, g x < 0 := by simpa only [S, Finset.mem_filter,
      Finset.mem_univ, true_and] using hη
    simp only [cutContribution, dite_eq_right hn]
  rw [hsum]
  apply Finset.sum_bij (fun η hη => cutFacet σ π g hπ ho η.val η.property
    (Finset.mem_filter.mp hη).2)
  · intro η hη
    have hs := cutFacet_spec σ π g hπ ho η.val η.property (Finset.mem_filter.mp hη).2
    refine Finset.mem_erase.mpr ⟨?_, hs.1⟩
    intro he
    obtain ⟨x, hx, hnx⟩ := (Finset.mem_filter.mp hη).2
    have hxc : x ∈ (cutFacet σ π g hπ ho η.val η.property
        (Finset.mem_filter.mp hη).2).carrier := hs.2.1 ▸ ⟨hx, hnx.le⟩
    rw [he, hcυ] at hxc
    exact (ne_of_lt hnx) hxc.2
  · intro η hη ξ hξ he
    exact Subtype.ext (cutFacet_injective σ π g hπ ho η.val ξ.val η.property ξ.property
      (Finset.mem_filter.mp hη).2 (Finset.mem_filter.mp hξ).2 he)
  · intro ζ hζ
    obtain ⟨hne, hζπ⟩ := Finset.mem_erase.mp hζ
    obtain ⟨x, hx, hnx⟩ := exists_neg_of_ne_cutFacet σ π g hπ hυ hcυ hζπ hne
    rcases σ.carrier_eq_cut_zero_or_inter_boundaryFacet π
      { g with cont := g.continuous_of_finiteDimensional } hπ hζπ with hc | ⟨η, hη, hc⟩
    · exact (hne (π.carrier_injOn_boundaryFacets hζπ hυ (hc.trans hcυ.symm))).elim
    · have hnη : ∃ x ∈ η.carrier, g x < 0 := ⟨x, (hc ▸ hx).1, hnx⟩
      refine ⟨⟨η, hη⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnη⟩, ?_⟩
      exact π.carrier_injOn_boundaryFacets (cutFacet_spec σ π g hπ ho η hη hnη).1 hζπ
        ((cutFacet_spec σ π g hπ ho η hη hnη).2.1.trans hc.symm)
  · intro η hη
    simp only [cutContribution, dite_eq_left (Finset.mem_filter.mp hη).2]

private theorem facet_not_contained_in_cut (σ π μ : OrientedCell h k)
    (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (hμ : μ.carrier = σ.carrier ∩ {x | 0 ≤ g x})
    (hoπ : π.orientation = σ.orientation) (hoμ : μ.orientation = σ.orientation)
    {υ : OrientedCell h (k + 1)} (hυ : υ ∈ π.boundaryFacets)
    (hcυ : υ.carrier = σ.carrier ∩ {x | g x = 0})
    (hυr : υ.reverse ∈ μ.boundaryFacets) {η : OrientedCell h (k + 1)}
    (hη : η ∈ σ.boundaryFacets) : ¬ (∀ x ∈ η.carrier, g x = 0) := by
  classical
  have := h.finiteDimensional
  intro hz
  -- A coarse facet contained in the cutting section would inherit the same
  -- orientation from both pieces, contradicting the opposite internal signs.
  have hmem (q : OrientedCell h k) (f : V →ᵃ[ℝ] ℝ)
      (hq : q.carrier = σ.carrier ∩ {x | f x ≤ 0})
      (hoq : q.orientation = σ.orientation) (hf : ∀ x ∈ η.carrier, f x = 0) :
      η ∈ q.boundaryFacets := by
    obtain ⟨F, hF, hFne, hFd, he⟩ := (σ.mem_boundaryFacets η).mp hη
    have hsub : q.carrier ⊆ σ.carrier := hq ▸ inter_subset_left
    have hFq : F ⊆ q.carrier := by
      intro x hx
      rw [hq]
      exact ⟨hF.subset hx, (hf x (by simpa only [he, boundaryFacet_carrier] using hx)).le⟩
    have hface := hF.mono hsub hFq
    have hdim : finrank ℝ (vectorSpan ℝ F) + 1 =
        finrank ℝ (vectorSpan ℝ q.carrier) := by
      have hd := q.direction_eq_of_subset σ hsub
      rw [direction_affineSpan, direction_affineSpan] at hd
      rwa [hd]
    have hcanon : q.boundaryFacet hface hFne hdim = η := by
      apply OrientedCell.ext (by simp only [he, boundaryFacet_carrier])
      rw [he]
      exact σ.boundaryFacet_orientation_eq_of_subset q hsub hoq
        hF hFne hFd hface hFne hdim Subset.rfl
    rw [← hcanon]
    exact q.boundaryFacet_mem_boundaryFacets _ _ _
  have hηπ := hmem π g hπ hoπ hz
  have hμ' : μ.carrier = σ.carrier ∩ {x | (-g) x ≤ 0} := by simpa using hμ
  have hημ := hmem μ (-g) hμ' hoμ (by simpa using hz)
  have heπ : η = υ := by
    by_contra hne
    obtain ⟨x, hx, hnx⟩ := exists_neg_of_ne_cutFacet σ π g hπ hυ hcυ hηπ hne
    exact (ne_of_lt hnx) (hz x hx)
  have heμ : η = υ.reverse := by
    by_contra hne
    have hcr : υ.reverse.carrier = σ.carrier ∩ {x | (-g) x = 0} := by
      simpa only [reverse_carrier, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hcυ
    obtain ⟨x, hx, hnx⟩ := exists_neg_of_ne_cutFacet σ μ (-g) hμ' hυr hcr hημ hne
    simp only [AffineMap.coe_neg, Pi.neg_apply, hz x hx, neg_zero, lt_self_iff_false] at hnx
  exact υ.reverse_ne_self (heμ.symm.trans heπ)

private theorem cutContribution_eq_mk_of_forall_le (σ π : OrientedCell h k)
    (g : V →ᵃ[ℝ] ℝ) (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (ho : π.orientation = σ.orientation) (η : OrientedCell h (k + 1))
    (hη : η ∈ σ.boundaryFacets) (hn : ∃ x ∈ η.carrier, g x < 0)
    (hle : ∀ x ∈ η.carrier, g x ≤ 0) (c : E) :
    cutContribution (R := R) σ π g hπ ho η hη c = PolyhedralCochain.mk (R := R) η c := by
  have hs := cutFacet_spec σ π g hπ ho η hη hn
  have he : cutFacet σ π g hπ ho η hη hn = η :=
    OrientedCell.ext (hs.2.1.trans (inter_eq_self_of_subset_left hle)) hs.2.2
  simp only [cutContribution, dite_eq_left hn, he]

private theorem cutContribution_add (σ π μ : OrientedCell h k) (g : V →ᵃ[ℝ] ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | g x ≤ 0})
    (hμ : μ.carrier = σ.carrier ∩ {x | 0 ≤ g x})
    (hoπ : π.orientation = σ.orientation) (hoμ : μ.orientation = σ.orientation)
    {υ : OrientedCell h (k + 1)} (hυ : υ ∈ π.boundaryFacets)
    (hcυ : υ.carrier = σ.carrier ∩ {x | g x = 0})
    (hυr : υ.reverse ∈ μ.boundaryFacets) (η : OrientedCell h (k + 1))
    (hη : η ∈ σ.boundaryFacets) (c : E) :
    cutContribution (R := R) σ π g hπ hoπ η hη c +
      cutContribution (R := R) σ μ (-g) (by simpa using hμ) hoμ η hη c =
        PolyhedralCochain.mk (R := R) η c := by
  classical
  have hμ' : μ.carrier = σ.carrier ∩ {x | (-g) x ≤ 0} := by simpa using hμ
  -- A crossed facet splits into two signed pieces; a one-sided facet is retained.
  by_cases hn : ∃ x ∈ η.carrier, g x < 0
  · by_cases hp : ∃ x ∈ η.carrier, (-g) x < 0
    · obtain ⟨F, hF, hFne, hFd, heη⟩ := (σ.mem_boundaryFacets η).mp hη
      have hnF : ∃ x ∈ F, g x < 0 := by
        simpa only [heη, boundaryFacet_carrier] using hn
      have hpF : ∃ x ∈ F, 0 < g x := by
        simpa only [heη, boundaryFacet_carrier, AffineMap.coe_neg, Pi.neg_apply,
          neg_lt_zero] using hp
      obtain ⟨τ, hτ, ξ, hξ, hcτ, hcξ, hne, hsub⟩ :=
        σ.exists_boundaryFacet_cut_subdivision π μ g hπ hμ hoπ hoμ hF hFne hFd hnF hpF
      have heτ : cutFacet σ π g hπ hoπ η hη hn = τ :=
        π.carrier_injOn_boundaryFacets (cutFacet_spec σ π g hπ hoπ η hη hn).1 hτ
          (by simpa only [heη, boundaryFacet_carrier, hcτ] using
            (cutFacet_spec σ π g hπ hoπ η hη hn).2.1)
      have heξ : cutFacet σ μ (-g) hμ' hoμ η hη hp = ξ :=
        μ.carrier_injOn_boundaryFacets (cutFacet_spec σ μ (-g) hμ' hoμ η hη hp).1 hξ
          (by simpa only [heη, boundaryFacet_carrier, hcξ, AffineMap.coe_neg,
            Pi.neg_apply, neg_nonpos] using
            (cutFacet_spec σ μ (-g) hμ' hoμ η hη hp).2.1)
      simp only [cutContribution, dite_eq_left hn, dite_eq_left hp, heτ, heξ]
      rw [heη, PolyhedralCochain.mk_eq_sum_of_isOrientedSubdivision hsub]
      exact (Finset.sum_pair (f := fun τ => PolyhedralCochain.mk (R := R) τ c) hne).symm
    · rw [cutContribution_eq_mk_of_forall_le σ π g hπ hoπ η hη hn
        (by simpa only [not_exists, not_and, not_lt, AffineMap.coe_neg, Pi.neg_apply,
          neg_nonneg, neg_nonpos] using hp) c]
      simp only [cutContribution, dite_eq_right hp, add_zero]
  · have hp : ∃ x ∈ η.carrier, (-g) x < 0 := by
      by_contra! hp
      apply facet_not_contained_in_cut σ π μ g hπ hμ hoπ hoμ hυ hcυ hυr hη
      intro x hx
      have hnonneg : 0 ≤ g x := le_of_not_gt (fun hlt => hn ⟨x, hx, hlt⟩)
      have hnonpos : g x ≤ 0 := by simpa using hp x hx
      exact le_antisymm hnonpos hnonneg
    rw [cutContribution_eq_mk_of_forall_le σ μ (-g) hμ' hoμ η hη hp
      (by simpa only [not_exists, not_and, not_lt, AffineMap.coe_neg, Pi.neg_apply,
        neg_nonneg, neg_nonpos] using hn) c]
    simp only [cutContribution, dite_eq_right hn, zero_add]

/-- Cutting a cell into two pieces of the same codimension and inherited orientation
preserves its signed boundary sum. The nonempty cutting section has codimension one
inside the parent; its two induced orientations cancel. External facets are retained
or subdivided, with equality in polyhedral cochains. -/
theorem cellCoboundary_cut_add_eq (σ π μ : OrientedCell h k)
    (l : V →L[ℝ] ℝ) (a : ℝ)
    (hπ : π.carrier = σ.carrier ∩ {x | l x ≤ a})
    (hμ : μ.carrier = σ.carrier ∩ {x | a ≤ l x})
    (hoπ : π.orientation = σ.orientation) (hoμ : μ.orientation = σ.orientation)
    (hne : (σ.carrier ∩ {x | l x = a}).Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (σ.carrier ∩ {x | l x = a})) + 1 =
      finrank ℝ (vectorSpan ℝ σ.carrier)) (c : E) :
    π.cellCoboundary (R := R) c + μ.cellCoboundary c = σ.cellCoboundary c := by
  classical
  let g : V →ᵃ[ℝ] ℝ := l.toLinearMap.toAffineMap - AffineMap.const ℝ V a
  have hg (x : V) : g x = l x - a := by simp [g]
  have hπg : π.carrier = σ.carrier ∩ {x | g x ≤ 0} := by
    simpa only [hg, sub_nonpos] using hπ
  have hμg : μ.carrier = σ.carrier ∩ {x | 0 ≤ g x} := by
    simpa only [hg, sub_nonneg] using hμ
  have hμg' : μ.carrier = σ.carrier ∩ {x | (-g) x ≤ 0} := by simpa using hμg
  obtain ⟨υ, hυ, hcυ, hυr⟩ := σ.exists_boundaryFacet_cut_reverse π μ l a hπ hμ
    (hoπ.trans hoμ.symm) hne hdim
  have hcυg : υ.carrier = σ.carrier ∩ {x | g x = 0} := by
    simpa only [hg, sub_eq_zero] using hcυ
  have hcr : υ.reverse.carrier = σ.carrier ∩ {x | (-g) x = 0} := by
    simpa using hcυg
  rw [π.cellCoboundary_add_eq_sum_erase μ hυ hυr c,
    ← sum_cutContribution σ π g hπg hoπ hυ hcυg c,
    ← sum_cutContribution σ μ (-g) hμg' hoμ hυr hcr c, ← Finset.sum_add_distrib]
  calc
    _ = ∑ η : σ.boundaryFacets, PolyhedralCochain.mk (R := R) η.val c := by
      apply Finset.sum_congr rfl
      intro η _
      exact cutContribution_add σ π μ g hπg hμg hoπ hoμ hυ hcυg hυr η.val η.property c
    _ = σ.cellCoboundary c := by
      rw [cellCoboundary_apply]
      exact Finset.sum_coe_sort σ.boundaryFacets (fun η => PolyhedralCochain.mk (R := R) η c)

end Mei.OrientedCell
