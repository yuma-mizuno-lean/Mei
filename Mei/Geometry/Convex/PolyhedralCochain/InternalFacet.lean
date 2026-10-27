/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Incidence

/-!
# Internal facets of polyhedral subdivisions

An internal facet of a subdivision piece has exactly one other incident piece.
Its signed boundary orientation in that piece is the reverse of its original
orientation. Every facet is therefore either supported on the original cell's
relative boundary or paired with a unique opposite signed occurrence. The
paired occurrences cancel in polyhedral cochains, leaving only facets supported
on the coarse relative boundary in the total signed boundary.

The construction applies to an oriented subdivision whose pieces are cells of
one finite complex, including subdivisions of lower-dimensional cells. It uses
`FinitePolyhedralComplex.eventually_subset_of_mem_cell` to recover incidence
from a short ray across the facet, and
`FinitePolyhedralComplex.eq_reverse_of_mem_boundaryFacets` to determine its sign.
Mathlib's exposed-face maximizers and relative-interior segment theorem provide
the geometric crossing. The finite cancellation uses Mathlib's
`Finset.sum_involution` on parent-facet incidences. No boundedness or absence of
lineality is required.
-/

public section

noncomputable section

open Set Module Filter Topology

namespace Mei.OrientedCell.IsOrientedSubdivision

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {σ τ : OrientedCell h k} {Q : Finset (OrientedCell h k)}
  {C : FinitePolyhedralComplex h} {υ : OrientedCell h (k + 1)}

/-- A facet meeting the relative interior of the subdivided cell in its own
relative interior has exactly one other incident piece. Its induced signed
orientation there is the reverse of the given facet. -/
theorem existsUnique_reverse_mem_boundaryFacets
    (hQ : IsOrientedSubdivision σ Q)
    (hQC : ∀ η ∈ Q, η.carrier ∈ C.cells) (hτ : τ ∈ Q)
    (hυ : υ ∈ τ.boundaryFacets)
    (hmeet : (intrinsicInterior ℝ υ.carrier ∩ intrinsicInterior ℝ σ.carrier).Nonempty) :
    ∃! η : OrientedCell h k, η ∈ Q ∧ η ≠ τ ∧ υ.reverse ∈ η.boundaryFacets := by
  have := h.finiteDimensional
  classical
  obtain ⟨q, hqυ, hqσ⟩ := hmeet
  obtain ⟨F, hF, hFn, hFd, hυF⟩ := (τ.mem_boundaryFacets υ).mp hυ
  have hFc : υ.carrier = F := by rw [hυF, boundaryFacet_carrier]
  have hproper : F ≠ τ.carrier := by intro he; rw [he] at hFd; omega
  obtain ⟨y, hy, hyF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  obtain ⟨l, hl⟩ := hF hFn
  have hqF : q ∈ F := hFc ▸ intrinsicInterior_subset hqυ
  have hl' : F = l.toExposed τ.carrier := hl
  have hqmax : q ∈ l.toExposed τ.carrier := hl' ▸ hqF
  have hylt : l y < l q := lt_of_le_of_ne (hqmax.2 y hy) (by
    intro he
    exact hyF (hl' ▸ (l.mem_toExposed_iff_of_mem hqmax).mpr ⟨hy, he⟩))
  let f : ℝ → V := fun t => q + t • (q - y)
  have hf : Tendsto f (𝓝 0) (𝓝 q) := by
    have hc : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [f, zero_smul, add_zero] using hc.tendsto 0
  have hfspan (t : ℝ) : f t ∈ affineSpan ℝ σ.carrier := by
    have hqA := subset_affineSpan ℝ σ.carrier (intrinsicInterior_subset hqσ)
    have hyA := subset_affineSpan ℝ σ.carrier (hQ.carrier_subset hτ hy)
    simpa only [f, vadd_eq_add, vsub_eq_sub, add_comm] using
      (affineSpan ℝ σ.carrier).vadd_mem_of_mem_direction
        ((affineSpan ℝ σ.carrier).direction.smul_mem t
          ((affineSpan ℝ σ.carrier).vsub_mem_direction hqA hyA)) hqA
  have hfσ : ∀ᶠ t in 𝓝 0, f t ∈ σ.carrier :=
    (tendsto_nhdsWithin_iff.mpr ⟨hf, Eventually.of_forall hfspan⟩).eventually
      (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hqσ)
  have hυC : υ.carrier ∈ C.cells := by
    rw [hFc]
    exact C.face_closed τ.carrier (hQC τ hτ) F (isPolyhedralFace_iff.mpr ⟨hFn, hF⟩)
  have hinc := hf.eventually (C.eventually_subset_of_mem_cell hυC hqυ)
  -- A short outward ray remains inside the coarse cell. Its containing piece
  -- is distinct from the original one and contains the entire facet.
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htσ, htinc⟩ :=
    (hpos.and ((hfσ.and hinc).filter_mono nhdsWithin_le_nhds)).exists
  have hft : f t ∉ τ.carrier := by
    intro hft
    have hle := hqmax.2 (f t) hft
    simp only [f, map_add, map_smul, map_sub, smul_eq_mul] at hle
    nlinarith [mul_pos ht (sub_pos.mpr hylt)]
  rw [← hQ.biUnion_carrier, Set.mem_iUnion₂] at htσ
  obtain ⟨η, hη, hftη⟩ := htσ
  have hne : η ≠ τ := by rintro rfl; exact hft hftη
  have hsub : υ.carrier ⊆ η.carrier := htinc η.carrier (hQC η hη) hftη
  have hex : IsExposed ℝ η.carrier υ.carrier :=
    (isPolyhedralFace_iff.mp (C.face_of_subset hυC (hQC η hη) hsub)).2
  have hd : finrank ℝ (vectorSpan ℝ υ.carrier) + 1 =
      finrank ℝ (vectorSpan ℝ η.carrier) := by
    have hu := υ.finrank_direction_add
    have he := η.finrank_direction_add
    rw [direction_affineSpan] at hu he
    omega
  -- The common facet has the opposite boundary orientation. A third piece
  -- would repeat this signed facet, contradicting uniqueness of its parent.
  let ω := η.boundaryFacet hex υ.nonempty hd
  have hω : ω ∈ η.boundaryFacets := η.boundaryFacet_mem_boundaryFacets hex υ.nonempty hd
  have hcarne : τ.carrier ≠ η.carrier := by
    intro he
    exact hne (OrientedCell.ext he.symm
      ((hQ.orientation_eq η hη).trans (hQ.orientation_eq τ hτ).symm))
  have hrev : υ.reverse = ω := by
    have he := C.eq_reverse_of_mem_boundaryFacets (hQC τ hτ) (hQC η hη) hcarne
      ((hQ.affineSpan_eq hτ).trans (hQ.affineSpan_eq hη).symm)
      ((hQ.orientation_eq τ hτ).trans (hQ.orientation_eq η hη).symm) hυ hω (by simp [ω])
    exact (congrArg reverse he).trans (reverse_reverse ω)
  refine ⟨η, ⟨hη, hne, hrev ▸ hω⟩, ?_⟩
  rintro ξ ⟨hξ, _, hυξ⟩
  exact C.eq_of_common_boundaryFacet (hQC ξ hξ) (hQC η hη)
    ((hQ.affineSpan_eq hξ).trans (hQ.affineSpan_eq hη).symm)
    ((hQ.orientation_eq ξ hξ).trans (hQ.orientation_eq η hη).symm)
    hυξ (hrev ▸ hω)

/-- Every boundary facet of a subdivision piece is supported on the coarse
relative boundary or has exactly one other incident piece with the opposite
signed orientation. No internal-incidence hypothesis is assumed. -/
theorem carrier_subset_intrinsicFrontier_or_existsUnique_reverse_mem_boundaryFacets
    (hQ : IsOrientedSubdivision σ Q)
    (hQC : ∀ η ∈ Q, η.carrier ∈ C.cells) (hτ : τ ∈ Q)
    (hυ : υ ∈ τ.boundaryFacets) :
    υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier ∨
      ∃! η : OrientedCell h k, η ∈ Q ∧ η ≠ τ ∧ υ.reverse ∈ η.boundaryFacets := by
  have := h.finiteDimensional
  by_cases hb : υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier
  · exact Or.inl hb
  right
  obtain ⟨y, hy, hyb⟩ := Set.not_subset.mp hb
  have hsub := (τ.carrier_subset_of_mem_boundaryFacets hυ).trans (hQ.carrier_subset hτ)
  have hyσ : y ∈ intrinsicInterior ℝ σ.carrier := by
    rw [← intrinsicClosure_sdiff_intrinsicFrontier]
    exact ⟨subset_intrinsicClosure (hsub hy), hyb⟩
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp υ.rational
  have hconvυ : Convex ℝ υ.carrier := hP ▸ P.convex
  obtain ⟨z, hz⟩ := υ.nonempty.intrinsicInterior hconvυ
  apply hQ.existsUnique_reverse_mem_boundaryFacets hQC hτ hυ
  refine ⟨midpoint ℝ z y, ?_, ?_⟩
  · exact hconvυ.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hz (subset_intrinsicClosure hy) (midpoint_mem_openSegment z y)
  · obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    rw [midpoint_comm]
    exact (hP ▸ P.convex).openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
      hyσ (subset_intrinsicClosure (hsub (intrinsicInterior_subset hz)))
      (midpoint_mem_openSegment y z)

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

open Classical in
/-- All internal facet occurrences cancel from the total signed boundary of a
complex subdivision. The sum retains parent indices, so coincident supports
are counted with their actual incidence multiplicities. -/
theorem sum_internal_boundaryFacets_eq_zero
    (hQ : IsOrientedSubdivision σ Q)
    (hQC : ∀ η ∈ Q, η.carrier ∈ C.cells) (c : E) :
    (∑ τ ∈ Q, ∑ υ ∈ τ.boundaryFacets with
      ¬υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier,
      PolyhedralCochain.mk (R := R) υ c) = 0 := by
  classical
  let S := Q.sigma fun τ => τ.boundaryFacets.filter fun υ =>
    ¬υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier
  have hS (x : Σ _ : OrientedCell h k, OrientedCell h (k + 1)) :
      x ∈ S ↔ x.1 ∈ Q ∧ x.2 ∈ x.1.boundaryFacets ∧
        ¬x.2.carrier ⊆ intrinsicFrontier ℝ σ.carrier := by
    simp only [S, Finset.mem_sigma, Finset.mem_filter]
  have hex (x) (hx : x ∈ S) :
      ∃! η : OrientedCell h k, η ∈ Q ∧ η ≠ x.1 ∧ x.2.reverse ∈ η.boundaryFacets := by
    obtain ⟨hxQ, hxF, hxb⟩ := (hS x).mp hx
    exact (hQ.carrier_subset_intrinsicFrontier_or_existsUnique_reverse_mem_boundaryFacets
      hQC hxQ hxF).resolve_left hxb
  let g (x) (hx : x ∈ S) : Σ _ : OrientedCell h k, OrientedCell h (k + 1) :=
    ⟨(hex x hx).choose, x.2.reverse⟩
  have hgmem (x) (hx : x ∈ S) : g x hx ∈ S := by
    obtain ⟨hη, _, hr⟩ := (hex x hx).choose_spec.1
    exact (hS _).mpr ⟨hη, hr, by
      simpa only [g, reverse_carrier] using ((hS x).mp hx).2.2⟩
  have hgg (x) (hx : x ∈ S) : g (g x hx) (hgmem x hx) = x := by
    have hp := (hex x hx).choose_spec.1
    have hfirst : (hex (g x hx) (hgmem x hx)).choose = x.1 :=
      ((hex (g x hx) (hgmem x hx)).choose_spec.2 x.1
        ⟨((hS x).mp hx).1, Ne.symm hp.2.1, by
          simpa only [g, reverse_reverse] using ((hS x).mp hx).2.1⟩).symm
    exact Sigma.ext hfirst (heq_of_eq (reverse_reverse x.2))
  rw [Finset.sum_sigma' Q]
  refine Finset.sum_involution g ?_ ?_ hgmem hgg
  · intro x hx
    simp only [g, PolyhedralCochain.mk_reverse, add_neg_cancel]
  · intro x hx _ he
    exact (hex x hx).choose_spec.1.2.1 (congrArg Sigma.fst he)

open Classical in
/-- The total boundary of all subdivision pieces contains only occurrences on
the coarse relative boundary: every internal occurrence cancels with its
unique oppositely oriented neighbor. -/
theorem sum_cellCoboundary_eq_sum_external_boundaryFacets
    (hQ : IsOrientedSubdivision σ Q)
    (hQC : ∀ η ∈ Q, η.carrier ∈ C.cells) (c : E) :
    (∑ τ ∈ Q, τ.cellCoboundary (R := R) c) =
      ∑ τ ∈ Q, ∑ υ ∈ τ.boundaryFacets with
        υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier, PolyhedralCochain.mk υ c := by
  classical
  have hsplit (τ : OrientedCell h k) : τ.cellCoboundary (R := R) c =
      (∑ υ ∈ τ.boundaryFacets with υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier,
        PolyhedralCochain.mk υ c) +
      ∑ υ ∈ τ.boundaryFacets with ¬υ.carrier ⊆ intrinsicFrontier ℝ σ.carrier,
        PolyhedralCochain.mk υ c := by
    rw [cellCoboundary_apply]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, hQ.sum_internal_boundaryFacets_eq_zero hQC c, add_zero]

end Mei.OrientedCell.IsOrientedSubdivision
