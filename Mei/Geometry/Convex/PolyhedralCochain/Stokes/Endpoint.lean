/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Basic
public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.Polyhedron.Face.Local
import Mathlib.Algebra.Order.Field.Pi

/-!
# Local endpoint Stokes for polyhedral potentials

A full-dimensional oriented polyhedron is a locally constant potential away
from its boundary. Near a relative interior point of a facet, pairing its
complete signed boundary with a segment gives the value of that potential at
the target minus its value at the source. The endpoints may lie on either
side; stationary segments and segments missing the facet are included.
The neighborhood works uniformly for all segments with endpoints off the
facet, without a bound on their transverse angle.

Finite presentations share a common neighborhood at every point avoiding
all relative frontiers of their boundary facets. Coefficients lie in modules
over arbitrary associative rings, including torsion coefficients. The result
is local; integrating along a general polygonal path requires subdivision.

These comparisons turn polyhedral primitives into local transport potentials.
They use the actual half-space model
`TauCeti.IsConvexPolyhedron.exists_ball_inter_eq_halfspace_of_facet` and the
orientation calculation
`OrientedCell.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove`.
The facet-isolation argument of
`OrientedCell.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet`
is shared through `OrientedCell.exists_ball_disjoint_other_boundaryFacets`.
-/

public section

noncomputable section

open Set Module Topology

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

private theorem endpoint_stokes_of_opposite_sides (σ : OrientedCell h 0)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (l : V →L[ℝ] ℝ) (b : ℝ) (x y : V)
    (hx : l x ≠ b) (hy : l y ≠ b) (hop : (l x < b) ≠ (l y < b))
    (hlocal : ∀ z ∈ segment ℝ x y, z ∈ σ.carrier ↔ l z ≤ b)
    (hplane : ∀ z ∈ segment ℝ x y, z ∈ F ↔ l z = b)
    (hother : ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (segment ℝ x y) τ.carrier) :
    ∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![y] - σ.intersectionIndex ![x] := by
  -- Opposite endpoint sides give an interior point on the actual facet.
  have hb : b ∈ openSegment ℝ (l x) (l y) := by
    rw [openSegment_eq_Ioo' (by grind : l x ≠ l y), mem_Ioo, min_lt_iff, lt_max_iff]
    grind
  have himage : l '' openSegment ℝ x y = openSegment ℝ (l x) (l y) := by
    simpa using image_openSegment ℝ l.toLinearMap.toAffineMap x y
  rw [← himage, openSegment_eq_image_lineMap] at hb
  obtain ⟨_, ⟨t, ht, rfl⟩, htb⟩ := hb
  let w : Fin 2 → ℝ := ![1 - t, t]
  have hw : ∑ j, w j = 1 := by simp [w]
  have hp : ∑ j, w j • (![x, y] : Fin 2 → V) j ∈ F := by
    have he : ∑ j, w j • (![x, y] : Fin 2 → V) j = AffineMap.lineMap x y t := by
      simp [w, AffineMap.lineMap_apply_module]
    rw [he]
    exact (hplane _ (lineMap_mem_segment ℝ x y ⟨ht.1.le, ht.2.le⟩)).mpr htb
  have hface (m : Fin 2) :
      (![x, y] : Fin 2 → V) ∘ m.succAbove = ![if m = 0 then y else x] := by
    ext a
    fin_cases a
    fin_cases m <;> rfl
  -- Choose the parameter face at the inside endpoint; the other face misses the cell.
  let j : Fin 2 := if l x < b then 1 else 0
  let q : V := if l x < b then x else y
  have hq : q ∈ σ.carrier ∧ q ∉ F := by
    dsimp only [q]
    split_ifs with hxb
    · exact ⟨(hlocal x (left_mem_segment ℝ x y)).mpr hxb.le,
        fun hm => hx ((hplane x (left_mem_segment ℝ x y)).mp hm)⟩
    · have hyb : l y < b := by grind
      exact ⟨(hlocal y (right_mem_segment ℝ x y)).mpr hyb.le,
        fun hm => hy ((hplane y (right_mem_segment ℝ x y)).mp hm)⟩
  have hjq : q ∈ convexHull ℝ (range ((![x, y] : Fin 2 → V) ∘ j.succAbove)) := by
    rw [hface]
    by_cases hxb : l x < b <;> simp [q, j, hxb, Matrix.range_cons]
  have hdisj (m : Fin 2) (hm : m ≠ j) :
      Disjoint (convexHull ℝ (range ((![x, y] : Fin 2 → V) ∘ m.succAbove))) σ.carrier := by
    have hout : if l x < b then y ∉ σ.carrier else x ∉ σ.carrier := by
      split_ifs with hxb
      · intro hyσ
        have hyb := (hlocal y (right_mem_segment ℝ x y)).mp hyσ
        grind
      · intro hxσ
        have hxb' := (hlocal x (left_mem_segment ℝ x y)).mp hxσ
        grind
    rw [hface]
    by_cases hxb : l x < b
    · have hm0 : m = 0 := by simp only [j, ite_eq_left hxb] at hm; fin_cases m <;> grind
      subst m
      simpa [hxb, Matrix.range_cons] using hout
    · have hm1 : m = 1 := by simp only [j, ite_eq_right hxb] at hm; fin_cases m <;> grind
      subst m
      simpa [hxb, Matrix.range_cons] using hout
  -- Apply the signed facet formula, then read the two parameter faces as endpoints.
  have hs := σ.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove hF hne hdim
    (v := ![x, y]) (b := w) (by intro a; fin_cases a <;> simp [w] <;> linarith [ht.1, ht.2])
    hw hp (l := j) (by dsimp [j]; split_ifs <;> simp [w] <;> linarith [ht.1, ht.2])
    hjq hq.1 hq.2 hdisj
    (by
      intro τ hτ hn
      rw [Matrix.range_cons_cons_empty, convexHull_pair]
      exact hother τ hτ hn)
  simp only [hface] at hs
  rw [Fin.sum_univ_two] at hs
  simpa only [Fin.val_zero, Fin.val_one, ite_true,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0), pow_zero, pow_one,
    one_mul, neg_one_mul, sub_eq_add_neg] using hs

private theorem endpoint_stokes_of_halfspace (σ : OrientedCell h 0)
    {F : Set V} (hF : IsExposed ℝ σ.carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (l : V →L[ℝ] ℝ) (b : ℝ) (x y : V)
    (hx : l x ≠ b) (hy : l y ≠ b)
    (hlocal : ∀ z ∈ segment ℝ x y, z ∈ σ.carrier ↔ l z ≤ b)
    (hplane : ∀ z ∈ segment ℝ x y, z ∈ F ↔ l z = b)
    (hother : ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (segment ℝ x y) τ.carrier) :
    ∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![y] - σ.intersectionIndex ![x] := by
  by_cases hop : (l x < b) ≠ (l y < b)
  · exact endpoint_stokes_of_opposite_sides σ hF hne hdim l b x y hx hy hop
      hlocal hplane hother
  have heq : (l x < b) ↔ (l y < b) := by grind
  have hmiss : Disjoint (segment ℝ x y) F := by
    apply disjoint_left.mpr
    intro z hz hzF
    have hzplane := (hplane z hz).mp hzF
    have hzl : l z ∈ segment ℝ (l x) (l y) := by
      have himage : l '' segment ℝ x y = segment ℝ (l x) (l y) := by
        simpa using image_segment ℝ l.toLinearMap.toAffineMap x y
      rw [← himage]
      exact mem_image_of_mem _ hz
    rw [hzplane, segment_eq_Icc', mem_Icc] at hzl
    grind
  have hdisj (τ) (hτ : τ ∈ σ.boundaryFacets) : Disjoint (segment ℝ x y) τ.carrier := by
    by_cases he : τ.carrier = F
    · rwa [he]
    · exact hother τ hτ he
  rw [Finset.sum_eq_zero fun τ hτ => intersectionIndex_of_disjoint (v := ![x, y])
    (by rw [Matrix.range_cons_cons_empty, convexHull_pair]; exact hdisj τ hτ)]
  have hmem : x ∈ σ.carrier ↔ y ∈ σ.carrier := by
    rw [hlocal x (left_mem_segment ℝ x y), hlocal y (right_mem_segment ℝ x y)]
    grind
  rw [intersectionIndex_singleton, intersectionIndex_singleton, ← hmem, sub_self]

/-- At a relative interior point of a facet of a full-dimensional cell, every
sufficiently small segment with endpoints off the facet satisfies
endpoint Stokes. The complete signed boundary is used, and neither endpoint
is required to lie inside the parent cell. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sub_endpoints
    (σ : OrientedCell h 0) {F : Set V} (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hp : p ∈ intrinsicInterior ℝ F) :
    ∃ ε > 0, ∀ x ∈ Metric.ball p ε, ∀ y ∈ Metric.ball p ε,
      x ∉ F → y ∉ F →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex ![x, y]) =
        σ.intersectionIndex ![y] - σ.intersectionIndex ![x] := by
  classical
  have := h.finiteDimensional
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  have hpoly : TauCeti.IsConvexPolyhedron σ.carrier := hP ▸ P.isConvexPolyhedron
  have htop : affineSpan ℝ σ.carrier = ⊤ := by
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      (σ.nonempty.mono (subset_affineSpan ℝ _))).mp
    apply Submodule.eq_top_of_finrank_eq
    simpa using σ.finrank_direction_add
  obtain ⟨l, ε, hε, hl, hlocal, hplane⟩ :=
    hpoly.exists_ball_inter_eq_halfspace_of_facet hF hdim hp
  obtain ⟨δ, hδ, hδball⟩ := σ.exists_ball_disjoint_other_boundaryFacets hF hdim hp
  refine ⟨min ε δ, lt_min hε hδ, fun x hx y hy hxF hyF => ?_⟩
  have hseg := (convex_ball p (min ε δ)).segment_subset hx hy
  have hsmall : segment ℝ x y ⊆ Metric.ball p ε :=
    hseg.trans (Metric.ball_subset_ball (min_le_left _ _))
  have hside (z) (hz : z ∈ segment ℝ x y) : z ∈ σ.carrier ↔ l z ≤ l p := by
    have he := Set.ext_iff.mp hlocal z
    simpa only [mem_inter_iff, htop, AffineSubspace.mem_top, mem_ofPred_eq,
      true_and, hsmall hz] using he
  have hflat (z) (hz : z ∈ segment ℝ x y) : z ∈ F ↔ l z = l p := by
    have he := Set.ext_iff.mp hplane z
    simpa only [mem_inter_iff, htop, AffineSubspace.mem_top, mem_ofPred_eq,
      true_and, hsmall hz] using he
  apply endpoint_stokes_of_halfspace σ hF ⟨p, intrinsicInterior_subset hp⟩ hdim l (l p) x y
    (fun he => hxF ((hflat x (left_mem_segment ℝ x y)).mpr he))
    (fun he => hyF ((hflat y (right_mem_segment ℝ x y)).mpr he))
    hside hflat
  intro τ hτ hn
  exact (hδball τ hτ hn).mono_left
    (hseg.trans (Metric.ball_subset_ball (min_le_right _ _)))

/-- At any point outside the relative frontiers of the boundary facets, a
full-dimensional cell satisfies endpoint Stokes on one neighborhood. Endpoints
avoid the actual signed boundary supports; they may lie inside or outside the cell. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sub_endpoints_of_regular
    (σ : OrientedCell h 0) (p : V)
    (hregular : ∀ τ ∈ σ.boundaryFacets, p ∉ intrinsicFrontier ℝ τ.carrier) :
    ∃ ε > 0, ∀ x ∈ Metric.ball p ε, ∀ y ∈ Metric.ball p ε,
      (∀ τ ∈ σ.boundaryFacets, x ∉ τ.carrier) →
      (∀ τ ∈ σ.boundaryFacets, y ∉ τ.carrier) →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex ![x, y]) =
        σ.intersectionIndex ![y] - σ.intersectionIndex ![x] := by
  have := h.finiteDimensional
  by_cases hfront : p ∈ intrinsicFrontier ℝ σ.carrier
  · rw [σ.intrinsicFrontier_eq_biUnion_boundaryFacets] at hfront
    obtain ⟨τ, hτ, hpτ⟩ := mem_iUnion₂.mp hfront
    have hpint : p ∈ intrinsicInterior ℝ τ.carrier := by
      rw [← intrinsicClosure_sdiff_intrinsicFrontier]
      exact ⟨subset_intrinsicClosure hpτ, hregular τ hτ⟩
    obtain ⟨F, hF, hFn, hFd, rfl⟩ := (σ.mem_boundaryFacets τ).mp hτ
    simp only [boundaryFacet_carrier] at hpint
    obtain ⟨ε, hε, he⟩ :=
      σ.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sub_endpoints hF hFd hpint
    refine ⟨ε, hε, fun x hx y hy hxτ hyτ => he x hx y hy ?_ ?_⟩
    · simpa only [boundaryFacet_carrier] using hxτ _ hτ
    · simpa only [boundaryFacet_carrier] using hyτ _ hτ
  -- Off the entire boundary, membership and the point index are locally constant.
  have htop : affineSpan ℝ σ.carrier = ⊤ := by
    apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      (σ.nonempty.mono (subset_affineSpan ℝ _))).mp
    exact Submodule.eq_top_of_finrank_eq (by simpa using σ.finrank_direction_add)
  have hmem : ∀ᶠ z in 𝓝 p, z ∈ σ.carrier ↔ p ∈ σ.carrier := by
    by_cases hpσ : p ∈ σ.carrier
    · have hpi : p ∈ interior σ.carrier := by
        rw [← Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top htop,
          ← intrinsicClosure_sdiff_intrinsicFrontier]
        exact ⟨subset_intrinsicClosure hpσ, hfront⟩
      filter_upwards [mem_interior_iff_mem_nhds.mp hpi] with z hz
      exact iff_of_true hz hpσ
    · filter_upwards [σ.isClosed_carrier.isOpen_compl.mem_nhds hpσ] with z hz
      exact iff_of_false hz hpσ
  have hclosed : IsClosed (intrinsicFrontier ℝ σ.carrier) :=
    isClosed_intrinsicFrontier (affineSpan ℝ σ.carrier).closed_of_finiteDimensional
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp
    (hmem.and (hclosed.isOpen_compl.mem_nhds hfront))
  refine ⟨ε, hε, fun x hx y hy _ _ => ?_⟩
  have hseg := (convex_ball p ε).segment_subset hx hy
  have hdisj (τ) (hτ : τ ∈ σ.boundaryFacets) : Disjoint (segment ℝ x y) τ.carrier := by
    apply disjoint_left.mpr
    intro z hz hzτ
    exact (he (Metric.mem_ball.mp (hseg hz))).2
      (σ.intrinsicFrontier_eq_biUnion_boundaryFacets ▸ mem_iUnion₂.mpr ⟨τ, hτ, hzτ⟩)
  rw [Finset.sum_eq_zero fun τ hτ => intersectionIndex_of_disjoint (v := ![x, y])
    (by rw [Matrix.range_cons_cons_empty, convexHull_pair]; exact hdisj τ hτ),
    intersectionIndex_singleton, intersectionIndex_singleton,
    (he (Metric.mem_ball.mp hx)).1, (he (Metric.mem_ball.mp hy)).1, sub_self]

end Mei.OrientedCell

namespace Mei.PolyhedralCochain

variable {N V R E : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  [Ring R] [AddCommGroup E] [Module R E]

/-- A finite full-dimensional potential satisfies endpoint Stokes on a common
neighborhood of each point avoiding all facet frontiers. Pairing its complete
signed boundary with a segment gives the difference of its point evaluations.
Coefficients may have torsion, and coincident boundary contributions are added. -/
theorem exists_ball_intersectionPairing_coboundaryPresentation_eq_sub
    (f : OrientedCell h 0 →₀ E) (p : V)
    (hregular : ∀ σ ∈ f.support, ∀ τ ∈ σ.boundaryFacets,
      p ∉ intrinsicFrontier ℝ τ.carrier) :
    ∃ ε > 0, ∀ x ∈ Metric.ball p ε, ∀ y ∈ Metric.ball p ε,
      (∀ σ ∈ f.support, ∀ τ ∈ σ.boundaryFacets, x ∉ τ.carrier) →
      (∀ σ ∈ f.support, ∀ τ ∈ σ.boundaryFacets, y ∉ τ.carrier) →
      OrientedCell.intersectionPairing (R := R) ![x, y] (coboundaryPresentation (R := R) f) =
        OrientedCell.intersectionPairing (R := R) ![y] f -
          OrientedCell.intersectionPairing (R := R) ![x] f := by
  classical
  choose δ hδ he using fun σ : f.support =>
    σ.val.exists_ball_sum_intersectionIndex_boundaryFacets_eq_sub_endpoints_of_regular p
      (hregular σ.val σ.property)
  obtain ⟨ε, hε, hεδ⟩ := Pi.exists_forall_pos_add_lt hδ
  refine ⟨ε, hε, fun x hx y hy hxτ hyτ => ?_⟩
  have hcell (σ) (hσ : σ ∈ f.support) := he ⟨σ, hσ⟩ x
    (Metric.ball_subset_ball (by simpa using (hεδ ⟨σ, hσ⟩).le) hx) y
    (Metric.ball_subset_ball (by simpa using (hεδ ⟨σ, hσ⟩).le) hy)
    (hxτ σ hσ) (hyτ σ hσ)
  calc
    OrientedCell.intersectionPairing (R := R) ![x, y] (coboundaryPresentation (R := R) f) =
        ∑ σ ∈ f.support, (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex ![x, y]) • f σ := by
      conv_lhs => rw [← Finsupp.sum_single f]
      simp only [coboundaryPresentation_single, map_sum,
        OrientedCell.intersectionPairing_single, Finset.sum_smul, Finsupp.sum]
    _ = ∑ σ ∈ f.support, (σ.intersectionIndex ![y] - σ.intersectionIndex ![x]) • f σ := by
      exact Finset.sum_congr rfl fun σ hσ => congrArg (fun n : ℤ => n • f σ) (hcell σ hσ)
    _ = _ := by
      simp only [sub_smul, Finset.sum_sub_distrib,
        OrientedCell.intersectionPairing_apply, Finsupp.sum]

end Mei.PolyhedralCochain
