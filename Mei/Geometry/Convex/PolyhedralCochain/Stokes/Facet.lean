/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Basic
public import Mei.Geometry.Convex.Polyhedron.Face.Local
public import Mei.Geometry.Affine.Simplex.Ray
import Mei.LinearAlgebra.Submodule.Ray
import Mathlib.Analysis.Convex.Combination

/-!
# Local Stokes at a boundary facet

At a relative interior point of a wall's boundary facet, every sufficiently
small triangle complementary to the facet direction satisfies the signed
Stokes formula, provided its interior contains the point and its vertices
miss the wall's affine span. The radius is independent of the triangle.
Unbounded walls, real offsets and lineality are allowed.

The facet half-space model `exists_ball_inter_eq_halfspace_of_facet` cuts the
transverse plane in an inward ray. `Affine.Triangle.exists_ray_exit_edge`
identifies its unique exit edge; the other edges miss the wall. This verifies
the geometric hypotheses of
`OrientedCell.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove`, whose
contraction calculation supplies the orientation signs.
-/

public section

noncomputable section

open Set Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

private theorem stokes_of_facet_halfspace (σ : OrientedCell h 1) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hpF : p ∈ F) (s : Affine.Triangle ℝ V) (hp : p ∈ s.interior)
    (hT : IsCompl (vectorSpan ℝ F) (vectorSpan ℝ (range s.points)))
    (hv : ∀ j, s.points j ∉ affineSpan ℝ σ.carrier)
    (l : V →L[ℝ] ℝ) (hl : F = l.toExposed σ.carrier)
    (hlocal : ∀ y ∈ convexHull ℝ (range s.points),
      y ∈ σ.carrier ↔ y ∈ affineSpan ℝ σ.carrier ∧ l y ≤ l p)
    (hother : ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (convexHull ℝ (range s.points)) τ.carrier) :
    (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
      ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (s.points ∘ m.succAbove) := by
  have := h.finiteDimensional
  -- Slice the facet half-space by the complementary triangle plane.
  let T := vectorSpan ℝ (range s.points)
  have hpA : p ∈ affineSpan ℝ σ.carrier := subset_affineSpan ℝ _ (hF.subset hpF)
  have hpS : p ∈ affineSpan ℝ (range s.points) := s.setInterior_subset_affineSpan hp
  have hproper : F ≠ σ.carrier := by intro he; rw [he] at hdim; omega
  obtain ⟨x, hx, hxF⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hF.subset hproper)
  have hpx : p ∈ l.toExposed σ.carrier := hl ▸ hpF
  have hlt : l x < l p := lt_of_le_of_ne (hpx.2 x hx) (fun he =>
    hxF (hl ▸ (l.mem_toExposed_iff_of_mem hpx).mpr ⟨hx, he⟩))
  obtain ⟨w, hw, hwl, hray⟩ := (vectorSpan ℝ σ.carrier).exists_neg_ray_of_isCompl
    (vectorSpan ℝ F) T (vectorSpan_mono ℝ hF.subset) hdim hT l.toLinearMap
    (by rw [hl]; exact l.vectorSpan_toExposed_le_ker σ.carrier)
    ⟨x - p, vsub_mem_vectorSpan ℝ hx (hF.subset hpF), by simpa using sub_neg.mpr hlt⟩
  simp only [ContinuousLinearMap.coe_coe] at hwl hray
  let q := w + p
  have hqS : q ∈ affineSpan ℝ (range s.points) := by
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hpS q).mp
    simp only [q, vsub_eq_sub, add_sub_cancel_right, direction_affineSpan]
    exact hw.2
  have hqp : q ≠ p := by
    intro he
    have hw0 : w = 0 := add_right_cancel (he.trans (zero_add p).symm)
    simp [hw0] at hwl
  have hline (t : ℝ) : AffineMap.lineMap p q t = t • w + p := by
    simp [AffineMap.lineMap_apply, q]
  have hplane (t : ℝ) : AffineMap.lineMap p q t ∈ affineSpan ℝ σ.carrier := by
    apply (AffineSubspace.vsub_right_mem_direction_iff_mem hpA _).mp
    simpa only [hline, vsub_eq_sub, add_sub_cancel_right, direction_affineSpan]
      using (vectorSpan ℝ σ.carrier).smul_mem t hw.1
  -- The inward ray exits exactly one edge, away from every vertex.
  obtain ⟨t, j, ht, hj, hexit⟩ := s.exists_ray_exit_edge hp hqS hqp
    (fun t _ j he => hv j (he ▸ hplane t))
  let y := AffineMap.lineMap p q t
  have hyHull : y ∈ convexHull ℝ (range s.points) := by
    rw [s.convexHull_eq_closedInterior]
    exact s.closedInterior_faceOpposite_subset_closedInterior j
      ((s.faceOpposite j).interior_subset_closedInterior hj)
  have hyl : l y < l p := by
    have he : l y = t * l w + l p := by simp only [y, hline, map_add, map_smul, smul_eq_mul]
    rw [he]
    linarith [mul_neg_of_pos_of_neg ht hwl]
  have hyσ : y ∈ σ.carrier := (hlocal y hyHull).mpr ⟨hplane t, hyl.le⟩
  have hyF : y ∉ F := by
    intro hy
    have he := (l.mem_toExposed_iff_of_mem hpx).mp (hl ▸ hy)
    exact hyl.ne he.2
  have hface (m : Fin 3) : convexHull ℝ (range (s.points ∘ m.succAbove)) =
      (s.faceOpposite m).closedInterior := by
    rw [← (s.faceOpposite m).convexHull_eq_closedInterior,
      s.range_faceOpposite_points, range_comp, Fin.range_succAbove]
  -- Any other edge intersection would lie on the same ray, contradicting its unique exit.
  have hdisj (m : Fin 3) (hm : m ≠ j) :
      Disjoint (convexHull ℝ (range (s.points ∘ m.succAbove))) σ.carrier := by
    apply Set.disjoint_left.mpr
    intro z hz hzσ
    have hzHull : z ∈ convexHull ℝ (range s.points) :=
      convexHull_mono (range_comp_subset_range _ _) hz
    have hzT : z - p ∈ T := by
      simpa only [T, vsub_eq_sub, direction_affineSpan] using
        (affineSpan ℝ (range s.points)).vsub_mem_direction
          (convexHull_subset_affineSpan _ hzHull) hpS
    have hzA := (hlocal z hzHull).mp hzσ
    have hzU : z - p ∈ vectorSpan ℝ σ.carrier := by
      simpa only [vsub_eq_sub, direction_affineSpan] using
        (affineSpan ℝ σ.carrier).vsub_mem_direction hzA.1 hpA
    obtain ⟨a, ha, haz⟩ := (hray (z - p) hzT).mp
      ⟨hzU, by simpa only [map_sub] using sub_nonpos.mpr hzA.2⟩
    have he : AffineMap.lineMap p q a = z := by rw [hline, haz]; abel
    have hmj := ((hexit a ha m).mp (he.symm ▸ (hface m ▸ hz))).2
    exact hm hmj
  -- The established chord geometry lets the existing contraction formula supply the signs.
  obtain ⟨b, hb, hb01, hbp⟩ := hp
  have hpSum : ∑ a, b a • s.points a ∈ F := by
    rw [← Finset.affineCombination_eq_linear_combination _ _ _ hb, hbp]
    exact hpF
  exact σ.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove hF ⟨p, hpF⟩ hdim
    (fun a => (hb01 a).1.le) hb hpSum ((hb01 j).1) (hface j ▸
      (s.faceOpposite j).interior_subset_closedInterior hj) hyσ hyF hdisj hother

/-- At a relative interior point of a wall facet there is a ball on which
Stokes holds for every transverse triangle containing that point in its
interior and whose vertices miss the wall's affine span. The signed facet
sum and the signed edge sum use the same vertex order. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet
    (σ : OrientedCell h 1) {F : Set V} (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hp : p ∈ intrinsicInterior ℝ F) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, p ∈ s.interior →
      IsCompl (affineSpan ℝ F).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε →
      (∀ j, s.points j ∉ affineSpan ℝ σ.carrier) →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (s.points ∘ m.succAbove) := by
  classical
  have := h.finiteDimensional
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  have hpoly : TauCeti.IsConvexPolyhedron σ.carrier := hP ▸ P.isConvexPolyhedron
  obtain ⟨l, ε, hε, hl, hlocal, -⟩ :=
    hpoly.exists_ball_inter_eq_halfspace_of_facet hF hdim hp
  let S := σ.boundaryFacets.filter (fun τ => τ.carrier ≠ F)
  have hpnot : p ∉ ⋃ τ ∈ S, τ.carrier := by
    intro hmem
    obtain ⟨τ, hτ, hpτ⟩ := mem_iUnion₂.mp hmem
    obtain ⟨hτmem, hτne⟩ := Finset.mem_filter.mp hτ
    obtain ⟨G, hG, hGn, hGd, hτG⟩ := (σ.mem_boundaryFacets τ).mp hτmem
    have he : τ.carrier = G := by rw [hτG, boundaryFacet_carrier]
    rw [he] at hpτ hτne
    have hinter : IsExposed ℝ F (F ∩ G) := by
      simpa only [inter_eq_left.mpr hF.subset] using (IsExposed.refl F).inter_inter hG
    have hFG : F ⊆ G := inter_eq_left.mp
      (hinter.eq_of_mem_intrinsicInterior ⟨intrinsicInterior_subset hp, hpτ⟩ hp)
    exact hτne (hF.eq_of_subset_of_finrank_add_one ⟨p, intrinsicInterior_subset hp⟩ hdim
      hG hFG (by intro heq; rw [heq] at hGd; omega)).symm
  have hclosed : IsClosed (⋃ τ ∈ S, τ.carrier) :=
    S.finite_toSet.isClosed_biUnion fun τ _ => τ.isClosed_carrier
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl p hpnot
  refine ⟨min ε δ, lt_min hε hδ, fun s hps hT hs hv => ?_⟩
  apply stokes_of_facet_halfspace σ hF hdim (intrinsicInterior_subset hp) s hps
    (by simpa only [direction_affineSpan] using hT) hv l hl
  · intro y hy
    have hyball := Metric.ball_subset_ball (min_le_left _ _) (hs hy)
    have he := Set.ext_iff.mp hlocal y
    exact ⟨fun hyσ => (he.mp ⟨hyball, hyσ⟩).2,
      fun hyσ => (he.mpr ⟨hyball, hyσ⟩).2⟩
  · intro τ hτ hτne
    apply Set.disjoint_left.mpr
    intro y hy hyτ
    exact hball (Metric.ball_subset_ball (min_le_right _ _) (hs hy))
      (mem_iUnion₂.mpr ⟨τ, Finset.mem_filter.mpr ⟨hτ, hτne⟩, hyτ⟩)

end Mei.OrientedCell
