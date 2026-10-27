/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Basic
public import Mei.Geometry.Convex.Polyhedron.Face.Local
public import Mei.Geometry.Affine.Simplex.Ray
public import Mei.Analysis.Convex.Exposed.Transverse
import Mathlib.Analysis.Convex.Combination

/-!
# Local Stokes at a boundary facet

At a relative interior point of a wall's boundary facet, every sufficiently
small triangle complementary to the facet direction satisfies the signed
Stokes formula, provided its interior contains the point and its vertices
miss the wall. The radius is independent of the triangle.
Unbounded walls, real offsets and lineality are allowed.

The facet half-space model `exists_ball_inter_eq_halfspace_of_facet` and
`ContinuousLinearMap.exists_transverse_halfspace_ray_of_toExposed` cut the
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

private theorem facet_stokes_of_halfspace (σ : OrientedCell h 1) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (l : V →L[ℝ] ℝ) (hl : F = l.toExposed σ.carrier)
    (s : Affine.Triangle ℝ V) {p : V} (hpF : p ∈ F) (hp : p ∈ s.interior)
    (hcompl : IsCompl (vectorSpan ℝ F) (vectorSpan ℝ (range s.points)))
    (hv : ∀ j, s.points j ∉ σ.carrier)
    (hlocal : ∀ z ∈ convexHull ℝ (range s.points),
      z ∈ σ.carrier ↔ z ∈ affineSpan ℝ σ.carrier ∧ l z ≤ l p)
    (hmiss : ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (convexHull ℝ (range s.points)) τ.carrier) :
    (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
      ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (s.points ∘ m.succAbove) := by
  have := h.finiteDimensional
  -- In the triangle plane, the supporting half-space is precisely one inward ray.
  obtain ⟨u, hu, hlu, hray⟩ := l.exists_transverse_halfspace_ray_of_toExposed
    (hl ▸ hpF) (hl ▸ hdim) (vectorSpan ℝ (range s.points)) (hl ▸ hcompl)
  have hpA : p ∈ affineSpan ℝ σ.carrier := subset_affineSpan ℝ _ (hF.subset hpF)
  have hpS : p ∈ affineSpan ℝ (range s.points) :=
    s.closedInterior_subset_affineSpan (s.interior_subset_closedInterior hp)
  have hu0 : u ≠ 0 := by intro he; simp [he] at hlu
  have hline (t : ℝ) : AffineMap.lineMap p (p + u) t = p + t • u := by
    simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  have hqA : p + u ∈ affineSpan ℝ (range s.points) := by
    have hm := (affineSpan ℝ (range s.points)).vadd_mem_of_mem_direction
      (by rw [direction_affineSpan]; exact hu.2) hpS
    simpa only [vadd_eq_add, add_comm] using hm
  have hlineA (t : ℝ) : AffineMap.lineMap p (p + u) t ∈ affineSpan ℝ σ.carrier := by
    rw [hline]
    have hm := (affineSpan ℝ σ.carrier).vadd_mem_of_mem_direction
      (by simpa only [direction_affineSpan] using (vectorSpan ℝ σ.carrier).smul_mem t hu.1) hpA
    simpa only [vadd_eq_add, add_comm] using hm
  -- Vertex avoidance forces a unique exit edge, with no intersection on the other edges.
  obtain ⟨t, m, ht, hedge, hunique⟩ := s.exists_ray_exit_edge hp hqA
    (by intro he; exact hu0 (add_left_cancel (he.trans (add_zero p).symm)))
    (fun a ha j he => by
      apply hv j
      apply (hlocal _ (subset_convexHull ℝ _ (mem_range_self j))).mpr
      refine ⟨he ▸ hlineA a, ?_⟩
      rw [← he, hline, map_add, map_smul, hlu, smul_eq_mul, mul_neg_one]
      exact add_le_of_nonpos_right (neg_nonpos.mpr ha.le))
  have hface (j : Fin 3) : convexHull ℝ (range (s.points ∘ j.succAbove)) =
      (s.faceOpposite j).closedInterior := by
    have he : s.points ∘ j.succAbove = (s.faceOpposite j).points :=
      funext fun a => (s.faceOpposite_point_eq_point_succAbove j a).symm
    rw [he, Affine.Simplex.convexHull_eq_closedInterior]
  let q := AffineMap.lineMap p (p + u) t
  have hqm : q ∈ convexHull ℝ (range (s.points ∘ m.succAbove)) := by
    rw [hface]
    exact (s.faceOpposite m).interior_subset_closedInterior hedge
  have hqS : q ∈ convexHull ℝ (range s.points) :=
    convexHull_mono (range_comp_subset_range _ _) hqm
  have hqσ : q ∈ σ.carrier := (hlocal q hqS).mpr ⟨hlineA t, by
    simp only [q, hline, map_add, map_smul, hlu, smul_eq_mul, mul_neg_one]
    exact add_le_of_nonpos_right (neg_nonpos.mpr ht.le)⟩
  have hqF : q ∉ F := by
    intro hqF
    have he := (l.mem_toExposed_iff_of_mem (hl ▸ hpF)).mp (hl ▸ hqF)
    have hlq : l q = l p - t := by
      simp only [q, hline, map_add, map_smul, hlu, smul_eq_mul, mul_neg_one, sub_eq_add_neg]
    linarith [he.2]
  have hdisj (j : Fin 3) (hjm : j ≠ m) :
      Disjoint (convexHull ℝ (range (s.points ∘ j.succAbove))) σ.carrier := by
    apply Set.disjoint_left.mpr
    intro z hz hzσ
    have hzS : z ∈ convexHull ℝ (range s.points) :=
      convexHull_mono (range_comp_subset_range _ _) hz
    have hzT : z - p ∈ vectorSpan ℝ (range s.points) := by
      rw [← direction_affineSpan]
      exact (affineSpan ℝ (range s.points)).vsub_mem_direction
        (convexHull_subset_affineSpan _ hzS) hpS
    obtain ⟨a, ha, hza⟩ := (hray z).mp ⟨hzT, (hlocal z hzS).mp hzσ⟩
    have hzedge : AffineMap.lineMap p (p + u) a ∈ (s.faceOpposite j).closedInterior := by
      rw [hline, ← hza, ← hface]
      exact hz
    exact hjm ((hunique a ha j).mp hzedge).2
  -- Apply the existing one-facet sign formula with the actual exit geometry.
  obtain ⟨b, hb, hb01, hbp⟩ := hp
  have hsum : ∑ j, b j • s.points j = p := by
    simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hb] using hbp
  exact σ.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove hF ⟨p, hpF⟩ hdim
    (fun j => (hb01 j).1.le) hb (hsum ▸ hpF) (hb01 m).1 hqm hqσ hqF hdisj hmiss

/-- At a relative interior point of a wall facet there is a ball on which
Stokes holds for every transverse triangle containing that point in its
interior and whose vertices miss the wall. The signed facet
sum and the signed edge sum use the same vertex order. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet
    (σ : OrientedCell h 1) {F : Set V} (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hp : p ∈ intrinsicInterior ℝ F) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V, p ∈ s.interior →
      IsCompl (affineSpan ℝ F).direction (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε →
      (∀ j, s.points j ∉ σ.carrier) →
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
  apply facet_stokes_of_halfspace σ hF hdim l hl s (intrinsicInterior_subset hp) hps
    (by simpa only [direction_affineSpan] using hT) hv
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
