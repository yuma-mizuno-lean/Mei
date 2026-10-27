/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Basic
public import Mei.Geometry.Convex.Polyhedron.Face.Local
public import Mei.Geometry.Affine.Simplex.Ray
import Mathlib.Analysis.Convex.Combination

/-!
# Local Stokes at a boundary facet

At a relative interior point of a wall's boundary facet, every sufficiently
small triangle complementary to the facet direction satisfies the signed
Stokes formula, provided its interior contains the point and its vertices
miss the wall. The radius is independent of the triangle.
Unbounded walls, real offsets and lineality are allowed.

The facet half-space model `exists_ball_inter_eq_halfspace_of_facet` and
`ContinuousLinearMap.exists_halfspace_slice_eq_ray` identify the transverse
section with an inward ray. `Affine.Triangle.exists_ray_exit_edge`
identifies its unique exit edge; the other edges miss the wall. This verifies
the geometric hypotheses of
`OrientedCell.intersectionIndex_boundaryFacet_eq_sum_succAbove` and
`OrientedCell.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove`, whose
contraction calculation and boundary-sum reduction supply the Stokes formulas.
-/

public section

noncomputable section

open Set Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

private theorem exists_exit_of_facet_halfspace
    (σ : OrientedCell h 1) {F : Set V}
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (l : V →L[ℝ] ℝ) (hFl : F = l.toExposed σ.carrier)
    (s : Affine.Triangle ℝ V) {p : V} (hpF : p ∈ F) (hp : p ∈ s.interior)
    (hcompl : IsCompl (vectorSpan ℝ F) (vectorSpan ℝ (range s.points)))
    (hvertices : ∀ j, s.points j ∉ σ.carrier)
    (hlocal : convexHull ℝ (range s.points) ∩ σ.carrier =
      convexHull ℝ (range s.points) ∩ {z | z ∈ affineSpan ℝ σ.carrier ∧ l z ≤ l p}) :
    ∃ (b : Fin 3 → ℝ) (j : Fin 3) (q : V),
      (∀ a, 0 ≤ b a) ∧ ∑ a, b a = 1 ∧ (∑ a, b a • s.points a) ∈ F ∧
      0 < b j ∧ q ∈ convexHull ℝ (range (s.points ∘ j.succAbove)) ∧
      q ∈ σ.carrier ∧ q ∉ F ∧
      ∀ m ≠ j, Disjoint (convexHull ℝ (range (s.points ∘ m.succAbove))) σ.carrier := by
  have := h.finiteDimensional
  -- Identify the wall slice in the triangle plane with the normalized inward ray.
  have hpA := s.closedInterior_subset_affineSpan (s.interior_subset_closedInterior hp)
  have hplane : AffineSubspace.mk' p (vectorSpan ℝ (range s.points)) =
      affineSpan ℝ (range s.points) := by
    rw [← direction_affineSpan, (affineSpan ℝ (range s.points)).mk'_eq hpA]
  obtain ⟨q, hqA, hlq, hray⟩ := l.exists_halfspace_slice_eq_ray (hFl ▸ hpF)
    (hFl ▸ hdim) _ (hFl ▸ hcompl)
  rw [hplane] at hqA hray
  have hqne : q ≠ p := by intro he; rw [he] at hlq; linarith
  have hline (t : ℝ) : l (AffineMap.lineMap p q t) = l p - t := by
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul, hlq]
    ring
  have hmem (z : V) (hz : z ∈ convexHull ℝ (range s.points)) :
      z ∈ σ.carrier ↔ ∃ t : ℝ, 0 ≤ t ∧ AffineMap.lineMap p q t = z := by
    have hzA := s.closedInterior_subset_affineSpan
      (Affine.Simplex.convexHull_eq_closedInterior s ▸ hz)
    have he := Set.ext_iff.mp hlocal z
    simpa only [mem_inter_iff, mem_ofPred_eq, hz, true_and, hray z hzA] using he
  -- The inward ray avoids every vertex because all vertices miss the actual wall support.
  have hv (t : ℝ) (ht : 0 < t) (j : Fin 3) :
      AffineMap.lineMap p q t ≠ s.points j := by
    intro he
    exact hvertices j ((hmem _ (subset_convexHull ℝ _ (mem_range_self j))).mpr
      ⟨t, ht.le, he⟩)
  -- The unique exit edge supplies the chord hypotheses for both Stokes formulas.
  obtain ⟨T, j, hT, hj, hexit⟩ := s.exists_ray_exit_edge hp hqA hqne hv
  have hface (m : Fin 3) :
      convexHull ℝ (range (s.points ∘ m.succAbove)) = (s.faceOpposite m).closedInterior := by
    rw [← Affine.Simplex.convexHull_eq_closedInterior]
    congr 2
    ext a
    simpa using (s.faceOpposite_point_eq_point_succAbove m a).symm
  have hface_sub (m : Fin 3) : convexHull ℝ (range (s.points ∘ m.succAbove)) ⊆
      convexHull ℝ (range s.points) := convexHull_mono (range_comp_subset_range _ _)
  have hjface : AffineMap.lineMap p q T ∈ convexHull ℝ (range (s.points ∘ j.succAbove)) := by
    rw [hface]
    exact (s.faceOpposite j).interior_subset_closedInterior hj
  have hjσ := (hmem _ (hface_sub j hjface)).mpr ⟨T, hT.le, rfl⟩
  have hjF : AffineMap.lineMap p q T ∉ F := by
    intro hm
    have he := ((l.mem_toExposed_iff_of_mem (hFl ▸ hpF)).mp (hFl ▸ hm)).2
    rw [hline] at he
    linarith
  have hdisj (m : Fin 3) (hm : m ≠ j) :
      Disjoint (convexHull ℝ (range (s.points ∘ m.succAbove))) σ.carrier := by
    apply Set.disjoint_left.mpr
    intro z hz hzσ
    obtain ⟨t, ht, rfl⟩ := (hmem z (hface_sub m hz)).mp hzσ
    exact hm (((hexit t ht m).mp (hface m ▸ hz)).2)
  obtain ⟨b, hb, hb01, hbp⟩ := hp
  have hsum : ∑ a, b a • s.points a = p := by
    simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hb] using hbp
  exact ⟨b, j, _, (fun a => (hb01 a).1.le), hb, hsum ▸ hpF,
    (hb01 j).1, hjface, hjσ, hjF, hdisj⟩

/-- In a half-space neighborhood of a wall facet, a complementary triangle
containing a point of the facet in its interior satisfies the signed facet Stokes formula.
The vertices need only avoid the wall itself. -/
theorem intersectionIndex_boundaryFacet_eq_sum_succAbove_of_halfspace
    (σ : OrientedCell h 1) {F : Set V} (hF : IsExposed ℝ σ.carrier F)
    (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    (l : V →L[ℝ] ℝ) (hFl : F = l.toExposed σ.carrier)
    (s : Affine.Triangle ℝ V) {p : V} (hpF : p ∈ F) (hp : p ∈ s.interior)
    (hcompl : IsCompl (vectorSpan ℝ F) (vectorSpan ℝ (range s.points)))
    (hvertices : ∀ j, s.points j ∉ σ.carrier)
    (hlocal : convexHull ℝ (range s.points) ∩ σ.carrier =
      convexHull ℝ (range s.points) ∩ {z | z ∈ affineSpan ℝ σ.carrier ∧ l z ≤ l p}) :
    (σ.boundaryFacet hF hne hdim).intersectionIndex s.points =
      ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (s.points ∘ m.succAbove) := by
  obtain ⟨b, j, q, hb₀, hb₁, hpF', hbj, hqj, hqσ, hqF, hdisj⟩ :=
    exists_exit_of_facet_halfspace σ hdim l hFl s hpF hp hcompl hvertices hlocal
  exact σ.intersectionIndex_boundaryFacet_eq_sum_succAbove hF hne hdim
    hb₀ hb₁ hpF' hbj hqj hqσ hqF hdisj

private theorem stokes_of_facet_halfspace (σ : OrientedCell h 1) {F : Set V}
    (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hpF : p ∈ F) (s : Affine.Triangle ℝ V) (hp : p ∈ s.interior)
    (hT : IsCompl (vectorSpan ℝ F) (vectorSpan ℝ (range s.points)))
    (hv : ∀ j, s.points j ∉ σ.carrier)
    (l : V →L[ℝ] ℝ) (hl : F = l.toExposed σ.carrier)
    (hlocal : ∀ y ∈ convexHull ℝ (range s.points),
      y ∈ σ.carrier ↔ y ∈ affineSpan ℝ σ.carrier ∧ l y ≤ l p)
    (hother : ∀ τ ∈ σ.boundaryFacets, τ.carrier ≠ F →
      Disjoint (convexHull ℝ (range s.points)) τ.carrier) :
    (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
      ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (s.points ∘ m.succAbove) := by
  obtain ⟨b, j, q, hb₀, hb₁, hpF', hbj, hqj, hqσ, hqF, hdisj⟩ :=
    exists_exit_of_facet_halfspace σ hdim l hl s hpF hp hT hv (by
      ext y
      constructor
      · rintro ⟨hy, hyσ⟩
        exact ⟨hy, (hlocal y hy).mp hyσ⟩
      · rintro ⟨hy, hyσ⟩
        exact ⟨hy, (hlocal y hy).mpr hyσ⟩)
  exact σ.sum_intersectionIndex_boundaryFacets_eq_sum_succAbove hF ⟨p, hpF⟩ hdim
    hb₀ hb₁ hpF' hbj hqj hqσ hqF hdisj hother

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
