/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Stokes.Basic
public import Mei.Geometry.Convex.Polyhedron.Face.Local
public import Mei.Geometry.Affine.Simplex.Ray
public import Mathlib.Analysis.Convex.Combination

/-!
# Local Stokes at a wall facet

A small triangle complementary to a wall facet and containing a relative interior
point of that facet crosses the wall through exactly one edge. Its intersection
with the signed facet therefore equals the signed sum of its edge intersections
with the wall. Shrinking the neighborhood excludes all other boundary facets,
giving the Stokes formula for the complete signed boundary of the wall.

The geometry combines `ContinuousLinearMap.exists_halfspace_slice_eq_ray`,
`TauCeti.IsConvexPolyhedron.exists_ball_inter_eq_halfspace_of_facet`, and
`Affine.Triangle.exists_ray_exit_edge`. The sign calculation is the existing
`OrientedCell.intersectionIndex_boundaryFacet_eq_sum_succAbove`. Real offsets,
unbounded walls and lineality are allowed.
-/

public section

noncomputable section

open Set Module

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- In a half-space neighborhood of a wall facet, a complementary triangle
containing a point of the facet satisfies the signed facet Stokes formula.
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
  -- The unique exit edge supplies the chord hypotheses for the existing sign formula.
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
  exact σ.intersectionIndex_boundaryFacet_eq_sum_succAbove hF hne hdim
    (fun a => (hb01 a).1.le) hb (hsum ▸ hpF) (hb01 j).1 hjface hjσ hjF hdisj

/-- At a relative interior point of a wall facet there is a ball on which
Stokes holds for every complementary triangle containing that point in its
interior and whose vertices avoid the wall. The radius depends
only on the wall, facet and point, not on the triangle. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove_of_facet
    (σ : OrientedCell h 1) {F : Set V} (hF : IsExposed ℝ σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier))
    {p : V} (hp : p ∈ intrinsicInterior ℝ F) :
    ∃ ε > 0, ∀ s : Affine.Triangle ℝ V,
      p ∈ s.interior →
      IsCompl (vectorSpan ℝ F) (vectorSpan ℝ (range s.points)) →
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε →
      (∀ j, s.points j ∉ σ.carrier) →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex s.points) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) *
          σ.intersectionIndex (s.points ∘ m.succAbove) := by
  classical
  have := h.finiteDimensional
  have hpF := intrinsicInterior_subset hp
  have hne : F.Nonempty := ⟨p, hpF⟩
  let υ := σ.boundaryFacet hF hne hdim
  have hυ : υ ∈ σ.boundaryFacets := σ.boundaryFacet_mem_boundaryFacets hF hne hdim
  -- Every other facet misses this point; finitely many closed facets can be excluded at once.
  have hmiss (τ : OrientedCell h 2) (hτ : τ ∈ σ.boundaryFacets) (hneτ : τ ≠ υ) :
      p ∉ τ.carrier := by
    obtain ⟨G, hG, hGn, hGdim, heτ⟩ := (σ.mem_boundaryFacets τ).mp hτ
    have hτG : τ.carrier = G := by rw [heτ, boundaryFacet_carrier]
    rw [hτG]
    intro hpG
    have hsub : F ⊆ G := by
      have he := ((hF.inter hG).mono hF.subset inter_subset_left).eq_of_mem_intrinsicInterior
        ⟨hpF, hpG⟩ hp
      exact fun x hx => (he.symm ▸ hx).2
    have heFG : F = G := hF.eq_of_subset_of_finrank_add_one hne hdim hG hsub
      (by intro he; rw [he] at hGdim; omega)
    apply hneτ
    exact σ.carrier_injOn_boundaryFacets hτ hυ (by simp [hτG, υ, heFG])
  let U : Set V := ⋃ τ ∈ σ.boundaryFacets.erase υ, τ.carrier
  have hUclosed : IsClosed U := isClosed_biUnion_finset fun τ _ => τ.isClosed_carrier
  have hpU : p ∉ U := by
    intro hm
    obtain ⟨τ, hτ, hpτ⟩ := mem_iUnion₂.mp hm
    exact hmiss τ (Finset.mem_erase.mp hτ).2 (Finset.mem_erase.mp hτ).1 hpτ
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl p hpU
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  have hpoly : TauCeti.IsConvexPolyhedron σ.carrier := hP ▸ P.isConvexPolyhedron
  obtain ⟨l, δ, hδ, hFl, hlocal, -⟩ :=
    hpoly.exists_ball_inter_eq_halfspace_of_facet hF hdim hp
  refine ⟨min r δ, lt_min hr hδ, fun s hps hcompl hball hv => ?_⟩
  -- Inside the model ball the complementary slice is a ray and meets exactly one edge.
  have hsδ := hball.trans (Metric.ball_subset_ball (min_le_right r δ))
  have hmodel : convexHull ℝ (range s.points) ∩ σ.carrier =
      convexHull ℝ (range s.points) ∩ {z | z ∈ affineSpan ℝ σ.carrier ∧ l z ≤ l p} := by
    ext z
    have he := Set.ext_iff.mp hlocal z
    grind
  have hsign := σ.intersectionIndex_boundaryFacet_eq_sum_succAbove_of_halfspace
    hF hne hdim l hFl s hpF hps hcompl hv hmodel
  rw [← hsign]
  apply Finset.sum_eq_single_of_mem υ hυ
  intro τ hτ hneτ
  apply intersectionIndex_of_disjoint
  apply Set.disjoint_left.mpr
  intro z hz hzτ
  exact hrball (Metric.ball_subset_ball (min_le_left r δ) (hball hz))
    (mem_iUnion₂.mpr ⟨τ, Finset.mem_erase.mpr ⟨hneτ, hτ⟩, hzτ⟩)

end Mei.OrientedCell
