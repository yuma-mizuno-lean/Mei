/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.Geometry.Convex.PolyhedralCochain.Coorientation
public import Mei.Geometry.Convex.PolyhedralCochain.Boundary
public import Mei.Geometry.Convex.Polyhedron.Path.Sum

/-!
# Local Stokes at the interior of a wall

Near a relative interior point, a wall agrees with its affine tangent hyperplane.
The intersection index of a segment is then the increase of the positive-side
indicator. Consequently the signed edge indices of a triangle sum to zero.
The triangle also misses every boundary facet, giving the Stokes equality in
this interior case. This includes degenerate triangles with vertices off the
tangent hyperplane.

The endpoint calculation reuses `WallComplement.crossingExponent_eq_side_sub`;
the local hyperplane description uses `OrientedCell.exists_integral_coorientation`
and `Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior`. Together with the
single-boundary-facet comparison, the interior case describes the local wall
contributions to polygonal meridian intersections.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- When a wall agrees with a cooriented hyperplane along a segment, its
intersection index is the increase of the positive-side indicator. The segment's
endpoints must miss the hyperplane. -/
theorem intersectionIndex_eq_sub_side (σ : OrientedCell h 1)
    (ν : V →ₗ[ℝ] ℝ) (b : ℝ) {x y : V} (hx : ν x ≠ b) (hy : ν y ≠ b)
    (hν : ∀ w, SignType.sign (ν w) = σ.orientation.evalSign (fun _ : Fin 1 => w))
    (hlocal : segment ℝ x y ∩ σ.carrier = segment ℝ x y ∩ {z | ν z = b}) :
    σ.intersectionIndex ![x, y] =
      (if b < ν y then 1 else 0 : ℤ) - (if b < ν x then 1 else 0) := by
  classical
  let W : Unit → Set V := fun _ => {z | ν z = b}
  let a : WallComplement W := ⟨x, fun _ => hx⟩
  let c : WallComplement W := ⟨y, fun _ => hy⟩
  have hc := WallComplement.crossingExponent_eq_side_sub a c ν b () rfl
  dsimp only [a, c] at hc
  have hm : (convexHull ℝ (range ![x, y]) ∩ σ.carrier).Nonempty ↔
      ∃ t, ((), t) ∈ WallComplement.crossings a c := by
    rw [Matrix.range_cons_cons_empty, convexHull_pair, hlocal, segment_eq_image_lineMap]
    simp only [WallComplement.mem_crossings]
    exact Set.image_inter_nonempty_iff
  have hframe : (fun j : Fin 1 => ![x, y] j.succ - ![x, y] 0) =
      fun _ : Fin 1 => y - x := by ext j; fin_cases j; rfl
  by_cases hmeet : (convexHull ℝ (range ![x, y]) ∩ σ.carrier).Nonempty
  · rw [intersectionIndex_of_nonempty hmeet, hframe, ← hν]
    rw [ite_eq_left (hm.mp hmeet)] at hc
    have hn : ν y - ν x ≠ 0 := by
      intro he
      have ht := hm.mp hmeet
      obtain ⟨t, ht⟩ := ht
      have htb := ((WallComplement.mem_crossings a c () t).mp ht).2
      simp only [W, mem_ofPred_eq, a, c, AffineMap.lineMap_apply_module',
        map_add, map_smul, map_sub, smul_eq_mul] at htb
      exact hx (by simpa only [he, mul_zero, zero_add] using htb)
    rw [map_sub]
    rcases lt_or_gt_of_ne hn with hn | hn
    · simp only [sign_neg hn, SignType.coe_neg_one]
      simp only [map_sub, ite_eq_right (by linarith : ¬0 < ν y - ν x)] at hc
      omega
    · simp only [sign_pos hn, SignType.coe_one]
      simp only [map_sub, ite_eq_left hn] at hc
      omega
  · rw [intersectionIndex_of_disjoint
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))]
    rw [ite_eq_right (hm.not.mp hmeet)] at hc
    omega

/-- The signed edge indices of a triangle cancel when the wall agrees with
one cooriented hyperplane throughout the triangle. Vertices miss that plane;
no affine independence of the triangle is required. -/
theorem sum_intersectionIndex_triangle_eq_zero (σ : OrientedCell h 1)
    (ν : V →ₗ[ℝ] ℝ) (b : ℝ) (v : Fin 3 → V)
    (hv : ∀ j, ν (v j) ≠ b)
    (hν : ∀ w, SignType.sign (ν w) = σ.orientation.evalSign (fun _ : Fin 1 => w))
    (hlocal : convexHull ℝ (range v) ∩ σ.carrier =
      convexHull ℝ (range v) ∩ {z | ν z = b}) :
    ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (v ∘ m.succAbove) = 0 := by
  have hedge (a c : Fin 3) : segment ℝ (v a) (v c) ∩ σ.carrier =
      segment ℝ (v a) (v c) ∩ {z | ν z = b} := by
    have hs : segment ℝ (v a) (v c) ⊆ convexHull ℝ (range v) :=
      (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (mem_range_self a))
        (subset_convexHull ℝ _ (mem_range_self c))
    ext z
    have he := Set.ext_iff.mp hlocal z
    grind
  have he (a c : Fin 3) := σ.intersectionIndex_eq_sub_side ν b (hv a) (hv c) hν (hedge a c)
  have hface (m : Fin 3) : v ∘ m.succAbove = ![v (m.succAbove 0), v (m.succAbove 1)] := by
    ext j
    fin_cases j <;> rfl
  simp only [Fin.sum_univ_three, hface]
  rw [he, he, he]
  norm_num [Fin.succAbove]

/-- At a relative interior point of a wall there is a ball on which the
Stokes formula holds for every triangle whose vertices miss the tangent
hyperplane. Both sides are zero: the signed edge intersections cancel and
the triangle misses all boundary facets. -/
theorem exists_ball_sum_intersectionIndex_boundaryFacets_eq_sum_succAbove
    (σ : OrientedCell h 1) {q : V} (hq : q ∈ intrinsicInterior ℝ σ.carrier) :
    ∃ ε > 0, ∀ v : Fin 3 → V,
      convexHull ℝ (range v) ⊆ Metric.ball q ε →
      (∀ j, v j ∉ affineSpan ℝ σ.carrier) →
      (∑ τ ∈ σ.boundaryFacets, τ.intersectionIndex v) =
        ∑ m : Fin 3, (-1 : ℤ) ^ (m : ℕ) * σ.intersectionIndex (v ∘ m.succAbove) := by
  have := h.finiteDimensional
  obtain ⟨ν, -, hker, hsign⟩ := σ.exists_integral_coorientation
  let f := h.realCharacter ν
  have hqA : q ∈ affineSpan ℝ σ.carrier := subset_affineSpan ℝ _ (intrinsicInterior_subset hq)
  have hplane (z : V) : z ∈ affineSpan ℝ σ.carrier ↔ f z = f q := by
    rw [← (affineSpan ℝ σ.carrier).mk'_eq hqA, AffineSubspace.mem_mk', ← hker,
      LinearMap.mem_ker]
    simp only [f, vsub_eq_sub, map_sub, sub_eq_zero]
  have hfront : q ∉ intrinsicFrontier ℝ σ.carrier := by
    rw [← intrinsicClosure_sdiff_intrinsicFrontier] at hq
    exact hq.2
  have hfclosed : IsClosed (intrinsicFrontier ℝ σ.carrier) :=
    isClosed_intrinsicFrontier (affineSpan ℝ σ.carrier).closed_of_finiteDimensional
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hfclosed.isOpen_compl q hfront
  have hmem := Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hq
  obtain ⟨δ, hδ, hδmem⟩ := Metric.mem_nhdsWithin_iff.mp hmem
  refine ⟨min ε δ, lt_min hε hδ, fun v hv hvA => ?_⟩
  have hlocal : convexHull ℝ (range v) ∩ σ.carrier =
      convexHull ℝ (range v) ∩ {z | f z = f q} := by
    ext z
    constructor
    · rintro ⟨hz, hzσ⟩
      exact ⟨hz, (hplane z).mp (subset_affineSpan ℝ _ hzσ)⟩
    · rintro ⟨hz, hzplane⟩
      exact ⟨hz, hδmem ⟨Metric.ball_subset_ball (min_le_right _ _) (hv hz),
        (hplane z).mpr hzplane⟩⟩
  rw [σ.sum_intersectionIndex_triangle_eq_zero f (f q) v
    (fun j he => hvA j ((hplane _).mpr he)) hsign hlocal]
  apply Finset.sum_eq_zero
  intro τ hτ
  apply intersectionIndex_of_disjoint
  apply Set.disjoint_left.mpr
  intro z hz hzτ
  have hzfr : z ∈ intrinsicFrontier ℝ σ.carrier := by
    rw [σ.intrinsicFrontier_eq_biUnion_boundaryFacets]
    exact mem_iUnion₂.mpr ⟨τ, hτ, hzτ⟩
  exact hball (Metric.ball_subset_ball (min_le_left _ _) (hv hz)) hzfr

end Mei.OrientedCell
