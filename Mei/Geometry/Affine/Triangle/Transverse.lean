/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Hull
public import Mei.LinearAlgebra.FiniteDimensional

/-!
# Cone fillings transverse to codimension-two obstacles

For fixed segments missing countably many codimension-two sets, choose one
apex such that every filled triangle either misses an obstacle or spans a
plane complementary to its affine direction. The apex can lie in any
nonempty open set and avoid additional proper affine subspaces.

This gives isolated transverse intersections with joints in polygonal
fillings. A segment tangent to an obstacle's direction need not admit a
complementary filling plane; in that case its entire filled triangle avoids
the obstacle. No transversality of the original edges to the obstacles is
assumed. Conversely, if the plane of a filled triangle is not complementary to a
codimension-two direction, every translate of that direction meeting the filled
triangle meets one of its edges. This is the exchange step of Carathéodory's
theorem, performed modulo the direction.

The construction uses `AffineSubspace.exists_mem_open_genericLocus`,
`Disjoint.convexHull_insert_of_notMem_affineSpan`, and
`Submodule.isCompl_span_pair_of_notMem`.
-/

public section

open Set Module

namespace Mei

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The exceptional apex positions for one fixed edge and one codimension-two
obstacle lie in a proper affine subspace. Outside it the filled triangle misses
the obstacle or has complementary direction. -/
theorem exists_affineSubspace_triangle_filling_transverse (x y : V) (S : Set V)
    (hdim : finrank K (affineSpan K S).direction + 2 = finrank K V)
    (hbase : Disjoint (segment K x y) S) :
    ∃ B : AffineSubspace K V, B ≠ ⊤ ∧ ∀ z ∉ B,
      Disjoint (convexHull K {z, x, y}) S ∨
        IsCompl (affineSpan K S).direction (vectorSpan K {z, x, y}) := by
  by_cases hv : y - x ∈ (affineSpan K S).direction
  · -- For a tangent edge, exclude the span of the obstacle and the edge.
    let B := affineSpan K (insert x S)
    have hB : B ≠ ⊤ := by
      simpa only [B, affineSpan_insert_affineSpan] using
        (affineSpan K S).affineSpan_insert_ne_top_of_finrank (by omega) x
    have hx : x ∈ B := subset_affineSpan K _ (mem_insert _ _)
    have hdir : (affineSpan K S).direction ≤ B.direction :=
      AffineSubspace.direction_le (affineSpan_mono K (subset_insert _ _))
    have hy : y ∈ B := by
      simpa only [vadd_eq_add, sub_add_cancel] using
        AffineSubspace.vadd_mem_of_mem_direction (hdir hv) hx
    have hle : affineSpan K ({x, y} ∪ S) ≤ B := by
      apply affineSpan_le.mpr
      rintro w (hw | hw)
      · rcases hw with rfl | hw
        · exact hx
        · exact (mem_singleton_iff.mp hw) ▸ hy
      · exact subset_affineSpan K _ (mem_insert_of_mem _ hw)
    refine ⟨B, hB, fun z hz => Or.inl ?_⟩
    have hb : Disjoint (convexHull K {x, y}) S := by
      simpa only [convexHull_pair] using hbase
    exact hb.convexHull_insert_of_notMem_affineSpan (fun hw => hz (hle hw))
  · -- Otherwise, one further vector outside this hyperplane completes the normal plane.
    let B := AffineSubspace.mk' x ((affineSpan K S).direction ⊔ K ∙ (y - x))
    have hB : B ≠ ⊤ := by
      intro he
      have hd := Submodule.finrank_sup_span_singleton hv
      have ht := congrArg AffineSubspace.direction he
      rw [AffineSubspace.direction_mk', AffineSubspace.direction_top] at ht
      rw [ht, finrank_top] at hd
      omega
    refine ⟨B, hB, fun z hz => Or.inr ?_⟩
    have hw : z - x ∉ (affineSpan K S).direction ⊔ K ∙ (y - x) := by
      simpa only [B, AffineSubspace.mem_mk', vsub_eq_sub] using hz
    have hspan : vectorSpan K {z, x, y} = Submodule.span K {y - x, z - x} := by
      rw [vectorSpan_eq_span_vsub_set_right K (by simp : x ∈ ({z, x, y} : Set V))]
      simp [Submodule.span_insert, sup_comm]
    rw [hspan]
    exact Submodule.isCompl_span_pair_of_notMem _ hdim hv hw

/-- If the plane of a filled triangle is not complementary to a codimension-two
direction `W`, every translate of `W` meeting the filled triangle also meets one of
its three edges. Degenerate triangles are included. -/
theorem exists_mem_segment_sub_mem_of_not_isCompl {W : Submodule K V}
    (hdim : finrank K W + 2 = finrank K V) {x y z w : V}
    (hw : w ∈ convexHull K {x, y, z}) (hW : ¬ IsCompl W (vectorSpan K {x, y, z})) :
    ∃ u, (u ∈ segment K x y ∨ u ∈ segment K y z ∨ u ∈ segment K z x) ∧ u - w ∈ W := by
  classical
  -- A nonzero barycentric direction of total weight zero moves the triangle along `W`.
  obtain ⟨μ, hμ, hμsum, hμW⟩ : ∃ μ : Fin 3 → K, μ ≠ 0 ∧ ∑ j, μ j = 0 ∧
      ∑ j, μ j • ![x, y, z] j ∈ W := by
    by_cases hv : y - x ∈ W
    · refine ⟨![-1, 1, 0], by simp [funext_iff, Fin.forall_fin_succ], by simp [Fin.sum_univ_three],
        ?_⟩
      simpa [Fin.sum_univ_three, neg_add_eq_sub] using hv
    by_cases hz : z - x ∈ W ⊔ K ∙ (y - x)
    · obtain ⟨d, hd, e, he, hde⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp he
      refine ⟨![c - 1, -c, 1], by simp [funext_iff, Fin.forall_fin_succ],
        by simp [Fin.sum_univ_three]; ring, ?_⟩
      convert hd using 1
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [eq_sub_iff_add_eq.mpr hde]
      module
    · have hspan : vectorSpan K {x, y, z} = Submodule.span K {y - x, z - x} := by
        rw [vectorSpan_eq_span_vsub_set_right K (by simp : x ∈ ({x, y, z} : Set V))]
        simp [Submodule.span_insert]
      exact (hW (hspan ▸ Submodule.isCompl_span_pair_of_notMem W hdim hv hz)).elim
  -- Barycentric coordinates of the given point.
  obtain ⟨l, hl0, hlsum, hlw⟩ : ∃ l : Fin 3 → K, (∀ j, 0 ≤ l j) ∧ ∑ j, l j = 1 ∧
      ∑ j, l j • ![x, y, z] j = w := by
    rw [convexHull_insert (by simp), mem_convexJoin] at hw
    obtain ⟨_, rfl, v, hv, a, b, ha, hb, hab, rfl⟩ := hw
    rw [convexHull_pair] at hv
    obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hv
    refine ⟨![a, b * c, b * d], ?_, ?_, ?_⟩
    · simp [Fin.forall_fin_succ, ha, mul_nonneg hb hc, mul_nonneg hb hd]
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      linear_combination hab + b * hcd
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      module
  -- Move along that direction until the first coordinate vanishes.
  have hneg : (Finset.univ.filter fun j => μ j < 0).Nonempty := by
    by_contra hne
    simp only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_lt] at hne
    apply hμ
    funext j
    have := Finset.single_le_sum (fun i _ => hne (x := i)) (Finset.mem_univ j)
    rw [hμsum] at this
    exact le_antisymm this (hne (x := j))
  obtain ⟨j₀, hj₀, hmin⟩ := (Finset.univ.filter fun j => μ j < 0).exists_min_image
    (fun j => l j / -μ j) hneg
  have hμj₀ : μ j₀ < 0 := (Finset.mem_filter.mp hj₀).2
  set τ := l j₀ / -μ j₀ with hτ
  have hτ0 : 0 ≤ τ := div_nonneg (hl0 j₀) (by linarith)
  let κ : Fin 3 → K := fun j => l j + τ * μ j
  have hκ0 (j : Fin 3) : 0 ≤ κ j := by
    by_cases hj : μ j < 0
    · have := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      rw [le_div_iff₀ (by linarith)] at this
      simp only [κ]
      linarith
    · exact add_nonneg (hl0 j) (mul_nonneg hτ0 (le_of_not_gt hj))
  have hκj₀ : κ j₀ = 0 := by
    simp only [κ, hτ]
    field_simp [hμj₀.ne]
    ring
  have hκsum : ∑ j, κ j = 1 := by
    simp only [κ, Finset.sum_add_distrib, ← Finset.mul_sum, hμsum, mul_zero, add_zero, hlsum]
  refine ⟨∑ j, κ j • ![x, y, z] j, ?_, ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hκsum ⊢
    fin_cases j₀ <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hκj₀
    · refine Or.inr (Or.inl ⟨κ 1, κ 2, hκ0 1, hκ0 2, by linarith, ?_⟩)
      rw [hκj₀, zero_smul, zero_add]
    · refine Or.inr (Or.inr ⟨κ 2, κ 0, hκ0 2, hκ0 0, by linarith, ?_⟩)
      rw [hκj₀, zero_smul, add_zero, add_comm]
    · refine Or.inl ⟨κ 0, κ 1, hκ0 0, hκ0 1, by linarith, ?_⟩
      rw [hκj₀, zero_smul, add_zero]
  · have heq : ∑ j, κ j • ![x, y, z] j - w = τ • ∑ j, μ j • ![x, y, z] j := by
      rw [← hlw]
      simp only [κ, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum]
      abel
    rw [heq]
    exact W.smul_mem τ hμW

end Mei

namespace Mei

variable {V ι κ μ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι] [Countable κ] [Countable μ]

/-- A common apex makes each triangle disjoint from, or complementary to, each
codimension-two obstacle. The base segments are fixed and need only avoid the
actual obstacles, which need not be convex or closed. -/
theorem exists_mem_open_triangle_fillings_transverse
    (x y : ι → V) (S : κ → Set V)
    (hdim : ∀ j, finrank ℝ (affineSpan ℝ (S j)).direction + 2 = finrank ℝ V)
    (hbase : ∀ a j, Disjoint (segment ℝ (x a) (y a)) (S j))
    (A : μ → AffineSubspace ℝ V) (hA : ∀ j, A j ≠ ⊤)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ j, z ∉ A j) ∧ ∀ a j,
      Disjoint (convexHull ℝ {z, x a, y a}) (S j) ∨
        IsCompl (affineSpan ℝ (S j)).direction (vectorSpan ℝ {z, x a, y a}) := by
  choose B hB htrans using fun aj : ι × κ =>
    exists_affineSubspace_triangle_filling_transverse
      (x aj.1) (y aj.1) (S aj.2) (hdim aj.2) (hbase aj.1 aj.2)
  obtain ⟨z, hzU, hz⟩ := AffineSubspace.exists_mem_open_genericLocus
    (Sum.elim B A) (by
      rintro (aj | j)
      · exact hB aj
      · exact hA j) hU hne
  exact ⟨z, hzU, fun j => hz (.inr j), fun a j => htrans (a, j) z (hz (.inl (a, j)))⟩

end Mei
