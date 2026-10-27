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
assumed.

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
