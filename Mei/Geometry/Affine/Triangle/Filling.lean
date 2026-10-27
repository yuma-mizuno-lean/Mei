/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Hull

/-!
# Triangle fillings avoiding affine obstacles

Choose one cone vertex for countably many fixed edges so that their filled
triangles avoid countably many obstacles of codimension at least three.
The edges need only avoid the obstacles themselves, rather than their affine
spans. The cone vertex may be chosen in any nonempty open set and can
simultaneously avoid additional proper affine subspaces.

For each edge and obstacle, the exceptional apex positions lie in their
joint affine span. Its dimension is at most the obstacle dimension plus two.
The choice uses `AffineSubspace.exists_mem_open_genericLocus`; disjointness
uses `Disjoint.convexHull_insert_of_notMem_affineSpan`.
-/

public section

open Set Module

namespace Mei

variable {V ι κ μ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι] [Countable κ] [Countable μ]

/-- Choose a common apex for fixed edges whose filled triangles avoid all
specified obstacles of codimension at least three. Only the actual obstacles
must miss the base segments; their affine spans may meet those segments.
Additional proper affine exceptions may be imposed on the apex. -/
theorem exists_mem_open_triangle_fillings_avoid
    (x y : ι → V) (S : κ → Set V)
    (hdim : ∀ j, finrank ℝ (affineSpan ℝ (S j)).direction + 2 < finrank ℝ V)
    (hbase : ∀ a j, Disjoint (segment ℝ (x a) (y a)) (S j))
    (A : μ → AffineSubspace ℝ V) (hA : ∀ j, A j ≠ ⊤)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ j, z ∉ A j) ∧
      ∀ a j, Disjoint (convexHull ℝ {z, x a, y a}) (S j) := by
  let B : (ι × κ) ⊕ μ → AffineSubspace ℝ V := Sum.elim
    (fun a => affineSpan ℝ ({x a.1, y a.1} ∪ S a.2)) A
  have hB : ∀ a, B a ≠ ⊤ := by
    rintro (⟨a, j⟩ | j)
    · have he : affineSpan ℝ ({x a, y a} ∪ S j) =
          affineSpan ℝ ({x a, y a} ∪ (affineSpan ℝ (S j) : Set V)) := by
        simp only [AffineSubspace.span_union, AffineSubspace.affineSpan_coe]
      dsimp only [B, Sum.elim_inl]
      rw [he]
      exact (affineSpan ℝ (S j)).affineSpan_pair_union_ne_top_of_finrank (hdim j) _ _
    · exact hA j
  obtain ⟨z, hzU, hz⟩ := AffineSubspace.exists_mem_open_genericLocus B hB hU hne
  refine ⟨z, hzU, fun j => hz (.inr j), fun a j => ?_⟩
  have hb : Disjoint (convexHull ℝ {x a, y a}) (S j) := by
    simpa only [convexHull_pair] using hbase a j
  exact hb.convexHull_insert_of_notMem_affineSpan (hz (.inl (a, j)))

end Mei
