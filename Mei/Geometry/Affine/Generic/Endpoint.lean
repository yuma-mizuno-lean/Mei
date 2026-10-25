/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Generic

/-!
# Avoiding a covered set while fixing allowed endpoints

An endpoint may belong to an affine subspace used to cover the bad set while
remaining outside the bad set itself. Excluding the span of that subspace and
the endpoint prevents every nonzero line parameter from meeting the subspace.
The zero parameter is handled by the actual endpoint condition.
-/

public section

open Set

namespace AffineSubspace

section Normed

variable {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Countable ι] [Countable κ]

/-- A set covered by countably many affine subspaces of codimension at least
two can be avoided by both full lines from two fixed allowed endpoints to a
vertex in any nonempty open set. The vertex may simultaneously avoid any
additional countable family of proper affine subspaces.

The endpoints are required to avoid the actual set only; they may lie in its
affine cover. The prescribed open set constrains the vertex, not the lines. -/
theorem exists_mem_open_two_lineMaps_avoid_set
    (S : κ → AffineSubspace ℝ V)
    (hS : ∀ k, Module.finrank ℝ (S k).direction + 1 < Module.finrank ℝ V)
    (A : ι → AffineSubspace ℝ V) (hA : ∀ i, A i ≠ ⊤)
    {E : Set V} (hE : E ⊆ ⋃ k, (S k : Set V))
    {x y : V} (hx : x ∉ E) (hy : y ∉ E)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ i, z ∉ A i) ∧ ∀ t : ℝ,
      AffineMap.lineMap x z t ∉ E ∧ AffineMap.lineMap y z t ∉ E := by
  let B : (κ ⊕ κ) ⊕ ι → AffineSubspace ℝ V := Sum.elim
    (Sum.elim (fun k => affineSpan ℝ (insert x (S k : Set V)))
      (fun k => affineSpan ℝ (insert y (S k : Set V)))) A
  have hB : ∀ i, B i ≠ ⊤ := by
    intro i
    rcases i with k | i
    · rcases k with k | k
      · exact (S k).affineSpan_insert_ne_top_of_finrank (hS k) x
      · exact (S k).affineSpan_insert_ne_top_of_finrank (hS k) y
    · exact hA i
  obtain ⟨z, hzU, hz⟩ := exists_mem_open_genericLocus B hB hU hne
  have havoid (p : V) (hp : p ∉ E)
      (hzp : ∀ k, z ∉ affineSpan ℝ (insert p (S k : Set V))) (t : ℝ) :
      AffineMap.lineMap p z t ∉ E := by
    by_cases ht : t = 0
    · simpa [ht] using hp
    · intro htE
      obtain ⟨k, htk⟩ := Set.mem_iUnion.mp (hE htE)
      exact (S k).lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero (hzp k) ht htk
  exact ⟨z, hzU, fun i => hz (.inr i), fun t =>
    ⟨havoid x hx (fun k => hz (.inl (.inl k))) t,
      havoid y hy (fun k => hz (.inl (.inr k))) t⟩⟩

end Normed

end AffineSubspace
