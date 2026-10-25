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

section Algebra

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- An affine subspace whose direction has codimension one is proper. -/
theorem ne_top_of_finrank_direction_add_one_eq (A : AffineSubspace K V)
    (hdim : Module.finrank K A.direction + 1 = Module.finrank K V) : A ≠ ⊤ := by
  intro heq
  rw [heq, direction_top, finrank_top] at hdim
  omega

/-- Outside the span of an affine obstacle and an endpoint, every nonzero
parameter on the line from that endpoint avoids the obstacle. The endpoint
itself need not avoid the obstacle. -/
theorem lineMap_not_mem_of_not_mem_affineSpan_insert_of_ne_zero (S : AffineSubspace K V)
    {x z : V} (hz : z ∉ affineSpan K (insert x (S : Set V)))
    {t : K} (ht : t ≠ 0) : AffineMap.lineMap x z t ∉ S := by
  intro htS
  apply hz
  have hxspan : x ∈ affineSpan K (insert x (S : Set V)) :=
    subset_affineSpan K _ (mem_insert x _)
  have htspan : AffineMap.lineMap x z t ∈ affineSpan K (insert x (S : Set V)) :=
    subset_affineSpan K _ (mem_insert_of_mem x htS)
  simpa only [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ ht,
    AffineMap.lineMap_apply_one] using AffineMap.lineMap_mem t⁻¹ hxspan htspan

end Algebra

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
