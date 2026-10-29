/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mei.Geometry.Affine.Generic

/-!
# Convex open sets minus obstacles of codimension two

In a finite-dimensional real normed space, removing from a nonempty convex open set any subset
of countably many affine subspaces of codimension at least two leaves a path-connected set.
Two remaining points are joined by two segments through a common vertex in the convex set;
`AffineSubspace.exists_mem_open_two_lineMaps_avoid_set` chooses the vertex so that both
segments avoid the obstacles. Mathlib's `isPathConnected_compl_of_one_lt_codim` is the case of
a single linear subspace and the whole space.
-/

public section

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Removing from a nonempty convex open set a subset of countably many affine subspaces of
codimension at least two leaves a path-connected set. -/
theorem Convex.isPathConnected_diff_of_subset_iUnion {K : Set V} (hK : Convex ℝ K)
    (hKo : IsOpen K) (hne : K.Nonempty) {κ : Type*} [Countable κ] (S : κ → AffineSubspace ℝ V)
    (hS : ∀ k, Module.finrank ℝ (S k).direction + 1 < Module.finrank ℝ V)
    {E : Set V} (hE : E ⊆ ⋃ k, (S k : Set V)) : IsPathConnected (K \ E) := by
  have hnotMem {x : V} (hx : ∀ k, x ∉ S k) : x ∉ E := fun hxE => by
    obtain ⟨k, hxk⟩ := mem_iUnion.mp (hE hxE)
    exact hx k hxk
  have hS' (k : κ) : S k ≠ ⊤ := fun htop => by
    have := hS k
    rw [htop, AffineSubspace.direction_top, finrank_top] at this
    omega
  obtain ⟨z, hzK, hz⟩ := AffineSubspace.exists_mem_open_genericLocus S hS' hKo hne
  refine isPathConnected_iff.mpr ⟨⟨z, hzK, hnotMem hz⟩, fun x hx y hy => ?_⟩
  obtain ⟨z, hzK, -, hz⟩ := AffineSubspace.exists_mem_open_two_lineMaps_avoid_set S hS
    (Empty.elim : Empty → AffineSubspace ℝ V) (fun i => i.elim) hE hx.2 hy.2 hKo hne
  have hjoin {p : V} (hp : p ∈ K) (hline : ∀ t : ℝ, AffineMap.lineMap p z t ∉ E) :
      JoinedIn (K \ E) p z := by
    refine JoinedIn.of_segment_subset fun q hq => ⟨hK.segment_subset hp hzK hq, ?_⟩
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨t, -, rfl⟩ := hq
    exact hline t
  exact (hjoin hx.1 fun t => (hz t).1).trans (hjoin hy.1 fun t => (hz t).2).symm
