/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mei.Geometry.Affine.Generic

/-!
# Convex sets with nonempty interior minus obstacles of codimension two

In a finite-dimensional real normed space, removing from a convex set with nonempty interior
any subset of countably many affine subspaces of codimension at least two leaves a
path-connected set.
Two remaining points are joined by two segments through a common vertex in the convex set;
`AffineSubspace.exists_mem_open_two_lineMaps_avoid_set` chooses the vertex so that both
segments avoid the obstacles. Mathlib's `isPathConnected_compl_of_one_lt_codim` is the case of
a single linear subspace and the whole space.

The resulting neighborhood criterion gives arbitrarily small preconnected neighborhoods
whose intersections with a subset are nonempty and preconnected, when its complement
is contained in the affine obstacles.
-/

public section

open Set TopologicalSpace Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Removing from a convex set with nonempty interior a subset of countably many affine subspaces of
codimension at least two leaves a path-connected set. -/
theorem Convex.isPathConnected_diff_of_subset_iUnion {K : Set V} (hK : Convex ℝ K)
    (hne : (interior K).Nonempty) {κ : Type*} [Countable κ] (S : κ → AffineSubspace ℝ V)
    (hS : ∀ k, Module.finrank ℝ (S k).direction + 1 < Module.finrank ℝ V)
    {E : Set V} (hE : E ⊆ ⋃ k, (S k : Set V)) : IsPathConnected (K \ E) := by
  have hnotMem {x : V} (hx : ∀ k, x ∉ S k) : x ∉ E := fun hxE => by
    obtain ⟨k, hxk⟩ := mem_iUnion.mp (hE hxE)
    exact hx k hxk
  have hS' (k : κ) : S k ≠ ⊤ := fun htop => by
    have := hS k
    rw [htop, AffineSubspace.direction_top, finrank_top] at this
    omega
  obtain ⟨z, hzK, hz⟩ := AffineSubspace.exists_mem_open_genericLocus S hS' isOpen_interior hne
  refine isPathConnected_iff.mpr ⟨⟨z, interior_subset hzK, hnotMem hz⟩, fun x hx y hy => ?_⟩
  obtain ⟨z, hzK, -, hz⟩ := AffineSubspace.exists_mem_open_two_lineMaps_avoid_set S hS
    (Empty.elim : Empty → AffineSubspace ℝ V) (fun i => i.elim) hE hx.2 hy.2 isOpen_interior hne
  have hjoin {p : V} (hp : p ∈ K) (hline : ∀ t : ℝ, AffineMap.lineMap p z t ∉ E) :
      JoinedIn (K \ E) p z := by
    refine JoinedIn.of_segment_subset fun q hq =>
      ⟨hK.segment_subset hp (interior_subset hzK) hq, ?_⟩
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨t, -, rfl⟩ := hq
    exact hline t
  exact (hjoin hx.1 fun t => (hz t).1).trans (hjoin hy.1 fun t => (hz t).2).symm

variable {S : Set V}

/-- If the points of `U` outside `O` lie in countably many affine subspaces of codimension at
least two, then every point of `U` has arbitrarily small preconnected open neighborhoods whose
intersections with `O` are nonempty and preconnected. -/
theorem IsOpen.exists_isPreconnected_inter_of_subset_iUnion (hS : IsOpen S)
    {κ : Type*} [Countable κ]
    (A : κ → AffineSubspace ℝ V)
    (hA : ∀ k, Module.finrank ℝ (A k).direction + 1 < Module.finrank ℝ V)
    {O : Set S} {U : Opens S} (hsing : ∀ x ∈ U, x ∉ O → ∃ k, (x : V) ∈ A k)
    {x : S} (hx : x ∈ U) {W : Set S} (hW : W ∈ 𝓝 x) :
    ∃ N : Opens S, x ∈ N ∧ (N : Set S) ⊆ W ∧
      IsPreconnected (N : Set S) ∧
        IsPreconnected ((N : Set S) ∩ O) ∧ ((N : Set S) ∩ O).Nonempty := by
  obtain ⟨w, hw, hwW⟩ := mem_nhds_subtype S x _ |>.mp
    (Filter.inter_mem hW (U.isOpen.mem_nhds hx))
  obtain ⟨r, hr, hrw⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hw (hS.mem_nhds x.2))
  let E : Set V := ⋃ k, (A k : Set V)
  let B : Set V := Metric.ball (x : V) r
  have hBS : B ⊆ S := fun p hp => (hrw hp).2
  have hval {T : Set V} (hT : T ⊆ B) : ((↑) : S → V) '' ((↑) ⁻¹' T) = T := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (hT.trans hBS)]
  have hinduc : IsInducing ((↑) : S → V) := IsInducing.subtypeVal
  let N : Opens S := ⟨(↑) ⁻¹' B, Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hNWU : (N : Set S) ⊆ W ∩ U := fun p hp => hwW (hrw hp).1
  -- The off-obstacle part of `N` is preconnected and dense in `N`.
  let D : Set S := (↑) ⁻¹' (B \ E)
  have hDpath : IsPathConnected (B \ E) := (convex_ball _ _).isPathConnected_diff_of_subset_iUnion
    (by simpa only [Metric.isOpen_ball.interior_eq] using Metric.nonempty_ball.mpr hr)
      A hA subset_rfl
  have hDconn : IsPreconnected D :=
    hinduc.isPreconnected_image.mp (by rw [hval sdiff_subset]; exact hDpath.isConnected.2)
  have hDO : D ⊆ (N : Set S) ∩ O := fun p hp => ⟨hp.1, by_contra fun hpO => by
    obtain ⟨k, hk⟩ := hsing p (hNWU hp.1).2 hpO
    exact hp.2 (mem_iUnion.mpr ⟨k, hk⟩)⟩
  have hA' (k : κ) : A k ≠ ⊤ := fun htop => by
    have := hA k
    rw [htop, AffineSubspace.direction_top, finrank_top] at this
    omega
  have hdense : Dense Eᶜ := by
    simpa only [E, AffineSubspace.genericLocus_eq_iInter, Set.compl_iUnion] using
      AffineSubspace.dense_genericLocus A hA'
  have hND : (N : Set S) ⊆ closure D := by
    rw [hinduc.closure_eq_preimage_closure_image, hval sdiff_subset]
    exact fun p hp => Metric.isOpen_ball.inter_closure (s := B) (t := Eᶜ) ⟨hp, hdense (p : V)⟩
  obtain ⟨p, hpB, hpE⟩ := hDpath.nonempty
  refine ⟨N, Metric.mem_ball_self hr, fun p hp => (hNWU hp).1, ?_,
    hDconn.subset_closure hDO fun p hp => hND hp.1, ⟨⟨p, hBS hpB⟩, hDO ⟨hpB, hpE⟩⟩⟩
  exact hinduc.isPreconnected_image.mp (by
    rw [Opens.coe_mk, hval subset_rfl]
    exact (convex_ball _ _).isPreconnected)
