/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Topology.Sheaves.LocallyConstant.Extension
public import Mei.Analysis.Convex.PathConnected

/-!
# Facet descent for locally constant sheaves

Let `S` be an open subset of a finite-dimensional real normed space and `F` a sheaf of types
on `S` with bijective restrictions to nonempty preconnected subopens of small neighborhoods.
Consider opens `G ≤ O ≤ U` of `S`: `G` is the union of the top strata, dense in `O`; the points
of `O` outside `G` are the facets; and the points of `U` outside `O` lie in countably many affine
subspaces of codimension at least two. For a locally finite polyhedral stratification, the
codimension-two strata lie in their countably many affine spans.

A section of `F` on the top strata then extends to `U` exactly when it extends across each
facet, that is, to some neighborhood of each facet point. The extension is unique. Across the
facets this is the sheaf gluing of `TopCat.Sheaf.existsUnique_extension_of_subset_closure`.
Across codimension two, small balls stay preconnected after deleting the obstacles, by
`Convex.isPathConnected_diff_of_subset_iUnion`, so sections extend by
`TopCat.Sheaf.map_bijective_of_isPreconnected_inter`.

This is the descent step used to obtain theta functions as global sections from their
chamber values and facet equations; compare Gross–Hacking–Siebert, *Theta functions on
varieties with effective anti-canonical class*, §3.2 (arXiv:1601.07081v4).
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology Set

universe u v

namespace TopCat.Sheaf

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {S : Set V} (F : (TopCat.of S).Sheaf (Type v)) [F.HasLocallyBijectivePreconnectedRestrictions]

/-- If the points of `U` outside `O` lie in countably many affine subspaces of codimension at
least two, then every point of `U` has arbitrarily small preconnected open neighborhoods whose
intersections with `O` are nonempty and preconnected. -/
private theorem exists_isPreconnected_inter (hS : IsOpen S) {κ : Type*} [Countable κ]
    (A : κ → AffineSubspace ℝ V)
    (hA : ∀ k, Module.finrank ℝ (A k).direction + 1 < Module.finrank ℝ V)
    {O U : Opens (TopCat.of S)} (hsing : ∀ x ∈ U, x ∉ O → ∃ k, (x : V) ∈ A k)
    {x : TopCat.of S} (hx : x ∈ U) {W : Set (TopCat.of S)} (hW : W ∈ 𝓝 x) :
    ∃ N : Opens (TopCat.of S), x ∈ N ∧ (N : Set (TopCat.of S)) ⊆ W ∧
      IsPreconnected (N : Set (TopCat.of S)) ∧
        IsPreconnected ((N : Set (TopCat.of S)) ∩ O) ∧ ((N : Set (TopCat.of S)) ∩ O).Nonempty := by
  obtain ⟨w, hw, hwW⟩ := mem_nhds_subtype S x _ |>.mp
    (Filter.inter_mem hW (U.isOpen.mem_nhds hx))
  obtain ⟨r, hr, hrw⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hw (hS.mem_nhds x.2))
  let E : Set V := ⋃ k, (A k : Set V)
  let B : Set V := Metric.ball (x : V) r
  have hBS : B ⊆ S := fun p hp => (hrw hp).2
  have hval {T : Set V} (hT : T ⊆ B) : ((↑) : S → V) '' ((↑) ⁻¹' T) = T := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr (hT.trans hBS)]
  have hinduc : IsInducing ((↑) : S → V) := IsInducing.subtypeVal
  let N : Opens (TopCat.of S) := ⟨(↑) ⁻¹' B, Metric.isOpen_ball.preimage continuous_subtype_val⟩
  have hNWU : (N : Set (TopCat.of S)) ⊆ W ∩ U := fun p hp => hwW (hrw hp).1
  -- The off-obstacle part of `N` is preconnected and dense in `N`.
  let D : Set (TopCat.of S) := (↑) ⁻¹' (B \ E)
  have hDpath : IsPathConnected (B \ E) := (convex_ball _ _).isPathConnected_diff_of_subset_iUnion
    Metric.isOpen_ball (Metric.nonempty_ball.mpr hr) A hA subset_rfl
  have hDconn : IsPreconnected D :=
    hinduc.isPreconnected_image.mp (by rw [hval sdiff_subset]; exact hDpath.isConnected.2)
  have hDO : D ⊆ (N : Set (TopCat.of S)) ∩ O := fun p hp => ⟨hp.1, by_contra fun hpO => by
    obtain ⟨k, hk⟩ := hsing p (hNWU hp.1).2 hpO
    exact hp.2 (mem_iUnion.mpr ⟨k, hk⟩)⟩
  have hND : (N : Set (TopCat.of S)) ⊆ closure D := fun p hp => by
    -- Every small ball around a point of `N` still meets `B` off the obstacles.
    refine closure_subtype.mpr (Metric.mem_closure_iff.mpr fun ε hε => ?_)
    have hpath := Convex.isPathConnected_diff_of_subset_iUnion
      ((convex_ball (p : V) ε).inter (convex_ball (x : V) r))
      (Metric.isOpen_ball.inter Metric.isOpen_ball) ⟨p, Metric.mem_ball_self hε, hp⟩ A hA
      subset_rfl
    obtain ⟨q, ⟨hqε, hqB⟩, hqE⟩ := hpath.nonempty
    rw [hval sdiff_subset]
    exact ⟨q, ⟨hqB, hqE⟩, by rw [dist_comm]; exact hqε⟩
  obtain ⟨p, hpB, hpE⟩ := hDpath.nonempty
  refine ⟨N, Metric.mem_ball_self hr, fun p hp => (hNWU hp).1, ?_,
    hDconn.subset_closure hDO fun p hp => hND hp.1, ⟨⟨p, hBS hpB⟩, hDO ⟨hpB, hpE⟩⟩⟩
  exact hinduc.isPreconnected_image.mp (by
    rw [Opens.coe_mk, hval subset_rfl]
    exact (convex_ball _ _).isPreconnected)

/-- **Facet descent.** Let `G ≤ O ≤ U` be opens of an open subset `S` of a finite-dimensional
real normed space, with `G` dense in `O` and the points of `U` outside `O` contained in countably
many affine subspaces of codimension at least two. A section `s` of `F` on `G` extends uniquely to
`U`, provided it extends to a neighborhood of every point of `O` outside `G`.

For a stratification, `G` is the union of the top strata and the points of `O` outside `G` are
the facets; the condition at a facet point says that the continuations of `s` from the two
adjacent chambers agree. -/
theorem existsUnique_extension_of_facets (hS : IsOpen S) {κ : Type*} [Countable κ]
    (A : κ → AffineSubspace ℝ V)
    (hA : ∀ k, Module.finrank ℝ (A k).direction + 1 < Module.finrank ℝ V)
    {G O U : Opens (TopCat.of S)} (hGO : G ≤ O) (hOU : O ≤ U)
    (hdense : (O : Set (TopCat.of S)) ⊆ closure (G : Set (TopCat.of S)))
    (hsing : ∀ x ∈ U, x ∉ O → ∃ k, (x : V) ∈ A k) (s : F.presheaf.obj (op G))
    (hfacet : ∀ x ∈ O, x ∉ G → ∃ (N : Opens (TopCat.of S)) (t : F.presheaf.obj (op N)), x ∈ N ∧
      F.presheaf.map (homOfLE (inf_le_left : N ⊓ G ≤ N)).op t =
        F.presheaf.map (homOfLE (inf_le_right : N ⊓ G ≤ G)).op s) :
    ∃! u : F.presheaf.obj (op U), F.presheaf.map (homOfLE (hGO.trans hOU)).op u = s := by
  have : LocallyConnectedSpace (TopCat.of S) := hS.locallyConnectedSpace
  obtain ⟨u', hu', huniq'⟩ := F.existsUnique_extension_of_subset_closure hGO hdense s
    fun x hx => by
      by_cases hxG : x ∈ G
      · exact ⟨G, s, hxG, rfl⟩
      · exact hfacet x hx hxG
  have hbij := F.map_bijective_of_isPreconnected_inter hOU fun x hx W hW =>
    exists_isPreconnected_inter hS A hA hsing hx hW
  have hcomp (w : F.presheaf.obj (op U)) :
      F.presheaf.map (homOfLE hGO).op (F.presheaf.map (homOfLE hOU).op w) =
        F.presheaf.map (homOfLE (hGO.trans hOU)).op w := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  obtain ⟨u, rfl⟩ := hbij.surjective u'
  refine ⟨u, (hcomp u).symm.trans hu', fun u₁ hu₁ => ?_⟩
  exact hbij.injective (huniq' _ ((hcomp u₁).trans hu₁))

end TopCat.Sheaf
