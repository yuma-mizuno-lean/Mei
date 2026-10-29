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

open TopCat.Presheaf (restrict_restrict)

universe u v

namespace TopCat.Sheaf

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {S : Set V} (F : (TopCat.of S).Sheaf (Type v)) [F.HasLocallyBijectivePreconnectedRestrictions]

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
    hS.exists_isPreconnected_inter_of_subset_iUnion A hA hsing hx hW
  obtain ⟨u, rfl⟩ := hbij.surjective u'
  refine ⟨u, (restrict_restrict (CC := fun T => T) (F := F.presheaf) hGO hOU u).symm.trans hu',
    fun u₁ hu₁ => ?_⟩
  exact hbij.injective (huniq' _
    ((restrict_restrict (CC := fun T => T) (F := F.presheaf) hGO hOU u₁).trans hu₁))

end TopCat.Sheaf
