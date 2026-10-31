/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Sheaves.LocallyConstant.FacetDescent.Basic

/-!
# Facet descent for morphisms into sheaf sections

Local data may be morphisms from a fixed object rather than individual elements.
If restrictions of a category-valued sheaf are locally isomorphisms on nonempty
preconnected opens, morphisms from any object extend uniquely across facets and
codimension-two obstacles under the usual facet conditions.

For semimodule-valued sheaves, this extends linear maps from an incoming semimodule.
A finite sum of branch maps is one such map, and only its total needs to satisfy
the facet condition. There is no need to extend each branch separately. Arbitrary
semirings and semimodules without additive inverses are included.

We use Mathlib's `CategoryTheory.sheafOver`, the sheaf of morphisms from a fixed
object, and apply the existing Type-valued facet descent theorem to it. The
geometric inputs are those of `TopCat.Sheaf.existsUnique_extension_of_facets`.
-/

public section

open CategoryTheory TopologicalSpace Opposite Topology Set

universe u v w

namespace TopCat.Sheaf

variable {C : Type w} [Category.{v} C]

section Facets

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {S : Set V} (F : (TopCat.of S).Sheaf C)
  (hF : ∀ x : TopCat.of S, ∃ W : Opens (TopCat.of S), x ∈ W ∧
    ∀ (B : Opens (TopCat.of S)) (hBW : B ≤ W),
      (B : Set (TopCat.of S)).Nonempty → IsPreconnected (B : Set (TopCat.of S)) →
        IsIso (F.obj.map (homOfLE hBW).op))

include hF in
/-- A morphism to sections on the dense top-stratum open extends uniquely when
it extends locally across each facet. Applied in `SemimoduleCat R`, the extension
is a linear map, so incoming coefficients vary linearly. The local facet datum may
be a lift of a finite total even when individual summands admit no lift. -/
theorem existsUnique_hom_extension_of_facets (hS : IsOpen S) {κ : Type*} [Countable κ]
    (A : κ → AffineSubspace ℝ V)
    (hA : ∀ k, Module.finrank ℝ (A k).direction + 1 < Module.finrank ℝ V)
    {G O U : Opens (TopCat.of S)} (hGO : G ≤ O) (hOU : O ≤ U)
    (hdense : (O : Set (TopCat.of S)) ⊆ closure (G : Set (TopCat.of S)))
    (hsing : ∀ x ∈ U, x ∉ O → ∃ k, (x : V) ∈ A k)
    (H : C) (s : H ⟶ F.obj.obj (op G))
    (hfacet : ∀ x ∈ O, x ∉ G →
      ∃ (N : Opens (TopCat.of S)) (t : H ⟶ F.obj.obj (op N)), x ∈ N ∧
        t ≫ F.obj.map (homOfLE (inf_le_left : N ⊓ G ≤ N)).op =
          s ≫ F.obj.map (homOfLE (inf_le_right : N ⊓ G ≤ G)).op) :
    ∃! t : H ⟶ F.obj.obj (op U), t ≫ F.obj.map (homOfLE (hGO.trans hOU)).op = s := by
  have := F.hasLocallyBijectivePreconnectedRestrictions_sheafOver hF H
  exact TopCat.Sheaf.existsUnique_extension_of_facets (CategoryTheory.sheafOver F H)
    hS A hA hGO hOU hdense hsing s hfacet

end Facets

end TopCat.Sheaf
