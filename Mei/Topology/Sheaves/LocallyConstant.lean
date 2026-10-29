/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Connected.Basic

/-!
# Locally bijective restrictions to preconnected opens

A sheaf satisfies the restriction-sense local-constancy condition when every
point has an open neighborhood whose sections restrict bijectively to each
nonempty preconnected open subset. On locally connected spaces this agrees
with being locally isomorphic to a constant sheaf. On arbitrary spaces the
conditions can differ: the restriction criterion is vacuous when there are no
nonempty preconnected open subsets.
-/

public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- The restriction-sense local-constancy condition: bijective restriction to
nonempty preconnected subopens of a sufficiently small neighborhood. On locally
connected spaces this agrees with the usual locally constant sheaf condition.
On arbitrary spaces the conditions can differ, and this criterion can be vacuous. -/
class HasLocallyBijectivePreconnectedRestrictions (F : X.Sheaf (Type v)) : Prop where
  /-- Each point has an open neighborhood with the local restriction property. -/
  exists_bijective_restrictions (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∀ (V : Opens X) (hVU : V ≤ U),
      (V : Set X).Nonempty → IsPreconnected (V : Set X) →
        Function.Bijective (F.presheaf.map (homOfLE hVU).op)

variable (F : X.Sheaf (Type v)) [F.HasLocallyBijectivePreconnectedRestrictions]

/-- Every point has a neighborhood `W` such that restriction between nonempty preconnected
opens `P ≤ N ≤ W` is bijective. -/
theorem exists_bijective_restrictions_of_le (x : X) :
    ∃ W : Opens X, x ∈ W ∧ ∀ (N P : Opens X) (hPN : P ≤ N), N ≤ W →
      (P : Set X).Nonempty → IsPreconnected (N : Set X) → IsPreconnected (P : Set X) →
        Function.Bijective (F.presheaf.map (homOfLE hPN).op) := by
  obtain ⟨W, hxW, hW⟩ := HasLocallyBijectivePreconnectedRestrictions.exists_bijective_restrictions
    (F := F) x
  refine ⟨W, hxW, fun N P hPN hNW hP hcN hcP => ?_⟩
  have hN := hW N hNW (hP.mono hPN) hcN
  have hcomp : F.presheaf.map (homOfLE hPN).op ∘ F.presheaf.map (homOfLE hNW).op =
      F.presheaf.map (homOfLE (hPN.trans hNW)).op :=
    funext fun s => TopCat.Presheaf.restrict_restrict (CC := fun T => T) (F := F.presheaf) hPN hNW s
  rw [← Function.Bijective.of_comp_iff _ hN, hcomp]
  exact hW P (hPN.trans hNW) hP hcP

end TopCat.Sheaf
