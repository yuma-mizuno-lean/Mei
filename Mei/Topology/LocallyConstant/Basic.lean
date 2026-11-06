/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local constancy on subsets

An ambient function that is constant near every point of a subset restricts to a
locally constant function on that subset. This transfers ambient neighborhood
stability to the subspace topology, using `IsLocallyConstant.iff_eventually_eq`.
-/

public section

open Filter Topology

namespace Set

/-- A function constant on an ambient neighborhood of each point of `s` restricts
to a locally constant function on `s`. -/
theorem isLocallyConstant_domRestrict_of_eventually_eq {X Y : Type*} [TopologicalSpace X]
    (s : Set X) {f : X → Y} (hf : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, f y = f x) :
    IsLocallyConstant (s.domRestrict f) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact continuous_subtype_val.continuousAt.tendsto.eventually (hf x.val x.property)

end Set
