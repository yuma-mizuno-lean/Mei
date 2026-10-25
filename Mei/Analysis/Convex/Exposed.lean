/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Exposed

/-!
# Exposed subsets of intersections

Intersections of exposed subsets are exposed in the intersection of their
ambient sets. This supplies exposed faces when intersecting convex sets,
without requiring polyhedral hypotheses.
-/

public section

namespace IsExposed

variable {R V : Type*} [TopologicalSpace R] [Ring R] [PartialOrder R] [IsOrderedRing R]
  [ContinuousAdd R] [AddCommMonoid V] [TopologicalSpace V] [Module R V] {P Q F G : Set V}

/-- Intersections of exposed subsets are exposed in the intersection of their
ambient sets. This includes empty intersections and requires no convexity. -/
theorem inter_inter (hF : IsExposed R P F) (hG : IsExposed R Q G) :
    IsExposed R (P ∩ Q) (F ∩ G) := by
  rintro ⟨p, hpF, hpG⟩
  obtain ⟨l, hl⟩ := hF ⟨p, hpF⟩
  obtain ⟨m, hm⟩ := hG ⟨p, hpG⟩
  have hpL := hl ▸ hpF
  have hpM := hm ▸ hpG
  refine ⟨l + m, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxF, hxG⟩
    have hxL := hl ▸ hxF
    have hxM := hm ▸ hxG
    exact ⟨⟨hxL.1, hxM.1⟩, fun y hy => add_le_add (hxL.2 y hy.1) (hxM.2 y hy.2)⟩
  · rintro x ⟨⟨hxP, hxQ⟩, hxmax⟩
    have hsum := hxmax p ⟨hpL.1, hpM.1⟩
    constructor
    · rw [hl]
      refine ⟨hxP, fun y hy => ?_⟩
      exact (add_le_add_iff_right (m x)).mp
        ((add_le_add (hpL.2 y hy) (hpM.2 x hxQ)).trans hsum)
    · rw [hm]
      refine ⟨hxQ, fun y hy => ?_⟩
      exact (add_le_add_iff_left (l x)).mp
        ((add_le_add (hpL.2 x hxP) (hpM.2 y hy)).trans hsum)

end IsExposed
