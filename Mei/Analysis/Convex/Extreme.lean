/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Extreme

/-!
# Extreme subsets of intersections

Intersections of extreme subsets are extreme in the intersection of their
ambient sets. This provides closure under intersections when combining faces
of different convex sets.
-/

public section

namespace IsExtreme

variable {R V : Type*} [Semiring R] [PartialOrder R] [AddCommMonoid V] [SMul R V]
  {P Q F G : Set V}

/-- Intersections of extreme subsets are extreme in the intersection of their ambient sets. -/
theorem inter_inter (hF : IsExtreme R P F) (hG : IsExtreme R Q G) :
    IsExtreme R (P ∩ Q) (F ∩ G) := by
  refine ⟨fun x hx => ⟨hF.subset hx.1, hG.subset hx.2⟩, ?_⟩
  intro x hx y hy z hz hxy
  exact ⟨hF.left_mem_of_mem_openSegment hx.1 hy.1 hz.1 hxy,
    hG.left_mem_of_mem_openSegment hx.2 hy.2 hz.2 hxy⟩

end IsExtreme
