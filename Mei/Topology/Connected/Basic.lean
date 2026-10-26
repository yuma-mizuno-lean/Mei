/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Connected.Basic

/-!
# Limits in closures of connected components

A continuous image of a preconnected set lies in one connected component of
any set containing that image. Its limiting values lie in the ambient closure
of that component. This applies to endpoint limits of curves on half-open intervals.
-/

public section

open Set

namespace IsPreconnected

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A limiting value of a continuous image of a preconnected set lies in the
closure of the component containing the image of any point of that set. -/
theorem mem_closure_connectedComponentIn_image {s : Set X} {u : Set Y} {f : X → Y}
    (hs : IsPreconnected s) (hf : ContinuousOn f s) {x t : X} (hx : x ∈ s)
    (ht : t ∈ closure s) (hft : ContinuousWithinAt f s t) (hu : MapsTo f s u) :
    f t ∈ closure (_root_.connectedComponentIn u (f x)) := by
  exact hft.mem_closure ht (image_subset_iff.mp ((hs.image f hf).subset_connectedComponentIn
    (mem_image_of_mem f hx) (image_subset_iff.mpr hu)))

end IsPreconnected
