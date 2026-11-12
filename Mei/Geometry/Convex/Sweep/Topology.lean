/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Sweep.Topology

/-!
# Sweeping the horizontal axis

The closed lower half-plane is the negative-ray sweep of the horizontal axis.
-/

public section

namespace Mei.Convex

/-- An unbounded base with lineality: the horizontal axis sweeps to the closed
lower half-plane under the positive vertical sweeping vector. -/
theorem sweep_horizontal_axis :
    Set.sweep ℝ {p : ℝ × ℝ | p.2 = 0} (0, 1) = {p : ℝ × ℝ | p.2 ≤ 0} :=
  Set.sweep_hyperplane (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 rfl

end Mei.Convex
