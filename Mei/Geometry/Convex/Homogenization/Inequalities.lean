/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Homogenization
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Homogeneous inequalities for homogenization

For a nonempty affine-inequality presentation, the closed cone generated
by its height-one embedding is exactly the cone obtained by homogenizing its
inequalities and requiring nonnegative height. The height-zero part follows
from the recession-cone theorem, so unbounded bases and lineality are included.

Nonemptiness is essential. Empty presentations can give different homogeneous
inequality cones, whereas carrier-defined homogenization always gives the zero
cone for the empty set.
-/

public section

namespace ContinuousAffineMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V]

/-- A nonpositive affine support remains nonpositive throughout the actual
closed homogenization, including at height zero. -/
theorem homogenizedInequality_nonpos [ContinuousSMul ℝ V] {P : Set V}
    (g : V →ᴬ[ℝ] ℝ) (hg : ∀ x ∈ P, g x ≤ 0) {z : V × ℝ}
    (hz : z ∈ Set.homogenization P) :
    homogenize g z ≤ 0 := by
  let C := (PointedCone.positive ℝ ℝ).comap (-(homogenize g).toLinearMap)
  have hcoe : (C : Set (V × ℝ)) = {z | homogenize g z ≤ 0} := by
    ext z
    simp only [C, SetLike.mem_coe, PointedCone.mem_comap, PointedCone.mem_positive,
      LinearMap.neg_apply, ContinuousLinearMap.coe_coe, neg_nonneg, Set.mem_ofPred_eq]
  have hclosed : IsClosed (C : Set (V × ℝ)) := by
    rw [hcoe]
    exact isClosed_le (homogenize g).continuous continuous_const
  have hle : Set.homogenization P ≤ C :=
    (Set.homogenization_le_iff hclosed).mpr fun x hx => by
      simpa only [C, PointedCone.mem_comap, PointedCone.mem_positive, LinearMap.neg_apply,
        ContinuousLinearMap.coe_coe, neg_nonneg, homogenize_apply_one] using hg x hx
  simpa only [C, PointedCone.mem_comap, PointedCone.mem_positive, LinearMap.neg_apply,
    ContinuousLinearMap.coe_coe, neg_nonneg] using hle hz

end ContinuousAffineMap
