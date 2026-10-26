/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Face

/-!
# Directions of finite intersections of affine halfspaces

The direction of a nonempty polyhedron is the common kernel of the linear
parts of the inequalities that vanish on the whole polyhedron. This identifies
the tangent space without choosing an irredundant presentation, and allows
arbitrary offsets, unboundedness and lineality.

The argument uses `Convex.exists_mem_zero_iff_forall` to choose a point with
exactly the universally active constraints, and
`AffineMap.exists_pos_lineMap_neg_forall_le` to move a short distance in any
vector annihilated by those constraints.
-/

public section

namespace AffineMap

open Set

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Finite ι]

/-- The direction of a nonempty finite intersection of affine halfspaces is
the common kernel of the universally active linear parts. -/
theorem direction_affineSpan_setOf_forall_le (g : ι → (V →ᵃ[ℝ] ℝ))
    (hne : ({x | ∀ j, g j x ≤ 0} : Set V).Nonempty) :
    (affineSpan ℝ {x | ∀ j, g j x ≤ 0}).direction =
      ⨅ (j) (_ : ∀ x, (∀ k, g k x ≤ 0) → g j x = 0), (g j).linear.ker := by
  let P : Set V := {x | ∀ j, g j x ≤ 0}
  have hconv : Convex ℝ P := by
    simpa only [P, Set.ofPred_forall, Set.preimage, Set.mem_Iic] using
      convex_iInter (fun j => (convex_Iic (0 : ℝ)).affine_preimage (g j))
  obtain ⟨p, hp, hactive⟩ := hconv.exists_mem_zero_iff_forall hne g
    (fun j x hx => hx j)
  apply le_antisymm
  · refine le_iInf fun j => le_iInf fun hj => ?_
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    exact LinearMap.mem_ker.mpr (by
      rw [(g j).linear_apply_vsub, hj x hx, hj y hy, vsub_self])
  · intro v hv
    have hvzero : ∀ j, g j p = 0 → (g j).linear v = 0 := by
      intro j hj
      have hvall : ∀ j, (∀ x, (∀ k, g k x ≤ 0) → g j x = 0) →
          (g j).linear v = 0 := by simpa only [Submodule.mem_iInf, LinearMap.mem_ker] using hv
      exact hvall j ((hactive j).mp hj)
    obtain ⟨ε, hε, hmove⟩ := exists_pos_lineMap_neg_forall_le g hp (x := v + p) (by
      intro j hj
      rw [← vadd_eq_add, (g j).map_vadd, hvzero j hj, hj]
      simp)
    have hdir := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ P hmove) (subset_affineSpan ℝ P hp)
    have heq : lineMap p (v + p) (-ε) -ᵥ p = (-ε) • v := by
      simpa only [vsub_eq_sub, add_sub_cancel_right] using lineMap_vsub_left p (v + p) (-ε)
    rw [heq] at hdir
    exact (Submodule.smul_mem_iff _ (neg_ne_zero.mpr hε.ne')).mp hdir

end AffineMap
