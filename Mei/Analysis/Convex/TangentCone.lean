/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Tangent cones of convex sets

At a point `x` of a convex set `P`, the one-sided tangent cone contains every displacement
`y - x` to a point `y` of `P`. In finite dimension it lies in the direction of the affine span of
`P`, so the cone and `P` have the same affine direction.
-/

public section

open Filter Topology Set

namespace Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {x : V}

/-- A displacement from `x` to a point of a convex set lies in the tangent cone at `x`. -/
theorem sub_mem_posTangentConeAt (hP : Convex ℝ P) (hx : x ∈ P) {y : V} (hy : y ∈ P) :
    y - x ∈ posTangentConeAt P x :=
  sub_mem_posTangentConeAt_of_openSegment_subset (hP.openSegment_subset hx hy)

end Convex

namespace Mei

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {x : V}
  [FiniteDimensional ℝ V]

/-- In finite dimension, the tangent cone at a point of `P` lies in the direction of the affine
span of `P`. -/
theorem posTangentConeAt_subset_direction_affineSpan (hx : x ∈ P) :
    posTangentConeAt P x ⊆ (affineSpan ℝ P).direction := by
  intro v hv
  obtain ⟨α, l, hl, s, d, hd0, hdP, hsd⟩ := exists_fun_of_mem_tangentConeAt hv
  refine (Submodule.closed_of_finiteDimensional (affineSpan ℝ P).direction).mem_of_tendsto hsd ?_
  filter_upwards [hdP] with n hn
  refine Submodule.smul_of_tower_mem _ _ ?_
  simpa using AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hn)
    (subset_affineSpan ℝ _ hx)

end Mei

namespace Convex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P : Set V} {x : V}
  [FiniteDimensional ℝ V]

/-- A convex set and its tangent cone at one of its points have the same affine direction. -/
theorem direction_affineSpan_posTangentConeAt (hP : Convex ℝ P) (hx : x ∈ P) :
    (affineSpan ℝ (posTangentConeAt P x)).direction = (affineSpan ℝ P).direction := by
  have h0 : (0 : V) ∈ posTangentConeAt P x := by
    simpa using hP.sub_mem_posTangentConeAt hx hx
  have hsub : ((fun y => y - x) '' P) ⊆ posTangentConeAt P x := by
    rintro _ ⟨y, hy, rfl⟩
    exact hP.sub_mem_posTangentConeAt hx hy
  refine le_antisymm ?_ ?_
  · rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    simpa using Mei.posTangentConeAt_subset_direction_affineSpan hx hv
  · rw [direction_affineSpan, direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hx]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using vsub_mem_vectorSpan ℝ (hsub ⟨y, hy, rfl⟩) h0

end Convex
