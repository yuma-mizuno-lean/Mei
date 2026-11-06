/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Tangent cones of convex sets

At a point `x` of a convex set `P`, the one-sided tangent cone contains every displacement
`y - x` to a point `y` of `P`. In finite dimension it lies in the direction of the affine span of
`P`, so the cone and `P` have the same affine direction.
-/

public section

open Filter Topology Set
open scoped NNReal Pointwise

namespace Mei

/-- The positive tangent cone of any set is invariant under nonnegative scaling. -/
theorem smul_mem_posTangentConeAt {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousSMul ℝ V] {P : Set V} {x v : V}
    (hv : v ∈ posTangentConeAt P x) {t : ℝ} (ht : 0 ≤ t) :
    t • v ∈ posTangentConeAt P x := by
  obtain ⟨α, l, hl, c, d, hd0, hdP, hcd⟩ := exists_fun_of_mem_tangentConeAt hv
  refine mem_tangentConeAt_of_seq l (fun n => NNReal.mk t ht * c n) d hd0 hdP ?_
  simpa only [mul_smul, NNReal.smul_def, NNReal.coe_mk] using hcd.const_smul t

end Mei

namespace Convex

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] {P : Set V} {x : V}

/-- A displacement from `x` to a point of a convex set lies in the tangent cone at `x`. -/
theorem sub_mem_posTangentConeAt (hP : Convex ℝ P) (hx : x ∈ P) {y : V} (hy : y ∈ P) :
    y - x ∈ posTangentConeAt P x :=
  sub_mem_posTangentConeAt_of_openSegment_subset (hP.openSegment_subset hx hy)

/-- At a point of a convex set, the positive tangent cone is the closure of the nonnegative
multiples of displacements to points of the set. -/
theorem posTangentConeAt_eq_closure (hP : Convex ℝ P) (hx : x ∈ P) :
    _root_.posTangentConeAt P x = closure ((Set.univ : Set ℝ≥0) • (x + ·) ⁻¹' P) := by
  refine Subset.antisymm ?_ ?_
  · intro v hv
    rw [_root_.posTangentConeAt, tangentConeAt_eq_biInter_closure] at hv
    simpa using mem_iInter₂.mp hv Set.univ Filter.univ_mem
  · refine closure_minimal ?_ ?_
    · rintro _ ⟨t, _, v, hv, rfl⟩
      have hsub := hP.sub_mem_posTangentConeAt hx hv
      rw [add_sub_cancel_left] at hsub
      exact Mei.smul_mem_posTangentConeAt hsub t.coe_nonneg
    · rw [_root_.posTangentConeAt, tangentConeAt_eq_biInter_closure]
      exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_closure

variable [IsTopologicalAddGroup V]

/-- The positive tangent cone at a point of a convex set is convex. -/
theorem posTangentConeAt (hP : Convex ℝ P) (hx : x ∈ P) :
    Convex ℝ (_root_.posTangentConeAt P x) := by
  rw [hP.posTangentConeAt_eq_closure hx]
  apply Convex.closure
  have hD := hP.translate_preimage_right x
  rintro _ ⟨a, _, u, hu, rfl⟩ _ ⟨b, _, v, hv, rfl⟩ c d hc hd hcd
  obtain ⟨w, hw, heq⟩ := hD.exists_mem_add_smul_eq hu hv
    (mul_nonneg hc a.coe_nonneg) (mul_nonneg hd b.coe_nonneg)
  refine ⟨NNReal.mk (c * a + d * b) (add_nonneg (mul_nonneg hc a.coe_nonneg)
    (mul_nonneg hd b.coe_nonneg)), Set.mem_univ _, w, hw, ?_⟩
  simpa only [NNReal.smul_def, NNReal.coe_mk, mul_smul] using heq

/-- The positive tangent cone of a convex set is closed under addition. -/
theorem add_mem_posTangentConeAt (hP : Convex ℝ P) (hx : x ∈ P) {u v : V}
    (hu : u ∈ _root_.posTangentConeAt P x) (hv : v ∈ _root_.posTangentConeAt P x) :
    u + v ∈ _root_.posTangentConeAt P x := by
  have hm := hP.posTangentConeAt hx hu hv (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa [smul_add, smul_smul] using Mei.smul_mem_posTangentConeAt hm (by norm_num : (0 : ℝ) ≤ 2)

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
    (affineSpan ℝ (_root_.posTangentConeAt P x)).direction = (affineSpan ℝ P).direction := by
  have h0 : (0 : V) ∈ _root_.posTangentConeAt P x := by
    simpa using hP.sub_mem_posTangentConeAt hx hx
  have hsub : ((fun y => y - x) '' P) ⊆ _root_.posTangentConeAt P x := by
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
