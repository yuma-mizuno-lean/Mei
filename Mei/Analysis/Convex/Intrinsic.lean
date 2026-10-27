/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Linarith

/-!
# Relative interior points

An affine function nonpositive on a set and zero at a relative interior point
vanishes on that set. Continuity of the affine function is not required.

A set is a neighbourhood of each of its relative interior points within its
affine span: points of the span close to a relative interior point stay in the set.
-/

public section

open Set Filter Topology AffineSubspace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

namespace AffineMap

/-- An affine function nonpositive on a set and zero at a relative interior
point must vanish on the entire set. -/
theorem eq_zero_on_of_mem_intrinsicInterior (g : V →ᵃ[ℝ] ℝ) {P : Set V} {x : V}
    (hg : ∀ p ∈ P, g p ≤ 0) (hx : x ∈ intrinsicInterior ℝ P) (hgx : g x = 0) :
    ∀ p ∈ P, g p = 0 := by
  obtain ⟨xA, hxA, rfl⟩ := hx
  let A := affineSpan ℝ P
  let : Nonempty A := ⟨xA⟩
  intro p hp
  let pA : A := ⟨p, subset_affineSpan ℝ P hp⟩
  have hc : Continuous (fun t : ℝ => AffineMap.lineMap xA pA (-t)) :=
    AffineMap.lineMap_continuous.comp continuous_neg
  have ht : Tendsto (fun t : ℝ => AffineMap.lineMap xA pA (-t)) (𝓝 0) (𝓝 xA) := by
    simpa only [neg_zero, AffineMap.lineMap_apply_zero] using hc.tendsto 0
  have hs : ∀ᶠ y : A in 𝓝 xA, (y : V) ∈ P :=
    mem_interior_iff_mem_nhds.mp hxA
  have he := ht.eventually hs
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  have hε : 0 < δ / 2 := by positivity
  have hhalf : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    linarith
  have hy : A.subtype (AffineMap.lineMap xA pA (-(δ / 2))) ∈ P := hball hhalf
  have hyP : AffineMap.lineMap (xA : V) p (-(δ / 2)) ∈ P := by
    simpa only [A.subtype.apply_lineMap, AffineSubspace.subtype_apply] using hy
  have hle := hg _ hyP
  rw [g.apply_lineMap, AffineMap.lineMap_apply_ring, hgx] at hle
  have hpnonpos := hg p hp
  nlinarith

end AffineMap

namespace Mei

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- A set is a neighbourhood of each of its relative interior points within its affine span. -/
theorem mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior {P : Set V} {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) : P ∈ 𝓝[affineSpan ℝ P] x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [nhdsWithin_eq_map_subtype_coe y.property]
  exact mem_interior_iff_mem_nhds.mp hy

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- For a set spanning the ambient affine space, relative and ordinary interiors agree. -/
theorem intrinsicInterior_eq_interior_of_affineSpan_eq_top {P : Set V}
    (hP : affineSpan ℝ P = ⊤) : intrinsicInterior ℝ P = interior P := by
  refine Subset.antisymm (fun x hx => ?_) interior_subset_intrinsicInterior
  have hn := mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hx
  simpa [hP, ← mem_interior_iff_mem_nhds] using hn

end Mei
