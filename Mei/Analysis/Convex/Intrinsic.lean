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
# Affine functions at relative interior points

An affine function nonpositive on a set and zero at a relative interior point
vanishes on that set. Continuity of the affine function is not required.
-/

public section

open Set Filter Topology AffineSubspace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

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
