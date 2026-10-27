/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Intrinsic

/-!
# Cutting convex sets by affine halfspaces

A halfspace cut that contains a strictly feasible point of a convex set retains
its affine span. An affine inequality with a strictly feasible point is strict
throughout the relative interior. These facts detect full-dimensional pieces
and disjoint relative interiors in subdivisions by hyperplanes.
-/

public section

open Set AffineSubspace

namespace AffineMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A halfspace cut containing a strictly feasible point of a convex set
preserves its affine span. Continuity of the affine functional is unnecessary. -/
theorem affineSpan_inter_le_eq (g : V →ᵃ[ℝ] ℝ) {P : Set V} (hP : Convex ℝ P)
    (hg : ∃ x ∈ P, g x < 0) :
    affineSpan ℝ (P ∩ {x | g x ≤ 0}) = affineSpan ℝ P := by
  obtain ⟨x, hx, hgx⟩ := hg
  apply le_antisymm (affineSpan_mono ℝ inter_subset_left)
  apply affineSpan_le.mpr
  intro y hy
  let A := affineSpan ℝ (P ∩ {z | g z ≤ 0})
  have hxA : x ∈ A := subset_affineSpan ℝ _ ⟨hx, hgx.le⟩
  have hc : Continuous (fun t : ℝ => g (lineMap x y t)) := by
    simp only [g.apply_lineMap, lineMap_apply_ring]
    fun_prop
  have hn : {t : ℝ | g (lineMap x y t) < 0} ∈ nhds (0 : ℝ) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simpa using hgx)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let t := min (δ / 2) (1 / 2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have hlt : g (lineMap x y t) < 0 := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htδ)
  have hty : lineMap x y t ∈ A := subset_affineSpan ℝ _
    ⟨hP.lineMap_mem hx hy ⟨ht.le, (min_le_right _ _).trans (by norm_num)⟩,
      hlt.le⟩
  have hv := A.vsub_mem_direction hty hxA
  rw [lineMap_vsub_left] at hv
  have hyx : y -ᵥ x ∈ A.direction :=
    (Submodule.smul_mem_iff A.direction ht.ne').mp hv
  simpa only [vsub_vadd, A, SetLike.mem_coe] using A.vadd_mem_of_mem_direction hyx hxA

end AffineMap
