/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mei.Analysis.Convex.Intrinsic

/-!
# Relative interiors and boundaries of polyhedra

In a finite affine halfspace presentation, the relative interior is obtained by
making every inequality strict except those that vanish on the whole polyhedron.
The relative boundary is the union of the active-row faces of the remaining rows.
Redundant inequalities, empty and lower-dimensional polyhedra, unboundedness and
lineality are allowed. No finite-dimensionality assumption is needed.
-/

public section

open Set Filter Topology AffineSubspace

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

namespace Mei.Convex

/-- A point is in the relative interior precisely when it belongs to the polyhedron
and every defining row that is not identically zero on the polyhedron is strict at that point. -/
theorem mem_intrinsicInterior_iff_forall_lt [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | ∀ j, g j x ≤ 0}) {x : V} :
    x ∈ intrinsicInterior ℝ P ↔
      x ∈ P ∧ ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0 := by
  constructor
  · intro hx
    have hxP := intrinsicInterior_subset hx
    refine ⟨hxP, fun j hj => ?_⟩
    have hle : g j x ≤ 0 := by rw [hP] at hxP; exact hxP j
    apply lt_of_le_of_ne hle
    intro hzero
    obtain ⟨p, hp, hjp⟩ := hj
    have hgj : ∀ q ∈ P, g j q ≤ 0 := by
      intro q hq
      rw [hP] at hq
      exact hq j
    have heq : g j p = 0 := by
      simpa only [ContinuousAffineMap.coe_toAffineMap] using
        (g j).toAffineMap.eq_zero_on_of_mem_intrinsicInterior hgj hx hzero p hp
    exact hjp.ne heq
  · rintro ⟨hxP, hxstrict⟩
    let A := affineSpan ℝ P
    let xA : A := ⟨x, subset_affineSpan ℝ P hxP⟩
    let J : Set ι := {j | ∃ p ∈ P, g j p < 0}
    let U : Set A := {y | ∀ j : J, g j.val (y : V) < 0}
    have hU : IsOpen U := by
      have heq : U = ⋂ j : J, {y : A | g j.val (y : V) < 0} := by ext y; simp [U]
      rw [heq]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt ((g j.val).continuous.comp continuous_subtype_val) continuous_const
    have hxU : xA ∈ U := fun j => hxstrict j.val j.property
    have hUP : U ⊆ ((↑) ⁻¹' P : Set A) := by
      intro y hy
      rw [hP]
      intro j
      by_cases hj : j ∈ J
      · exact (hy ⟨j, hj⟩).le
      · have hzero : ∀ p ∈ P, g j p = 0 := by
          intro p hp
          have hle : g j p ≤ 0 := by rw [hP] at hp; exact hp j
          apply le_antisymm hle
          by_contra hn
          exact hj ⟨p, hp, lt_of_not_ge hn⟩
        have heq : P.EqOn (g j).toAffineMap (0 : V →ᵃ[ℝ] ℝ) := hzero
        have hspan := AffineMap.eqOn_affineSpan heq y.property
        exact le_of_eq hspan
    have hxint : xA ∈ interior U := by rwa [hU.interior_eq]
    exact ⟨xA, interior_mono hUP hxint, rfl⟩

/-- The relative boundary is exactly the union of the active-row faces whose
rows are not identically zero on the polyhedron. Every indexed face is proper;
empty row faces may occur and contribute nothing to the union. -/
theorem intrinsicFrontier_eq_iUnion_active [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | ∀ j, g j x ≤ 0}) :
    intrinsicFrontier ℝ P =
      ⋃ j ∈ {j | ∃ p ∈ P, g j p < 0}, {x ∈ P | g j x = 0} := by
  have hclosed : IsClosed P := by
    rw [hP]
    exact (TauCeti.isConvexPolyhedron_setOf_forall g).isClosed
  have hrel : intrinsicClosure ℝ P = P :=
    IsClosed.intrinsicClosure (hclosed.preimage
      (continuous_subtype_val : Continuous ((↑) : affineSpan ℝ P → V)))
  rw [← intrinsicClosure_sdiff_intrinsicInterior, hrel]
  ext x
  rw [Set.mem_sdiff, mem_intrinsicInterior_iff_forall_lt g hP]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxP, hxnot⟩
    have hnot : ¬ ∀ j, (∃ p ∈ P, g j p < 0) → g j x < 0 :=
      fun h => hxnot ⟨hxP, h⟩
    push Not at hnot
    obtain ⟨j, hj, hgj⟩ := hnot
    have hle : g j x ≤ 0 := by rw [hP] at hxP; exact hxP j
    exact ⟨j, hj, hxP, le_antisymm hle hgj⟩
  · rintro ⟨j, hj, hxP, hgj⟩
    refine ⟨hxP, ?_⟩
    rintro ⟨_, hstrict⟩
    have hlt := hstrict j hj
    rw [hgj] at hlt
    exact lt_irrefl 0 hlt

end Mei.Convex
