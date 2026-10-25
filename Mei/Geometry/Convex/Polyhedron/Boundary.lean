/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.Linarith

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

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace ContinuousAffineMap

/-- An affine function nonpositive on a set and zero at a relative interior
point must vanish on the entire set. -/
theorem eq_zero_on_of_mem_intrinsicInterior (g : V →ᴬ[ℝ] ℝ) {P : Set V} {x : V}
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
  have hy := hball (show δ / 2 ∈ Metric.ball (0 : ℝ) δ by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    linarith)
  have hyP : AffineMap.lineMap (xA : V) p (-(δ / 2)) ∈ P := by
    change A.subtype (AffineMap.lineMap xA pA (-(δ / 2))) ∈ P at hy
    rw [A.subtype.apply_lineMap] at hy
    exact hy
  have hle := hg _ hyP
  rw [g.apply_lineMap, AffineMap.lineMap_apply_ring, hgx] at hle
  have hpnonpos := hg p hp
  nlinarith

/-- A row with a negative value on the set cuts out a proper active-row subset. -/
theorem zero_face_ne_self_of_exists_neg (g : V →ᴬ[ℝ] ℝ) {P : Set V}
    (hg : ∃ p ∈ P, g p < 0) : {x ∈ P | g x = 0} ≠ P := by
  intro heq
  obtain ⟨p, hp, hgp⟩ := hg
  have hpface : p ∈ {x ∈ P | g x = 0} := by rwa [heq]
  linarith [hpface.2]

end ContinuousAffineMap

namespace Mei.Convex

/-- A point is in the relative interior precisely when every defining row
that is not identically zero on the polyhedron is strict at that point. -/
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
    have heq := (g j).eq_zero_on_of_mem_intrinsicInterior hgj hx hzero p hp
    linarith
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
