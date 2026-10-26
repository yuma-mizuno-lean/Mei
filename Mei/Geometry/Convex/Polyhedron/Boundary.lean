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
An ordinary noninterior point has a nonconstant active row, even when constant
zero rows are present. Redundant inequalities, empty and lower-dimensional
polyhedra, unboundedness and lineality are allowed. The affine direction of a
nonempty polyhedron is the common kernel of the rows vanishing everywhere on it.
No finite-dimensionality assumption is needed.
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

/-- The affine direction of a finite intersection of half-spaces is the common
kernel of the rows vanishing on the whole polyhedron. A relative interior point
supplies nonemptiness; no finite-dimensionality assumption is needed. -/
theorem direction_affineSpan_eq_iInf_ker [Finite ι] (g : ι → (V →ᴬ[ℝ] ℝ))
    {P : Set V} (hP : P = {x | ∀ j, g j x ≤ 0}) {p : V}
    (hp : p ∈ intrinsicInterior ℝ P) :
    (affineSpan ℝ P).direction =
      ⨅ j : {j // ∀ x ∈ P, g j x = 0}, (g j.val).toAffineMap.linear.ker := by
  apply le_antisymm
  · apply le_iInf
    intro j
    rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
    rintro v ⟨a, ha, b, hb, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [AffineMap.linear_apply_vsub]
    exact sub_eq_zero.mpr ((j.property a ha).trans (j.property b hb).symm)
  · intro v hv
    have hstrict := (mem_intrinsicInterior_iff_forall_lt g hP).mp hp
    -- Every nonconstant inequality stays strict for a small displacement in `v`.
    have hrow (j : ι) : ∀ᶠ t : ℝ in 𝓝 0, g j (p + t • v) ≤ 0 := by
      by_cases hj : ∃ x ∈ P, g j x < 0
      · have hlt : g j (p + (0 : ℝ) • v) < 0 := by simpa using hstrict.2 j hj
        exact ((by fun_prop : Continuous (fun t : ℝ => g j (p + t • v))).continuousAt.eventually
          (gt_mem_nhds hlt)).mono fun _ ht => ht.le
      · have hz : ∀ x ∈ P, g j x = 0 := by
          intro x hx
          have hxle : g j x ≤ 0 := by rw [hP] at hx; exact hx j
          exact le_antisymm hxle (by by_contra hn; exact hj ⟨x, hx, lt_of_not_ge hn⟩)
        have hgv := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hv ⟨j, hz⟩)
        exact Filter.Eventually.of_forall fun t => by
          have he := (g j).toAffineMap.map_vadd p (t • v)
          simpa only [vadd_eq_add, ContinuousAffineMap.coe_toAffineMap, map_smul, hgv, smul_zero,
            hz p hstrict.1, zero_add, add_comm] using he.le
    have hall : ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ P := by
      simpa only [hP, Set.mem_ofPred_eq] using Filter.eventually_all.mpr hrow
    obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hall
    have hmem : p + (ε / 2) • v ∈ P := he (by
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2)]
      linarith)
    have hdir := (affineSpan ℝ P).vsub_mem_direction
      (subset_affineSpan ℝ P hmem) (subset_affineSpan ℝ P hstrict.1)
    have ht : ε / 2 ≠ 0 := by positivity
    have hscaled := (affineSpan ℝ P).direction.smul_mem (ε / 2)⁻¹ hdir
    simpa only [vsub_eq_sub, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht,
      one_smul] using hscaled

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- At a point of a finite intersection of affine half-spaces that is not interior,
some active inequality has nonzero linear part. Constant zero rows are ignored. -/
theorem exists_nonzero_active_row_of_notMem_interior [Finite ι]
    (g : ι → (V →ᴬ[ℝ] ℝ)) {x : V}
    (hx : ∀ j, g j x ≤ 0) (hnot : x ∉ interior {y | ∀ j, g j y ≤ 0}) :
    ∃ j, g j x = 0 ∧ (g j).toAffineMap.linear ≠ 0 := by
  by_contra! hn
  apply hnot
  apply mem_interior_iff_mem_nhds.mpr
  have hrow (j : ι) : ∀ᶠ y in 𝓝 x, g j y ≤ 0 := by
    by_cases hz : g j x = 0
    · obtain ⟨c, hc⟩ := (g j).toAffineMap.linear_eq_zero_iff_exists_const.mp (hn j hz)
      have heq (y : V) : g j y = c := congrArg (fun f : V →ᵃ[ℝ] ℝ => f y) hc
      have hc0 : c = 0 := (heq x).symm.trans hz
      exact Filter.Eventually.of_forall fun y => ((heq y).trans hc0).le
    · exact ((g j).continuous.continuousAt.eventually
        (gt_mem_nhds (lt_of_le_of_ne (hx j) hz))).mono fun _ hy => hy.le
  exact Filter.eventually_all.mpr hrow

end Mei.Convex
