/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Relative interior points

An affine function nonpositive on a set and zero at a relative interior point
vanishes on that set. If it is strictly negative somewhere on the set, it is
strictly negative at every relative interior point. Continuity is not required.

A set is a neighbourhood of each of its relative interior points within its
affine span: points of the span close to a relative interior point stay in the set.
For a closed set, the relative boundary is nowhere dense in the affine span.
For any set, membership is locally constant off the relative boundary within the affine span.
Consequently a convex set meeting a set and missing its relative boundary meets its
affine span only inside the set. Intrinsic closure commutes with products, and
the relative boundary of a cylinder is the cylinder over the relative boundary.
Relative interiors are monotone for sets with equal affine spans. A direction with a positive
component towards an interior point and an arbitrary component along a relative interior
set enters the interior of a convex set. This uses Mathlib's
`Convex.combo_interior_self_mem_interior`.
-/

public section

open Set Filter Topology AffineSubspace

namespace Mei

/-- Intrinsic closure commutes with products of sets in topological affine spaces. -/
theorem intrinsicClosure_prod_eq
    {𝕜 V W P Q : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace P] [TopologicalSpace Q]
    [AddTorsor V P] [AddTorsor W Q] (s : Set P) (t : Set Q) :
    intrinsicClosure 𝕜 (s ×ˢ t) = intrinsicClosure 𝕜 s ×ˢ intrinsicClosure 𝕜 t := by
  simp only [intrinsicClosure_eq_closure_inter_affineSpan, closure_prod_eq,
    affineSpan_prod_eq, AffineSubspace.coe_prod]
  ext x
  simp only [mem_inter_iff, mem_prod]
  tauto

/-- The relative boundary of a cylinder is the cylinder over the relative boundary. -/
@[simp]
theorem intrinsicFrontier_prod_univ
    {𝕜 V W P Q : Type*} [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace P] [TopologicalSpace Q]
    [AddTorsor V P] [AddTorsor W Q] (s : Set P) :
    intrinsicFrontier 𝕜 (s ×ˢ (univ : Set Q)) = intrinsicFrontier 𝕜 s ×ˢ univ := by
  ext x
  simp [← intrinsicClosure_sdiff_intrinsicInterior, intrinsicClosure_prod_eq,
    intrinsicInterior_prod_eq]

/-- Relative interiors are monotone among sets with the same affine span. -/
theorem intrinsicInterior_mono_of_affineSpan_eq
    {𝕜 W A : Type*} [Ring 𝕜] [AddCommGroup W] [Module 𝕜 W]
    [TopologicalSpace A] [AddTorsor W A] {P Q : Set A} (hPQ : P ⊆ Q)
    (hspan : affineSpan 𝕜 P = affineSpan 𝕜 Q) :
    intrinsicInterior 𝕜 P ⊆ intrinsicInterior 𝕜 Q := by
  rw [intrinsicInterior, intrinsicInterior, hspan]
  exact image_mono (interior_mono (preimage_mono hPQ))

end Mei

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

/-- An affine inequality that is strict somewhere on a set is strict throughout
its relative interior. Convexity and continuity of the functional are unnecessary. -/
theorem lt_zero_of_mem_intrinsicInterior (g : V →ᵃ[ℝ] ℝ) {P : Set V}
    (hg : ∀ x ∈ P, g x ≤ 0) (hstrict : ∃ x ∈ P, g x < 0)
    {x : V} (hx : x ∈ intrinsicInterior ℝ P) : g x < 0 := by
  apply lt_of_le_of_ne (hg x (intrinsicInterior_subset hx))
  intro he
  obtain ⟨y, hy, hgy⟩ := hstrict
  exact hgy.ne (g.eq_zero_on_of_mem_intrinsicInterior hg hx he y hy)

end AffineMap

namespace Mei

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- A set is a neighbourhood of each of its relative interior points within its affine span. -/
theorem mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior {P : Set V} {x : V}
    (hx : x ∈ intrinsicInterior ℝ P) : P ∈ 𝓝[affineSpan ℝ P] x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [nhdsWithin_eq_map_subtype_coe y.property]
  exact mem_interior_iff_mem_nhds.mp hy

/-- For a set spanning the ambient affine space, relative and ordinary interiors agree. -/
theorem intrinsicInterior_eq_interior_of_affineSpan_eq_top {𝕜 W P : Type*}
    [Ring 𝕜] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace P] [AddTorsor W P]
    {s : Set P} (hs : affineSpan 𝕜 s = ⊤) : intrinsicInterior 𝕜 s = interior s := by
  refine Subset.antisymm (fun x hx => ?_) interior_subset_intrinsicInterior
  obtain ⟨y, hy, rfl⟩ := hx
  have hn : s ∈ 𝓝[affineSpan 𝕜 s] (y : P) := by
    rw [nhdsWithin_eq_map_subtype_coe y.property]
    exact mem_interior_iff_mem_nhds.mp hy
  simpa [hs, ← mem_interior_iff_mem_nhds] using hn

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- The relative boundary of a closed set is nowhere dense in its affine span. -/
theorem isNowhereDense_preimage_intrinsicFrontier {P : Set V} (hP : IsClosed P)
    {A : AffineSubspace ℝ V} (hA : affineSpan ℝ P = A) :
    IsNowhereDense ((↑) ⁻¹' intrinsicFrontier ℝ P : Set A) := by
  subst hA
  rw [intrinsicFrontier, preimage_image_eq _ Subtype.val_injective,
    isClosed_frontier.isNowhereDense_iff]
  exact interior_frontier (hP.preimage continuous_subtype_val)

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- Off the relative boundary of a set, membership in the set is locally constant within
its affine span. -/
theorem eventually_mem_iff_of_notMem_intrinsicFrontier {P : Set V}
    {A : AffineSubspace ℝ V} (hA : affineSpan ℝ P = A) {x : A}
    (hx : (x : V) ∉ intrinsicFrontier ℝ P) :
    ∀ᶠ y : A in 𝓝 x, ((y : V) ∈ P ↔ (x : V) ∈ P) := by
  subst hA
  have hxfr : x ∉ frontier ((↑) ⁻¹' P : Set (affineSpan ℝ P)) :=
    fun hfr => hx ⟨x, hfr, rfl⟩
  by_cases hxP : (x : V) ∈ P
  · have hint : x ∈ interior ((↑) ⁻¹' P : Set (affineSpan ℝ P)) :=
      (mem_interior_iff_notMem_frontier
        (s := ((↑) ⁻¹' P : Set (affineSpan ℝ P))) hxP).mpr hxfr
    filter_upwards [mem_interior_iff_mem_nhds.mp hint] with y hy
    exact iff_of_true hy hxP
  · have hint : x ∈ interior (((↑) ⁻¹' P : Set (affineSpan ℝ P))ᶜ) :=
      (mem_interior_iff_notMem_frontier
        (s := ((↑) ⁻¹' P : Set (affineSpan ℝ P))ᶜ) hxP).mpr
        (by rwa [frontier_compl])
    filter_upwards [mem_interior_iff_mem_nhds.mp hint] with y hy
    exact iff_of_false hy hxP

end Mei

namespace Convex

/-- A positive component towards an interior point, together with any direction tangent
to a set at a relative interior point, enters the interior of the convex ambient set.
Neither set needs to be closed, polyhedral or finite dimensional. -/
theorem eventually_add_smul_mem_interior {P Q : Set V} (hQ : Convex ℝ Q)
    (hPQ : P ⊆ Q) {q x v : V} (hq : q ∈ intrinsicInterior ℝ P)
    (hx : x ∈ interior Q) {a : ℝ} (ha : 0 < a)
    (hv : v - a • (x - q) ∈ (affineSpan ℝ P).direction) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ interior Q := by
  let w := v - a • (x - q)
  let f : ℝ → V := fun t => q + (t / (1 - t * a)) • w
  have hfspan (t : ℝ) : f t ∈ affineSpan ℝ P := by
    simpa only [f, w, vadd_eq_add, add_comm] using
      (affineSpan ℝ P).vadd_mem_of_mem_direction
        ((affineSpan ℝ P).direction.smul_mem (t / (1 - t * a)) hv)
        (subset_affineSpan ℝ P (intrinsicInterior_subset hq))
  have hftend : Tendsto f (𝓝 0) (𝓝 q) := by
    have hc : ContinuousAt f 0 :=
      continuousAt_const.add ((continuousAt_id.div
        (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
        (by simp)).smul continuousAt_const)
    simpa [f] using hc.tendsto
  have hfP : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ P :=
    (tendsto_nhdsWithin_iff.mpr ⟨hftend, Eventually.of_forall hfspan⟩).eventually
      (Mei.mem_nhdsWithin_affineSpan_of_mem_intrinsicInterior hq)
  have hlt : ∀ᶠ t : ℝ in 𝓝 0, t * a < 1 := by
    exact (continuousAt_id.mul continuousAt_const).eventually
      (gt_mem_nhds (by simp : (0 : ℝ) * a < 1))
  filter_upwards [hfP.filter_mono nhdsWithin_le_nhds,
    hlt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hta htpos
  have hden : 1 - t * a ≠ 0 := by linarith
  have heq : (t * a) • x + (1 - t * a) • f t = q + t • v := by
    dsimp only [f]
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hden]
    dsimp only [w]
    module
  rw [← heq]
  exact hQ.combo_interior_self_mem_interior hx (hPQ ht) (mul_pos htpos ha)
    (by linarith) (by ring)

/-- If the direction of a set contains the kernel of a functional, every positive
ray from its relative interior enters any convex superset having an interior point
on the positive side. -/
theorem eventually_add_smul_mem_interior_of_ker_le {P Q : Set V} (hQ : Convex ℝ Q)
    (hPQ : P ⊆ Q) (ν : V →ₗ[ℝ] ℝ)
    (hν : ν.ker ≤ (affineSpan ℝ P).direction) {q x v : V}
    (hq : q ∈ intrinsicInterior ℝ P) (hx : x ∈ interior Q)
    (hxpos : 0 < ν (x - q)) (hvpos : 0 < ν v) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, q + t • v ∈ interior Q := by
  apply hQ.eventually_add_smul_mem_interior hPQ hq hx (div_pos hvpos hxpos)
  apply hν
  rw [LinearMap.mem_ker]
  simp only [map_sub, map_smul, smul_eq_mul]
  rw [map_sub] at hxpos
  field_simp [hxpos.ne']
  ring

/-- A convex set meeting `P` and missing its relative boundary meets the affine span
of `P` only inside `P`. Neither set needs to be closed. -/
theorem inter_affineSpan_subset {P U : Set V} (hU : Convex ℝ U) (hUP : (U ∩ P).Nonempty)
    (hfr : Disjoint U (intrinsicFrontier ℝ P)) : U ∩ affineSpan ℝ P ⊆ P := by
  rintro z ⟨hzU, hzA⟩
  obtain ⟨w, hwU, hwP⟩ := hUP
  let g : unitInterval → affineSpan ℝ P := fun r =>
    ⟨AffineMap.lineMap w z (r : ℝ), AffineMap.lineMap_mem _ (subset_affineSpan ℝ P hwP) hzA⟩
  have hg : Continuous g :=
    (AffineMap.lineMap_continuous.comp continuous_subtype_val).subtype_mk _
  have hloc : IsLocallyConstant fun r => (g r : V) ∈ P := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun r => ?_
    have hr := Mei.eventually_mem_iff_of_notMem_intrinsicFrontier (x := g r) rfl
      (Set.disjoint_left.mp hfr (hU.lineMap_mem hwU hzU r.property))
    filter_upwards [(hg.tendsto r).eventually hr] with r' hr'
    exact propext hr'
  simpa [g] using (hloc.apply_eq_of_preconnectedSpace 1 0).mpr (by simpa [g] using hwP)

end Convex
