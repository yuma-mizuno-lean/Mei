/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.Affine
public import Mei.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Exposed subsets, relative interiors and affine transport

Intersections of exposed subsets are exposed in the intersection of their
ambient sets. An affine equivalence with continuous inverse carries exposed subsets to
exposed subsets. Composing an exposing linear functional with the inverse
linear part preserves all comparisons: the inverse translation contributes
the same additive constant at every point.

An exposed subset meeting the relative interior is the whole ambient set.
Nonempty proper exposed subsets have strictly smaller affine dimension.
The relative-interior statement uses `AffineMap.eq_zero_on_of_mem_intrinsicInterior`.
-/

public section

namespace IsExposed

section Intersections

variable {R V : Type*} [TopologicalSpace R] [Ring R] [PartialOrder R] [IsOrderedRing R]
  [ContinuousAdd R] [AddCommMonoid V] [TopologicalSpace V] [Module R V] {P Q F G : Set V}

/-- Intersections of exposed subsets are exposed in the intersection of their
ambient sets. This includes empty intersections and requires no convexity. -/
theorem inter_inter (hF : IsExposed R P F) (hG : IsExposed R Q G) :
    IsExposed R (P ∩ Q) (F ∩ G) := by
  rintro ⟨p, hpF, hpG⟩
  obtain ⟨l, hl⟩ := hF ⟨p, hpF⟩
  obtain ⟨m, hm⟩ := hG ⟨p, hpG⟩
  have hpL := hl ▸ hpF
  have hpM := hm ▸ hpG
  refine ⟨l + m, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxF, hxG⟩
    have hxL := hl ▸ hxF
    have hxM := hm ▸ hxG
    exact ⟨⟨hxL.1, hxM.1⟩, fun y hy => add_le_add (hxL.2 y hy.1) (hxM.2 y hy.2)⟩
  · rintro x ⟨⟨hxP, hxQ⟩, hxmax⟩
    have hsum := hxmax p ⟨hpL.1, hpM.1⟩
    constructor
    · rw [hl]
      refine ⟨hxP, fun y hy => ?_⟩
      exact (add_le_add_iff_right (m x)).mp
        ((add_le_add (hpL.2 y hy) (hpM.2 x hxQ)).trans hsum)
    · rw [hm]
      refine ⟨hxQ, fun y hy => ?_⟩
      exact (add_le_add_iff_left (l x)).mp
        ((add_le_add (hpL.2 x hxP) (hpM.2 y hy)).trans hsum)

end Intersections

variable {R V W : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
  [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W] [Module R W] {P F : Set V}

/-- An affine equivalence with continuous inverse preserves exposed subsets,
including empty subsets, without any convexity assumption. -/
theorem image_affineEquiv (hF : IsExposed R P F) (e : V ≃ᵃ[R] W)
    (he : Continuous e.symm) : IsExposed R (e '' P) (e '' F) := by
  intro hne
  have hFne : F.Nonempty := by
    obtain ⟨y, x, hx, _⟩ := hne
    exact ⟨x, hx⟩
  obtain ⟨l, hl⟩ := hF hFne
  let T : W →L[R] V := ⟨e.symm.toAffineMap.linear, AffineMap.continuous_linear_iff.mpr he⟩
  let k := l.comp T
  have hval (y : W) : l (e.symm y) = k y + l (e.symm 0) := by
    have hd := congrFun e.symm.toAffineMap.decomp y
    have heq : e.symm y = e.symm.toAffineMap.linear y + e.symm 0 := by
      simpa only [AffineEquiv.coe_toAffineMap, Pi.add_apply] using hd
    rw [heq, map_add]
    rfl
  have hcompare (x y : W) : k x ≤ k y ↔ l (e.symm x) ≤ l (e.symm y) := by
    rw [hval x, hval y, add_le_add_iff_right]
  refine ⟨k, Set.ext fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' := hl ▸ hx
    refine ⟨⟨x, hx'.1, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    apply (hcompare (e w) (e x)).mpr
    simpa only [e.symm_apply_apply] using hx'.2 w hw
  · rintro ⟨⟨x, hx, rfl⟩, hmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, fun w hw => ?_⟩
    have hm := (hcompare (e w) (e x)).mp (hmax (e w) ⟨w, hw, rfl⟩)
    simpa only [e.symm_apply_apply] using hm

/-- An affine equivalence continuous in both directions preserves and reflects
exposure of subsets. -/
theorem image_affineEquiv_iff {e : V ≃ᵃ[R] W}
    (he : Continuous e) (hes : Continuous e.symm) :
    IsExposed R (e '' P) (e '' F) ↔ IsExposed R P F := by
  constructor
  · intro hF
    have hback := hF.image_affineEquiv e.symm he
    have hP : e.symm '' (e '' P) = P := e.toEquiv.symm_image_image P
    have hFset : e.symm '' (e '' F) = F := e.toEquiv.symm_image_image F
    rwa [hP, hFset] at hback
  · intro hF
    exact hF.image_affineEquiv e hes

end IsExposed

namespace IsExposed

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] {P F : Set V}

/-- An exposed subset meeting the relative interior of its ambient set is the whole set.
Neither convexity nor finite dimensionality is required. -/
theorem eq_of_mem_intrinsicInterior (hF : IsExposed ℝ P F) {x : V}
    (hxF : x ∈ F) (hx : x ∈ intrinsicInterior ℝ P) : F = P := by
  obtain ⟨l, hl⟩ := hF ⟨x, hxF⟩
  have hxmax := hl ▸ hxF
  let g : V →ᵃ[ℝ] ℝ := l.toLinearMap.toAffineMap - AffineMap.const ℝ V (l x)
  have hg : ∀ p ∈ P, g p = 0 :=
    g.eq_zero_on_of_mem_intrinsicInterior
      (fun p hp => sub_nonpos.mpr (hxmax.2 p hp)) hx (sub_self _)
  apply Set.Subset.antisymm hF.subset
  intro p hp
  rw [hl]
  exact ⟨hp, fun q hq => (hxmax.2 q hq).trans (le_of_eq (sub_eq_zero.mp (hg p hp)).symm)⟩

end IsExposed

namespace IsExposed

variable {K V : Type*} [Ring K] [PartialOrder K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] {P F : Set V}

/-- An exposed subset with the same affine span as its ambient set is the whole set. -/
theorem eq_of_affineSpan_eq (hF : IsExposed K P F) (hne : F.Nonempty)
    (hspan : affineSpan K F = affineSpan K P) : F = P := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨l, hl⟩ := hF ⟨x, hx⟩
  have hxmax := hl ▸ hx
  have heq : Set.EqOn l.toLinearMap.toAffineMap (AffineMap.const K V (l x)) F := by
    intro y hy
    have hymax := hl ▸ hy
    exact le_antisymm (hxmax.2 y hymax.1) (hymax.2 x hxmax.1)
  have hconst : ∀ y ∈ P, l y = l x := by
    intro y hy
    apply AffineMap.eqOn_affineSpan heq
    rw [hspan]
    exact subset_affineSpan K P hy
  apply Set.Subset.antisymm hF.subset
  intro y hy
  rw [hl]
  exact ⟨hy, fun z hz => le_of_eq ((hconst z hz).trans (hconst y hy).symm)⟩

end IsExposed

namespace IsExposed

variable {K V : Type*} [DivisionRing K] [PartialOrder K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] {P F : Set V}

/-- A nonempty proper exposed face has strictly smaller direction dimension. -/
theorem finrank_direction_lt [FiniteDimensional K V] (hF : IsExposed K P F)
    (hne : F.Nonempty) (hproper : F ≠ P) :
    Module.finrank K (affineSpan K F).direction <
      Module.finrank K (affineSpan K P).direction := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply AffineSubspace.direction_lt_of_nonempty _ (hne.affineSpan K)
  exact lt_of_le_of_ne (affineSpan_mono K hF.subset)
    (fun heq => hproper (hF.eq_of_affineSpan_eq hne heq))

end IsExposed
