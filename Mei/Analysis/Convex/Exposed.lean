/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Algebra.Affine
public import Mei.Analysis.Convex.Intrinsic

/-!
# Exposed subsets, relative interiors and affine transport

Intersections of exposed subsets are exposed in the intersection of their
ambient sets. An affine equivalence with continuous inverse carries exposed subsets to
exposed subsets. Composing an exposing linear functional with the inverse
linear part preserves all comparisons: the inverse translation contributes
the same additive constant at every point.

An exposed subset meeting the relative interior is the whole ambient set.
See also `AffineMap.eq_zero_on_of_mem_intrinsicInterior`.
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

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Subtracting a multiple of a height constant on the base preserves all
comparisons of functional values there, and therefore preserves its maximizers. -/
theorem toExposed_sub_smul_of_eq (l f : V →L[ℝ] ℝ) (P : Set V) (a c : ℝ)
    (hfP : ∀ x ∈ P, f x = c) :
    (l - a • f).toExposed P = l.toExposed P := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    have hm := hmax y hy
    simpa only [sub_apply, smul_apply, smul_eq_mul, hfP x hx, hfP y hy,
      sub_le_sub_iff_right] using hm
  · rintro ⟨hx, hmax⟩
    refine ⟨hx, fun y hy => ?_⟩
    simpa only [sub_apply, smul_apply, smul_eq_mul, hfP x hx, hfP y hy,
      sub_le_sub_iff_right] using hmax y hy

end ContinuousLinearMap

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {P F : Set V}

/-- A nonempty exposed subset with the same affine-direction dimension as its
base is the whole base. This also holds for a nonconvex base. -/
theorem eq_of_finrank_vectorSpan_eq (hF : IsExposed ℝ P F) (hne : F.Nonempty)
    (hdim : Module.finrank ℝ (vectorSpan ℝ F) = Module.finrank ℝ (vectorSpan ℝ P)) :
    F = P := by
  obtain ⟨l, hl⟩ := hF hne
  have hdir := Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hF.subset) hdim
  have hker : vectorSpan ℝ F ≤ LinearMap.ker l.toLinearMap := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨a, ha, b, hb, rfl⟩
    have ha' := hl ▸ ha
    have hb' := hl ▸ hb
    have hab := ha'.2 b hb'.1
    have hba := hb'.2 a ha'.1
    apply LinearMap.mem_ker.mpr
    simpa only [ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] using
      sub_eq_zero.mpr (le_antisymm hba hab)
  apply Set.Subset.antisymm hF.subset
  intro x hx
  obtain ⟨z, hz⟩ := hne
  have hxz := vsub_mem_vectorSpan ℝ hx (hF.subset hz)
  rw [← hdir] at hxz
  have hlxz := hker hxz
  have he : l x = l z := sub_eq_zero.mp (by simpa only [LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] using hlxz)
  have hz' := hl ▸ hz
  rw [hl]
  exact ⟨hx, fun y hy => by simpa only [he] using hz'.2 y hy⟩

end IsExposed
