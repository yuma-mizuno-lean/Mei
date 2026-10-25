/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Faces of finitely generated cones are exposed

Every face of a finitely generated cone is the zero set within the cone of a
nonnegative linear functional. This gives supporting hyperplane descriptions,
allowing the zero functional for the full face.
`PointedCone.IsFaceOf.exists_nonneg_linear_inf_ker` expresses this as
an intersection with the functional's kernel, while
`PointedCone.IsFaceOf.exists_nonneg_linear_zero_iff` gives the pointwise criterion.
These algebraic results hold over any linearly ordered field, without finite
dimensionality, topological closedness, or salience assumptions.

In a finite-dimensional real normed space,
`PointedCone.IsFaceOf.isExposed_of_fg` supplies Mathlib's continuous-functional
predicate `IsExposed`, using the negative functional for its maximization convention.
The algebraic construction uses Tucker's theorem and the face property.
Conversely, `IsExposed.exists_isFaceOf_coe_eq` identifies every nonempty exposed
subset of a real cone with a cone face, without a finite-generation assumption.
-/

public section

namespace PointedCone.IsFaceOf

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] {C F : PointedCone K V}

/-- Every face of a finitely generated cone is cut out by a linear functional
nonnegative on the cone. Cones with lineality and the full face are included. -/
theorem exists_nonneg_linear_inf_ker (hF : F.IsFaceOf C) (hC : C.FG) :
    ∃ f : Module.Dual K V, (∀ x ∈ C, 0 ≤ f x) ∧
      C ⊓ PointedCone.ofSubmodule (LinearMap.ker f) = F := by
  classical
  obtain ⟨s, hs⟩ := hC
  let J := {j : s // (j : V) ∈ F}
  let a : s ⊕ J → V := Sum.elim Subtype.val (fun j => -(j.val : V))
  obtain ⟨c, f, hc, hsum, hf, hpos⟩ :=
    TauCeti.exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos (K := K) a
  have hsC : (s : Set V) ⊆ C := by
    rw [← hs]
    exact Submodule.subset_span
  have hsumF : (∑ j : s, c (.inl j) • (j : V)) ∈ F := by
    have heq : (∑ j : s, c (.inl j) • (j : V)) =
        ∑ j : J, c (.inr j) • (j.val : V) := by
      have h := hsum
      simp only [Fintype.sum_sum_type, a, Sum.elim_inl, Sum.elim_inr, smul_neg,
        Finset.sum_neg_distrib] at h
      exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)
    rw [heq]
    exact F.sum_mem fun j _ => PointedCone.smul_mem F (hc (.inr j)) j.property
  have houtside (j : s) (hj : (j : V) ∉ F) : c (.inl j) = 0 := by
    by_contra hne
    have hp : 0 < c (.inl j) := lt_of_le_of_ne (hc (.inl j)) (Ne.symm hne)
    exact hj (hF.mem_of_sum_smul_mem
      (fun k : s => hsC k.property) (fun k => hc (.inl k)) hsumF j hp)
  have hfacezero (j : s) (hj : (j : V) ∈ F) : f (j : V) = 0 := by
    have hp : 0 ≤ f (j : V) := hf (.inl j)
    have hn : 0 ≤ -f (j : V) := by
      simpa only [a, Sum.elim_inr, map_neg] using hf (.inr ⟨j, hj⟩)
    exact le_antisymm (neg_nonneg.mp hn) hp
  have hfgen : ∀ x ∈ s, 0 ≤ f x := fun x hx => hf (.inl ⟨x, hx⟩)
  have hzgen : ∀ x ∈ s, f x = 0 ↔ x ∈ F := by
    intro x hx
    constructor
    · intro hzero
      by_contra hxF
      have hp := hpos (.inl ⟨x, hx⟩)
      have hc0 := houtside ⟨x, hx⟩ hxF
      simp only [hc0, zero_add, a, Sum.elim_inl, hzero, lt_self_iff_false] at hp
    · exact hfacezero ⟨x, hx⟩
  have hfC : ∀ x ∈ C, 0 ≤ f x := by
    have hdual : f ∈ PointedCone.dual (Module.Dual.eval K V) (s : Set V) :=
      fun _ hx => hfgen _ hx
    rw [← PointedCone.dual_hull, PointedCone.hull, hs] at hdual
    exact fun _ hx => hdual hx
  exact ⟨f, hfC, PointedCone.inf_ker_eq_of_eq_hull hs.symm hF hfgen hzgen⟩

/-- The exposing functional vanishes precisely on the chosen face, among all
points of the original finitely generated cone. -/
theorem exists_nonneg_linear_zero_iff (hF : F.IsFaceOf C) (hC : C.FG) :
    ∃ f : Module.Dual K V, (∀ x ∈ C, 0 ≤ f x) ∧
      ∀ x ∈ C, f x = 0 ↔ x ∈ F := by
  obtain ⟨f, hf, heq⟩ := hF.exists_nonneg_linear_inf_ker hC
  refine ⟨f, hf, fun x hx => ?_⟩
  constructor
  · intro hzero
    rw [← heq]
    exact ⟨hx, hzero⟩
  · intro hxF
    rw [← heq] at hxF
    exact hxF.2

end PointedCone.IsFaceOf

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {C : PointedCone ℝ V} {S : Set V}

/-- Every nonempty exposed subset of a pointed cone is the carrier of a cone face.
No finite-generation or closedness assumption is needed in this direction. -/
theorem exists_isFaceOf_coe_eq (hS : IsExposed ℝ (C : Set V) S) (hne : S.Nonempty) :
    ∃ F : PointedCone ℝ V, F.IsFaceOf C ∧ (F : Set V) = S := by
  obtain ⟨l, hl⟩ := hS hne
  have hzero (x : V) (hx : x ∈ S) : l x = 0 := by
    have hm : x ∈ {x ∈ C | ∀ y ∈ C, l y ≤ l x} := hl ▸ hx
    have h₀ := hm.2 0 C.zero_mem
    have h₂ := hm.2 (2 • x) (C.smul_mem (by norm_num : (0 : ℝ) ≤ 2) hm.1)
    simp only [map_zero] at h₀
    simp only [map_smul, smul_eq_mul] at h₂
    linarith
  obtain ⟨p, hp⟩ := hne
  have hnonpos (x : V) (hx : x ∈ C) : l x ≤ 0 := by
    have hm : p ∈ {x ∈ C | ∀ y ∈ C, l y ≤ l x} := hl ▸ hp
    simpa only [hzero p hp] using hm.2 x hx
  let f : Module.Dual ℝ V := -l.toLinearMap
  have hf : ∀ x ∈ C, 0 ≤ f x := fun x hx => neg_nonneg.mpr (hnonpos x hx)
  refine ⟨C ⊓ PointedCone.ofSubmodule (LinearMap.ker f),
    PointedCone.isFaceOf_inf_ker hf, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    have hxzero : l x = 0 := neg_eq_zero.mp hfx
    rw [hl]
    exact ⟨hx, fun y hy => (hnonpos y hy).trans_eq hxzero.symm⟩
  · intro hx
    exact ⟨hS.subset hx, by simpa [f] using hzero x hx⟩

end IsExposed

namespace PointedCone.IsFaceOf

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C F : PointedCone ℝ V}

/-- Over a finite-dimensional real normed space, every face of a finitely
generated cone is exposed in Mathlib's continuous-functional sense. -/
theorem isExposed_of_fg (hF : F.IsFaceOf C) (hC : C.FG) :
    IsExposed ℝ (C : Set V) (F : Set V) := by
  intro _
  obtain ⟨f, hf, hzero⟩ := hF.exists_nonneg_linear_zero_iff hC
  let l : V →L[ℝ] ℝ := ⟨-f, (-f).continuous_of_finiteDimensional⟩
  refine ⟨l, ?_⟩
  ext x
  constructor
  · intro hxF
    refine ⟨hF.le hxF, fun y hy => ?_⟩
    have hxzero := (hzero x (hF.le hxF)).mpr hxF
    simp only [l, ContinuousLinearMap.coe_mk', LinearMap.neg_apply]
    rw [hxzero, neg_zero]
    exact neg_nonpos.mpr (hf y hy)
  · rintro ⟨hxC, hmax⟩
    have hmaxzero := hmax 0 C.zero_mem
    have hlx : 0 ≤ -f x := by
      simpa only [l, ContinuousLinearMap.coe_mk', LinearMap.neg_apply, map_zero, neg_zero]
        using hmaxzero
    exact (hzero x hxC).mp (le_antisymm (neg_nonneg.mp hlx) (hf x hxC))

end PointedCone.IsFaceOf
