/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Faces of finitely generated cones are exposed

Apply Tucker's theorem to a finite generating family together with the negatives
of its generators lying in the face. The resulting nonnegative relation has its
positive part in the face. The face property forces every coefficient of an
outside generator to vanish, so Tucker's functional is strictly positive there.
It vanishes on the face generators because both signs occur in the family.

This is an algebraic argument over any linearly ordered field. Neither finite
dimensionality, topological closedness, nor salience is required.
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
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hfgen x hx
    | zero => simp
    | add x y _ _ ix iy => simpa only [map_add] using add_nonneg ix iy
    | smul r x _ ix =>
      change 0 ≤ f ((r : K) • x)
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg r.property ix
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
    change -f y ≤ -f x
    rw [hxzero, neg_zero]
    exact neg_nonpos.mpr (hf y hy)
  · rintro ⟨hxC, hmax⟩
    have hmaxzero := hmax 0 C.zero_mem
    have hlx : 0 ≤ -f x := by
      change (-f) 0 ≤ (-f) x at hmaxzero
      simpa only [map_zero, LinearMap.neg_apply] using hmaxzero
    exact (hzero x hxC).mp (le_antisymm (neg_nonneg.mp hlx) (hf x hxC))

end PointedCone.IsFaceOf
