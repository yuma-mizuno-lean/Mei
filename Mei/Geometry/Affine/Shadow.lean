/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Shadows of a set along a direction

The endpoint discriminant of the closed-chart construction is assembled from the affine
spans of the shadows of the singular-support cells along the backward rays of the
admissible directions: the shadow of a set `σ` along `w` consists of the points reached
by moving from a point of `σ` backwards along the ray `-ℝ≥0 • w`.

The shadow contains the set and its translate by `-w`, is monotone, is unchanged by
repeating it, is convex when the set is convex, and — the form in which the
discriminant uses it — spans the same affine subspace as the set together with its
translate by `-w`. So the span of a shadow can be computed from two copies of the set,
and a full-dimensional shadow contributes the ambient space.

The construction uses only the real vector-space structure; no polyhedrality,
closedness or boundedness of `σ` is assumed.
-/

public section

noncomputable section

open Set

namespace Mei

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The shadow of a set along a direction `w`: the points reached from a point of the
set by moving backwards along the ray `-ℝ≥0 • w`. -/
def shadow (σ : Set V) (w : V) : Set V :=
  {v | ∃ s ∈ σ, ∃ t : ℝ, 0 ≤ t ∧ v = s - t • w}

/-- Membership in a shadow. -/
@[simp]
theorem mem_shadow {σ : Set V} {w v : V} :
    v ∈ shadow σ w ↔ ∃ s ∈ σ, ∃ t : ℝ, 0 ≤ t ∧ v = s - t • w := (Iff.rfl)

/-- A set is contained in its shadow. -/
theorem subset_shadow (σ : Set V) (w : V) : σ ⊆ shadow σ w :=
  fun s hs => ⟨s, hs, 0, le_rfl, by rw [zero_smul, sub_zero]⟩

/-- The translate of a set by `-w` lies in its shadow along `w`. -/
theorem image_sub_subset_shadow (σ : Set V) (w : V) :
    (fun s => s - w) '' σ ⊆ shadow σ w := by
  rintro v ⟨s, hs, rfl⟩
  exact ⟨s, hs, 1, zero_le_one, by rw [one_smul]⟩


/-- The shadow is the set of points that reach the set by a nonnegative multiple of `w`:
`y ∈ shadow σ w` exactly when `y + t • w ∈ σ` for some `t ≥ 0`. This is the form in which
`Mei.Convex.isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem` states polyhedrality of the
same construction. -/
theorem shadow_eq_setOf_exists_nonneg_add_smul_mem (σ : Set V) (w : V) :
    shadow σ w = {y | ∃ t : ℝ, 0 ≤ t ∧ y + t • w ∈ σ} := by
  ext y
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨t, ht, ?_⟩
    have h : s - t • w + t • w = s := by abel
    rwa [h]
  · rintro ⟨t, ht, h⟩
    exact ⟨y + t • w, h, t, ht, by abel⟩

/-- Shadows are monotone in the set. -/
theorem shadow_mono {σ τ : Set V} (h : σ ⊆ τ) (w : V) : shadow σ w ⊆ shadow τ w := by
  rintro v ⟨s, hs, t, ht, rfl⟩
  exact ⟨s, h hs, t, ht, rfl⟩

/-- The empty set has empty shadow. -/
@[simp]
theorem shadow_empty (w : V) : shadow (∅ : Set V) w = ∅ := by
  ext v
  simp only [mem_shadow, mem_empty_iff_false, false_and, exists_false]

/-- A union of shadows is the shadow of the union. -/
@[simp]
theorem shadow_union (σ τ : Set V) (w : V) :
    shadow (σ ∪ τ) w = shadow σ w ∪ shadow τ w := by
  ext v
  constructor
  · rintro ⟨s, hs | hs, t, ht, rfl⟩
    · exact Or.inl ⟨s, hs, t, ht, rfl⟩
    · exact Or.inr ⟨s, hs, t, ht, rfl⟩
  · rintro (⟨s, hs, t, ht, rfl⟩ | ⟨s, hs, t, ht, rfl⟩)
    · exact ⟨s, Or.inl hs, t, ht, rfl⟩
    · exact ⟨s, Or.inr hs, t, ht, rfl⟩

/-- The shadow along the zero direction is the set itself. -/
@[simp]
theorem shadow_zero (σ : Set V) : shadow σ (0 : V) = σ := by
  refine le_antisymm ?_ (subset_shadow σ 0)
  rintro v ⟨s, hs, t, ht, rfl⟩
  simpa using hs

/-- A shadow is unchanged by taking its shadow again. -/
@[simp]
theorem shadow_shadow (σ : Set V) (w : V) : shadow (shadow σ w) w = shadow σ w := by
  refine le_antisymm ?_ (subset_shadow _ _)
  rintro v ⟨s, ⟨s', hs', t', ht', rfl⟩, t, ht, rfl⟩
  refine ⟨s', hs', t' + t, add_nonneg ht' ht, ?_⟩
  rw [add_smul]
  abel

/-- The shadow of a convex set is convex. -/
theorem convex_shadow {σ : Set V} (hσ : Convex ℝ σ) (w : V) :
    Convex ℝ (shadow σ w) := by
  rintro v ⟨s, hs, t, ht, rfl⟩ u ⟨s', hs', t', ht', rfl⟩ a b ha hb hab
  refine ⟨a • s + b • s', hσ hs hs' ha hb hab, a * t + b * t',
    add_nonneg (mul_nonneg ha ht) (mul_nonneg hb ht'), ?_⟩
  module


/-- The shadow spans the same affine subspace as the set together with its translate by
`-w`: every shadow point is an affine combination of `s` and `s - w`, and conversely both
copies of the set lie in the shadow. -/
theorem affineSpan_shadow (σ : Set V) (w : V) :
    affineSpan ℝ (shadow σ w) = affineSpan ℝ (σ ∪ (fun s => s - w) '' σ) := by
  refine le_antisymm ?_ ?_
  · rw [affineSpan_le]
    rintro v ⟨s, hs, t, ht, rfl⟩
    set A := affineSpan ℝ (σ ∪ (fun s => s - w) '' σ) with hA
    have hs' : s ∈ A := subset_affineSpan ℝ _ (Or.inl hs)
    have hsw : s - w ∈ A := subset_affineSpan ℝ _ (Or.inr ⟨s, hs, rfl⟩)
    have hdir : -w ∈ A.direction := by
      have h := AffineSubspace.vsub_mem_direction hsw hs'
      simpa using h
    have hvadd : t • (-w) + s ∈ A :=
      AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hdir) hs'
    have hrew : t • (-w) + s = s - t • w := by
      rw [smul_neg]
      abel
    rwa [hrew] at hvadd
  · rw [affineSpan_le]
    intro v hv
    rcases hv with hv | hv
    · exact subset_affineSpan ℝ _ (subset_shadow σ w hv)
    · exact subset_affineSpan ℝ _ (image_sub_subset_shadow σ w hv)

end Mei

end
