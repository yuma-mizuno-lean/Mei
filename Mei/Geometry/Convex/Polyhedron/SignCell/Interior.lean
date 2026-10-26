/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.SignCell
public import Mei.Analysis.Convex.Intrinsic

/-!
# Relative interiors of arrangement cells

The relative interior of the closure of a realized cell of a finite affine
arrangement is exactly its strict sign cell. Thus every defining row has a
constant sign on the relative interior, including rows vanishing identically.
This allows constructions defined by signs to descend from points to closed
arrangement cells, even when the cells have lineality or redundant equations.

The proof uses `AffineMap.eq_zero_on_of_mem_intrinsicInterior` to rule out
additional active rows, and Mathlib's `AffineMap.eqOn_affineSpan` to retain
the equality rows in a relative neighborhood.
-/

public section

namespace Mei.Convex

open Set Topology

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  {g : ι → (V →ᴬ[ℝ] ℝ)} {σ : ι → SignType}

/-- A relative interior point of a realized weak sign cell satisfies all its
strict sign conditions. This direction allows infinitely many rows. -/
theorem intrinsicInterior_weakSignCell_subset_signCell
    (hne : (signCell g σ).Nonempty) :
    intrinsicInterior ℝ (weakSignCell g σ) ⊆ signCell g σ := by
  obtain ⟨p, hp⟩ := hne
  intro x hx
  have hxw := mem_weakSignCell.mp (intrinsicInterior_subset hx)
  apply mem_signCell.mpr
  intro j
  have hpj := mem_signCell.mp hp j
  rcases hxw j with ⟨hz, hn, hpos⟩
  cases hs : σ j with
  | zero => simp [hz hs]
  | neg =>
    have hle := hn hs
    have hne : g j x ≠ 0 := by
      intro he
      have hall := (g j).toAffineMap.eq_zero_on_of_mem_intrinsicInterior
        (fun y hy => (mem_weakSignCell.mp hy j).2.1 hs) hx he
      have hp0 : g j p = 0 := hall p (signCell_subset_weakSignCell g σ hp)
      simp [hs, hp0] at hpj
    simpa [hs] using sign_eq_neg_one_iff.mpr (lt_of_le_of_ne hle hne)
  | pos =>
    have hle := hpos hs
    have hne : g j x ≠ 0 := by
      intro he
      have hall := (-g j).toAffineMap.eq_zero_on_of_mem_intrinsicInterior
        (fun y hy => neg_nonpos.mpr ((mem_weakSignCell.mp hy j).2.2 hs)) hx
        (by simpa using he)
      have hp0 : g j p = 0 := neg_eq_zero.mp
        (hall p (signCell_subset_weakSignCell g σ hp))
      simp [hs, hp0] at hpj
    simpa [hs] using sign_eq_one_iff.mpr (lt_of_le_of_ne hle hne.symm)

omit [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] in
/-- Finitely many strict row conditions give a relative neighborhood inside the
weak cell. Equality rows hold throughout its affine span. -/
theorem signCell_subset_intrinsicInterior_weakSignCell [Finite ι] :
    signCell g σ ⊆ intrinsicInterior ℝ (weakSignCell g σ) := by
  intro x hx
  let A := affineSpan ℝ (weakSignCell g σ)
  let xA : A := ⟨x, subset_affineSpan ℝ _ (signCell_subset_weakSignCell g σ hx)⟩
  refine mem_intrinsicInterior.mpr ⟨xA, ?_, rfl⟩
  apply mem_interior_iff_mem_nhds.mpr
  have hrows : ∀ j, ∀ᶠ y : A in 𝓝 xA,
      (σ j = .zero → g j y = 0) ∧ (σ j = .neg → g j y ≤ 0) ∧
        (σ j = .pos → 0 ≤ g j y) := by
    intro j
    have hxj := mem_signCell.mp hx j
    cases hs : σ j with
    | zero =>
      have he : Set.EqOn (g j).toAffineMap (0 : V →ᵃ[ℝ] ℝ)
          (weakSignCell g σ) := fun y hy => (mem_weakSignCell.mp hy j).1 hs
      exact Filter.Eventually.of_forall fun y => by
        have hy := AffineMap.eqOn_affineSpan he y.property
        simpa [hs] using hy
    | neg =>
      have hlt : g j x < 0 := sign_eq_neg_one_iff.mp (by simpa [hs] using hxj)
      have he : ContinuousAt (fun y : A => g j y) xA :=
        ((g j).continuous.comp continuous_subtype_val).continuousAt
      filter_upwards [he.eventually (gt_mem_nhds hlt)] with y hy
      simp [hy.le]
    | pos =>
      have hlt : 0 < g j x := sign_eq_one_iff.mp (by simpa [hs] using hxj)
      have he : ContinuousAt (fun y : A => g j y) xA :=
        ((g j).continuous.comp continuous_subtype_val).continuousAt
      filter_upwards [he.eventually (lt_mem_nhds hlt)] with y hy
      simp [hy.le]
  filter_upwards [Filter.eventually_all.mpr hrows] with y hy
  exact mem_weakSignCell.mpr hy

/-- The relative interior of the closure of a sign cell is precisely its
strict sign locus, including for inconsistent sign assignments. -/
@[simp]
theorem intrinsicInterior_closure_signCell [Finite ι] :
    intrinsicInterior ℝ (closure (signCell g σ)) = signCell g σ := by
  by_cases hne : (signCell g σ).Nonempty
  · rw [closure_signCell hne]
    exact Subset.antisymm (intrinsicInterior_weakSignCell_subset_signCell hne)
      signCell_subset_intrinsicInterior_weakSignCell
  · simp [Set.not_nonempty_iff_eq_empty.mp hne]

/-- At a relative interior point of a realized closed sign cell, a row vanishes
if and only if it vanishes on the whole closed cell. -/
theorem row_eq_zero_iff_forall_of_mem_intrinsicInterior
    {x : V}
    (hx : x ∈ intrinsicInterior ℝ (closure (signCell g σ))) (j : ι) :
    g j x = 0 ↔ ∀ y ∈ closure (signCell g σ), g j y = 0 := by
  have hne : (signCell g σ).Nonempty :=
    closure_nonempty_iff.mp ⟨x, intrinsicInterior_subset hx⟩
  have hxs := intrinsicInterior_weakSignCell_subset_signCell hne
    (by rwa [closure_signCell hne] at hx)
  constructor
  · intro hx0 y hy
    have hs : σ j = .zero := (mem_signCell.mp hxs j).symm.trans
      (sign_eq_zero_iff.mpr hx0)
    rw [closure_signCell hne] at hy
    exact (mem_weakSignCell.mp hy j).1 hs
  · exact fun h => h x (intrinsicInterior_subset hx)

end Mei.Convex
