/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Homogenization.Inequalities
import Mathlib.Tactic.Linarith

/-!
# Empty presentations and homogenization

The inconsistent presentations `1 ≤ 0` and `x ≤ 0 ∧ 1 - x ≤ 0` have the same
empty carrier, but homogenizing their rows gives different cones. The first
gives the whole height-zero line; the second gives only the origin. The actual
homogenization, defined from the carrier, gives the origin in both cases.
-/

public section

open ContinuousAffineMap Set

namespace Mei.Convex

/-- The inconsistent constant row defining an empty subset of the real line. -/
def emptyConstantRow : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1

/-- Two incompatible upper bounds defining the empty subset of the real line. -/
def emptyOpposedRows (b : Bool) : ℝ →ᴬ[ℝ] ℝ :=
  if b then ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ
  else ContinuousAffineMap.id ℝ ℝ

/-- The constant inconsistent presentation has empty carrier. -/
theorem emptyConstantRow_carrier : {x : ℝ | emptyConstantRow x ≤ 0} = ∅ := by
  ext x
  simp [emptyConstantRow]

/-- The two opposed inequalities also have empty carrier. -/
theorem emptyOpposedRows_carrier : {x : ℝ | ∀ b, emptyOpposedRows b x ≤ 0} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hx
  have h₀ := hx false
  have h₁ := hx true
  simp [emptyOpposedRows] at h₀ h₁
  linarith

/-- Naively homogenizing the constant row leaves every horizontal direction. -/
theorem homogeneousInequalityCone_emptyConstantRow :
    (homogeneousInequalityCone (fun _ : Unit => emptyConstantRow) : Set (ℝ × ℝ)) =
      {z | z.2 = 0} := by
  ext z
  simp only [SetLike.mem_coe, mem_homogeneousInequalityCone, Set.mem_ofPred_eq]
  have hr : homogenizedInequality emptyConstantRow z = z.2 := by
    rcases z with ⟨x, t⟩
    rw [homogenizedInequality_apply, ← sub_zero x, ← vsub_eq_sub,
      AffineMap.linear_apply_vsub]
    simp [emptyConstantRow]
  simp only [hr, forall_const]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩

/-- Naively homogenizing the opposed rows instead leaves only the origin. -/
theorem homogeneousInequalityCone_emptyOpposedRows :
    homogeneousInequalityCone emptyOpposedRows = ⊥ := by
  ext z
  simp only [mem_homogeneousInequalityCone, Submodule.mem_bot]
  have h₀ : homogenizedInequality (emptyOpposedRows false) z = z.1 := by
    rcases z with ⟨x, t⟩
    rw [homogenizedInequality_apply, ← sub_zero x, ← vsub_eq_sub,
      AffineMap.linear_apply_vsub]
    simp [emptyOpposedRows]
  have h₁ : homogenizedInequality (emptyOpposedRows true) z = z.2 - z.1 := by
    rcases z with ⟨x, t⟩
    rw [homogenizedInequality_apply, ← sub_zero x, ← vsub_eq_sub,
      AffineMap.linear_apply_vsub]
    simp [emptyOpposedRows, sub_eq_add_neg, add_comm]
  constructor
  · rintro ⟨ht, hz⟩
    have hx := hz false
    have hy := hz true
    rw [h₀] at hx
    rw [h₁] at hy
    apply Prod.ext <;> dsimp <;> linarith
  · rintro rfl
    simp

/-- The actual homogenization of either inconsistent presentation is the zero cone. -/
theorem homogenization_empty_presentations :
    homogenization {x : ℝ | emptyConstantRow x ≤ 0} = ⊥ ∧
      homogenization {x : ℝ | ∀ b, emptyOpposedRows b x ≤ 0} = ⊥ := by
  rw [emptyConstantRow_carrier, emptyOpposedRows_carrier]
  simp

end Mei.Convex
