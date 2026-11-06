/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith

/-!
# Eventual affine inequalities along rays

An affine inequality eventually holds along a ray over a linearly ordered field
exactly when its linear part decreases strictly, or is constant and the inequality
holds at the base.
For a finite nonincreasing family, only the tangential rows constrain eventual
admission. These criteria need no topology on the domain and supply the algebraic
step in polyhedral source-admission arguments.
-/

public section

namespace AffineMap

variable {𝕜 V ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- An affine inequality holds eventually along a ray precisely when it decreases
strictly, or is constant along the ray and already holds at its base point. -/
@[simp↓] -- Normalize the affine ray before the generic atTop eventuality expands.
theorem eventually_apply_add_smul_le_iff (g : V →ᵃ[𝕜] 𝕜) (x w : V) :
    (∀ᶠ t : 𝕜 in Filter.atTop, g (x + t • w) ≤ 0) ↔
      g.linear w < 0 ∨ g.linear w = 0 ∧ g x ≤ 0 := by
  have heval (t : 𝕜) : g (x + t • w) = g x + g.linear w * t := by
    simpa only [vadd_eq_add, map_smul, smul_eq_mul, mul_comm, add_comm] using
      g.map_vadd x (t • w)
  simp only [heval]
  rcases lt_trichotomy (g.linear w) 0 with hneg | hzero | hpos
  · refine iff_of_true ?_ (Or.inl hneg)
    filter_upwards [Filter.eventually_ge_atTop (-g x / g.linear w)] with t ht
    have := (div_le_iff_of_neg hneg).mp ht
    linarith
  · simp only [hzero, zero_mul, add_zero, Filter.eventually_const, lt_self_iff_false,
      true_and, false_or]
  · have hnot : ¬ ∀ᶠ t : 𝕜 in Filter.atTop, g x + g.linear w * t ≤ 0 := by
      intro he
      obtain ⟨t, ht, hle⟩ := ((Filter.eventually_gt_atTop (-g x / g.linear w)).and he).exists
      have := (div_lt_iff₀ hpos).mp ht
      nlinarith
    simp [hnot, hpos.ne', hpos.not_gt]

/-- When all inequalities are nonincreasing along a ray, exactly the tangential
ones constrain eventual admission. Strictly decreasing rows impose no condition
on the base point. -/
theorem eventually_forall_apply_add_smul_le_iff_of_nonpos
    [Finite ι] (g : ι → V →ᵃ[𝕜] 𝕜) (w : V) (hw : ∀ j, (g j).linear w ≤ 0) (x : V) :
    (∀ᶠ t : 𝕜 in Filter.atTop, ∀ j, g j (x + t • w) ≤ 0) ↔
      ∀ j, (g j).linear w = 0 → g j x ≤ 0 := by
  rw [Filter.eventually_all]
  simp only [eventually_apply_add_smul_le_iff]
  constructor
  · intro hx j hj
    rcases hx j with hneg | ⟨_, hle⟩
    · exact (hneg.ne hj).elim
    · exact hle
  · intro hx j
    rcases (hw j).lt_or_eq with hneg | hzero
    · exact Or.inl hneg
    · exact Or.inr ⟨hzero, hx j hzero⟩

end AffineMap
