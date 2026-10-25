/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Division comparisons with denominators of opposite signs

Clearing a negative and a positive denominator reverses one inequality. This
comparison is useful when matching lower and upper bounds in linear systems.
-/

public section

namespace Mei

/-- Compare fractions with a negative left denominator and a positive right denominator. -/
theorem div_le_div_iff_of_neg_pos {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b c d : K} (ha : a < 0) (hc : 0 < c) :
    b / a ≤ d / c ↔ a * d ≤ c * b := by
  rw [div_le_iff_of_neg ha, div_mul_eq_mul_div, div_le_iff₀ hc]
  simp only [mul_comm]

end Mei
