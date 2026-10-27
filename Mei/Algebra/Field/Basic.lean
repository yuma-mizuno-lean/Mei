/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Factoring a linear combination by a difference of ratios

Over a field, a linear combination with two nonzero factors can be expressed
using the difference of the corresponding ratios. This identifies the zeros
and signs of affine functions in a pencil by their slope levels.
-/

public section

namespace Mei

/-- Factor a linear combination as a product times a difference of ratios,
assuming both denominators are nonzero. -/
theorem mul_add_mul_eq_mul_mul_div_sub {K : Type*} [Field K] {a b l m : K}
    (hl : l ≠ 0) (hb : b ≠ 0) :
    a * l + b * m = b * l * (m / l - -a / b) := by
  field_simp
  ring

end Mei
