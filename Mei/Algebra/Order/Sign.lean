/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mei.Algebra.Order.Field.Ray
import Mathlib.Tactic.LinearCombination

/-!
# Signs of small perturbations

In a linearly ordered additive group, adding an element of smaller absolute value does not
change the sign: if `|e| < |a|`, then `sign (a + e) = sign a` and `sign (a - e) = sign a`.

In a linearly ordered field, on the line `a q = b p` with `a ≠ 0`, the sign of `a p + b q` is
`sign a * sign p`.
-/

public section

namespace Mei

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a e : α}

/-- A perturbation of smaller absolute value does not change the sign. -/
theorem sign_add_of_abs_lt (h : |e| < |a|) : SignType.sign (a + e) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [abs_of_neg ha] at h
    have : a + e < 0 := by
      have := le_abs_self e
      calc a + e ≤ a + |e| := add_le_add_right this a
        _ < a + -a := add_lt_add_right h a
        _ = 0 := add_neg_cancel a
    rw [sign_neg ha, sign_neg this]
  · exact absurd h (not_lt.mpr (by simp))
  · rw [abs_of_pos ha] at h
    have : 0 < a + e := by
      have := neg_abs_le e
      calc 0 = a + -a := (add_neg_cancel a).symm
        _ < a + -|e| := add_lt_add_right (neg_lt_neg h) a
        _ ≤ a + e := add_le_add_right this a
    rw [sign_pos ha, sign_pos this]

/-- Subtracting an element of smaller absolute value does not change the sign. -/
theorem sign_sub_of_abs_lt (h : |e| < |a|) : SignType.sign (a - e) = SignType.sign a := by
  rw [sub_eq_add_neg]
  exact sign_add_of_abs_lt (by rwa [abs_neg])

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b p q : K}

/-- On the line `a q = b p` with `a ≠ 0`, the sign of `a p + b q` is `sign a * sign p`. -/
theorem sign_mul_add_mul_of_mul_sub_mul_eq_zero (ha : a ≠ 0) (h : a * q - b * p = 0) :
    SignType.sign (a * p + b * q) = SignType.sign a * SignType.sign p := by
  have hk : a * (a * p + b * q) = (a ^ 2 + b ^ 2) * p := by linear_combination b * h
  have hs := congrArg SignType.sign hk
  rw [sign_mul, sign_mul, sign_pos (sq_add_sq_pos_of_ne_zero_or_ne_zero (.inl ha)),
    one_mul] at hs
  rcases ha.lt_or_gt with ha | ha
  · rw [sign_neg ha] at hs ⊢
    rw [← hs, ← mul_assoc, neg_one_mul, neg_neg, one_mul]
  · rw [sign_pos ha] at hs ⊢
    rw [← hs, one_mul, one_mul]

end Field

end Mei

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The sign of a real linear functional is invariant under strictly positive
real scalar multiplication. -/
theorem sign_pos_smul (f : V →ₗ[ℝ] ℝ) (v : V) {t : ℝ} (ht : 0 < t) :
    SignType.sign (f (t • v)) = SignType.sign (f v) := by
  simp [sign_mul, sign_pos ht]

end LinearMap
