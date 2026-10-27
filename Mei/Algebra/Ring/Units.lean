/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Units

/-!
# Units and power differences

Invertibility of a difference of powers of a unit and its inverse implies
invertibility of the corresponding even-power difference from one.
-/

public section

namespace Units

/-- Multiplication by a power of a unit converts an invertible difference of
opposite powers into an invertible even-power difference from one. -/
theorem isUnit_sq_pow_sub_one {R : Type*} [Ring R] (q : Rˣ) (n : ℕ)
    (h : IsUnit ((q : R) ^ n - ((q⁻¹ : Rˣ) : R) ^ n)) :
    IsUnit (((q : R) ^ 2) ^ n - 1) := by
  have hinv : (q : R) ^ n * ((q⁻¹ : Rˣ) : R) ^ n = 1 := by
    rw [← q.commute_coe_inv.mul_pow]
    simp
  have he : (q : R) ^ n * ((q : R) ^ n - ((q⁻¹ : Rˣ) : R) ^ n) =
      ((q : R) ^ 2) ^ n - 1 := by
    rw [mul_sub, hinv, ← pow_add, ← Nat.two_mul, pow_mul]
  rw [← he]
  exact (q.isUnit.pow n).mul h

end Units
