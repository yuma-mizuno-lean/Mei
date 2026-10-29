/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Units

/-!
# Powers of units and power differences

Multiplicative maps preserve integer powers of units.
Invertibility of a difference of powers of a unit and its inverse implies
invertibility of the corresponding even-power difference from one.
-/

public section

namespace Mei

/-- A multiplicative map sends an integer power of a unit to the same power of its image. -/
theorem map_units_zpow {M N F : Type*} [Monoid M] [Monoid N]
    [FunLike F M N] [MonoidHomClass F M N] (f : F) (u : Mˣ) (k : ℤ) :
    f ↑(u ^ k) = ↑(Units.map (f : M →* N) u ^ k) := by
  rw [← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]

end Mei

namespace Units

/-- If `q ^ n - q⁻¹ ^ n` is a unit, then so is `(q ^ 2) ^ n - 1`. -/
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
