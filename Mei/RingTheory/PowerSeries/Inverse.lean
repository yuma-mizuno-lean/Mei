/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.PowerSeries.Geometric
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Coefficients of inverse linear series

The inverse of `1 + a X` has coefficient `(-a)^j` in degree `j`, over an
arbitrary associative ring. This computes the factors in inverse ray
multipliers without requiring `a` to be invertible.

The proof uses `TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one`
and uniqueness of a two-sided inverse.
-/

public section

namespace PowerSeries

/-- The inverse linear series has geometric coefficients, even when its slope
is a zero divisor or is not a unit. -/
@[simp]
theorem coeff_invOfUnit_one_add_C_mul_X {R : Type*} [Ring R] (a : R) (j : ℕ) :
    coeff j (invOfUnit (1 + C a * X) 1) = (-a) ^ j := by
  have hgeom : mk (fun n => (-a) ^ n) * (1 + C a * X) = 1 := by
    simpa only [map_neg, neg_mul, sub_neg_eq_add] using
      TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (-a)
  have heq := left_inv_eq_right_inv hgeom
    (mul_invOfUnit (1 + C a * X) 1 (by simp))
  exact (congrArg (coeff j) heq).symm.trans (coeff_mk _ _)

end PowerSeries
