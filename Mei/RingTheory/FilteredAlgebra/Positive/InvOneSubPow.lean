/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.RingTheory.FilteredAlgebra.Positive.PowerSeries
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Positivity of inverse powers of `1 - x`

Let `x` be an element of the first completed ideal of a filtered algebra. Evaluating
Mathlib's `PowerSeries.invOneSubPow R d`, the inverse of `(1 - X) ^ d`, at `x` inverts
`(1 - x) ^ d` (`TauCeti.AlgFiltration.completedAeval_invOneSubPow_mul_one_sub_pow`). The
coefficients of `PowerSeries.invOneSubPow R d` are natural numbers, so if `x` is positive for a
subsemiring `P`, then so is this inverse
(`TauCeti.AlgFiltration.IsPositive.completedAeval_invOneSubPow`,
`TauCeti.AlgFiltration.IsPositive.inv_of_val_eq_one_sub_pow`). Unlike
`TauCeti.AlgFiltration.IsPositive.inv_of_val_eq_one_add`, which inverts `1 + x`, no hypothesis on
`P` beyond being a subsemiring is needed.
-/

public section

namespace TauCeti.AlgFiltration

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B] {F : AlgFiltration B}
  {P : Subsemiring B}

/-- Evaluating the inverse of `(1 - X) ^ d` at `x` inverts `(1 - x) ^ d`. -/
theorem completedAeval_invOneSubPow_mul_one_sub_pow (x : F.completionIdeal 1) (d : ℕ) :
    F.completedAeval x (PowerSeries.invOneSubPow R d : PowerSeries R) *
      (1 - (x : F.completion)) ^ d = 1 := by
  rw [← F.completedAeval_X (R := R) x, ← map_one (F.completedAeval (R := R) x), ← map_sub,
    ← map_pow, ← map_mul, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow, Units.inv_eq_val_inv,
    Units.mul_inv, map_one]

/-- The inverse of `(1 - X) ^ d` evaluates at a positive element of the first completed ideal
to a positive element. -/
theorem IsPositive.completedAeval_invOneSubPow {x : F.completionIdeal 1}
    (hx : F.IsPositive P (x : F.completion)) (d : ℕ) :
    F.IsPositive P (F.completedAeval x (PowerSeries.invOneSubPow R d : PowerSeries R)) := by
  cases d with
  | zero =>
    rw [PowerSeries.invOneSubPow_zero, Units.val_one, map_one]
    exact isPositive_one
  | succ d =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    exact hx.completedAeval fun i => by simp

/-- If `x` is a positive element of the first completed ideal, then the inverse of the unit
`(1 - x) ^ d` is positive. -/
theorem IsPositive.inv_of_val_eq_one_sub_pow {x : F.completionIdeal 1}
    (hx : F.IsPositive P (x : F.completion)) (d : ℕ) {U : F.completionˣ}
    (hU : (U : F.completion) = (1 - x) ^ d) :
    F.IsPositive P ((U⁻¹ : F.completionˣ) : F.completion) := by
  have h := F.completedAeval_invOneSubPow_mul_one_sub_pow (R := ℤ) x d
  rw [← hU] at h
  rw [Units.inv_eq_of_mul_eq_one_left h]
  exact hx.completedAeval_invOneSubPow d

end TauCeti.AlgFiltration
