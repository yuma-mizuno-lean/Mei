/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.PowerSeries.Nilpotent.Basic
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Evaluating the logarithm at a nilpotent element

The algebra evaluation of the scalar series `log(1 + X)` at a nilpotent element
is the finite logarithm of one plus that element. This works in associative
rational algebras and connects `PowerSeries.nilpotentAeval` with
`IsNilpotent.log_eq_sum`.
-/

public section

namespace PowerSeries

variable {R A : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [Algebra ℚ A] [IsScalarTower ℚ R A]

/-- Evaluating the formal logarithm at a nilpotent element gives the finite
logarithm of one plus that element. -/
@[simp]
theorem nilpotentAeval_log {x : A} (hx : IsNilpotent x) :
    nilpotentAeval hx (log R) = IsNilpotent.log (1 + x) := by
  let n := hx.choose
  have hn : x ^ n = 0 := hx.choose_spec
  rw [nilpotentAeval_eq_sum _ hn, IsNilpotent.log_eq_sum (n := n) (by simpa using hn)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = 0
  · simp [hi]
  · simp only [coeff_log, hi, ite_false, add_sub_cancel_left]
    exact IsScalarTower.algebraMap_smul R _ _

end PowerSeries
