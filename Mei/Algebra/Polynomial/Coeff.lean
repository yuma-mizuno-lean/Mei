/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Coefficients of finite generating functions

Extract coefficients from finite sums of weighted monomials, and convolve such sums with
an arbitrary polynomial using Mathlib's coefficient multiplication formula.
-/

public section

namespace Polynomial

open Finset

/-- The coefficient of a filtered finite generating function is the weight of its level set. -/
theorem coeff_sum_C_mul_X_pow {ι R : Type*} [Semiring R] (s : Finset ι) (w : ι → R)
    (P : ι → Prop) [DecidablePred P] (a : ι → ℕ) (n : ℕ) :
    (∑ i ∈ s with P i, C (w i) * X ^ a i).coeff n =
      ∑ i ∈ s with P i ∧ a i = n, w i := by
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  simp only [sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases hP : P i <;> by_cases ha : a i = n
  all_goals simp [hP, ha, eq_comm (a := n) (b := a i)]

/-- Multiplication by a polynomial convolves its coefficients with the weighted level sets
of a filtered finite generating function. -/
theorem coeff_mul_sum_C_mul_X_pow {ι R : Type*} [Semiring R] (Q : R[X]) (s : Finset ι)
    (w : ι → R) (P : ι → Prop) [DecidablePred P] (a : ι → ℕ) (n : ℕ) :
    (Q * ∑ i ∈ s with P i, C (w i) * X ^ a i).coeff n =
      ∑ k ∈ range (n + 1), Q.coeff k * ∑ i ∈ s with P i ∧ a i = n - k, w i := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_sum_C_mul_X_pow]

end Polynomial
