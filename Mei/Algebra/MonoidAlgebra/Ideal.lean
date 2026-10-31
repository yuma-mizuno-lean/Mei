/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Coefficient ideal bounds in additive monoid algebras

Multiplication convolves coefficients, so coefficients in ideals `I` and `J`
produce coefficients in `I * J`. In particular, raising a monoid polynomial
whose coefficients lie in `I` to the power `n` puts every coefficient in `I ^ n`.
These bounds do not require cancellation or unique decompositions in the monoid.
-/

public section

namespace AddMonoidAlgebra

variable {R M : Type*} [Semiring R]

/-- Coefficientwise ideal bounds multiply under convolution. -/
theorem coeff_mul_mem_mul [Add M] {I J : Ideal R} {x y : R[M]}
    (hx : ∀ m, x.coeff m ∈ I) (hy : ∀ m, y.coeff m ∈ J) (m : M) :
    (x * y).coeff m ∈ I * J := by
  classical
  rw [coeff_mul, Finsupp.sum]
  refine (I * J).sum_mem fun i _ => ?_
  rw [Finsupp.sum]
  refine (I * J).sum_mem fun j _ => ?_
  split_ifs
  · exact Ideal.mul_mem_mul (hx i) (hy j)
  · exact (I * J).zero_mem

/-- A power of a polynomial with coefficients in `I` has coefficients in the
corresponding power of `I`. -/
theorem coeff_pow_mem_pow [AddMonoid M] {I : Ideal R} {x : R[M]}
    (hx : ∀ m, x.coeff m ∈ I) (n : ℕ) (m : M) :
    (x ^ n).coeff m ∈ I ^ n := by
  induction n generalizing m with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ n ih =>
    rw [pow_succ, Submodule.pow_succ]
    exact coeff_mul_mem_mul ih hx m

end AddMonoidAlgebra
