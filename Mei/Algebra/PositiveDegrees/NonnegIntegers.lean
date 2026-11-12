/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Monomials over the nonnegative integers

The monoid algebra `A[nonnegIntegers.monoid]` of the nonnegative integers
`TauCeti.PositiveDegrees.nonnegIntegers` is the polynomial ring in one variable. This file names
the natural exponents (`TauCeti.PositiveDegrees.nonnegIntegers.natExponent`) and the variable
`TauCeti.PositiveDegrees.nonnegIntegers.X`, the monomial of exponent `1`, whose powers are the
monomials of natural exponent (`TauCeti.PositiveDegrees.nonnegIntegers.X_pow`).
-/

public section

noncomputable section

namespace TauCeti.PositiveDegrees.nonnegIntegers


open _root_.AddMonoidAlgebra

/-- The natural number `j` as an exponent in the monoid of nonnegative integers. -/
def natExponent (j : ℕ) : nonnegIntegers.monoid :=
  ⟨j, mem_nonnegIntegers_monoid.mpr (Int.natCast_nonneg j)⟩

/-- The exponent `natExponent j` is the integer `j`. -/
@[simp]
theorem coe_natExponent (j : ℕ) : (natExponent j : ℤ) = j :=
  (rfl)

/-- The natural exponent `0` is zero. -/
@[simp]
theorem natExponent_zero : natExponent 0 = 0 :=
  Subtype.ext (by simp)

/-- Natural exponents add as natural numbers. -/
@[simp]
theorem natExponent_add (i j : ℕ) : natExponent i + natExponent j = natExponent (i + j) :=
  Subtype.ext (by simp)

/-- Natural multiples of natural exponents are natural exponents. -/
@[simp]
theorem nsmul_natExponent (i j : ℕ) : i • natExponent j = natExponent (i * j) :=
  Subtype.ext (by simp)

variable (A : Type*) [Semiring A]

/-- The variable of `A[nonnegIntegers.monoid]`: the monomial of exponent `1`. -/
def X : A[nonnegIntegers.monoid] :=
  single (natExponent 1) 1

/-- The variable is the monomial of exponent `1`. -/
theorem X_def : X A = single (natExponent 1) 1 :=
  (rfl)

/-- The powers of the variable are the monomials of natural exponent. -/
@[simp]
theorem X_pow (j : ℕ) : X A ^ j = single (natExponent j) 1 := by
  simp [X_def]

end TauCeti.PositiveDegrees.nonnegIntegers
