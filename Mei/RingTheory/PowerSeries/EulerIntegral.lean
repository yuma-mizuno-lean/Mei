/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Algebra.Algebra.Rat

/-!
# Integration for the Euler derivation

The Euler derivation `f ↦ X * derivative f` multiplies the coefficient of degree
`j` by `j`. Over a rational algebra, `eulerIntegral` divides the positive-degree
coefficients by their degrees and sets the constant coefficient to zero. It
inverts the Euler derivation on series without constant term. Applied to a formal
logarithm, this gives the potential whose ray exponential acts by that wall
function.
-/

public section

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Integration against `dX / X`, with zero integration constant. The constant
coefficient of the input is discarded. -/
def eulerIntegral : PowerSeries R →ₗ[R] PowerSeries R where
  toFun f := mk fun j => (j : ℚ)⁻¹ • coeff j f
  map_add' f g := by ext j; simp [smul_add]
  map_smul' r f := by ext j; simp

/-- Euler integration divides each positive-degree coefficient by its degree. -/
@[simp]
theorem coeff_eulerIntegral (f : PowerSeries R) (j : ℕ) :
    coeff j (eulerIntegral f) = (j : ℚ)⁻¹ • coeff j f := by
  simp [eulerIntegral]

/-- Euler integration uses zero integration constant. -/
@[simp]
theorem constantCoeff_eulerIntegral (f : PowerSeries R) :
    constantCoeff (eulerIntegral f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_eulerIntegral]
  simp

/-- The Euler derivative recovers a series with zero constant coefficient. -/
theorem X_mul_derivative_eulerIntegral (f : PowerSeries R)
    (hf : constantCoeff f = 0) : X * d⁄dX (eulerIntegral f) = f := by
  ext j
  cases j with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, hf]
  | succ j =>
    simp only [coeff_succ_X_mul, coeff_derivative, coeff_eulerIntegral]
    rw [mul_comm, ← Nat.cast_succ, ← map_natCast (algebraMap ℚ R),
      ← Algebra.smul_def, smul_smul]
    simp [Nat.cast_add_one_ne_zero]

/-- The Euler integral is the unique zero-constant series with the prescribed
Euler derivative. -/
theorem eulerIntegral_eq_iff (f g : PowerSeries R) (hf : constantCoeff f = 0) :
    eulerIntegral f = g ↔ constantCoeff g = 0 ∧ X * d⁄dX g = f := by
  have : HasUniqueDiv R := .of_module_rat R
  constructor
  · rintro rfl
    exact ⟨constantCoeff_eulerIntegral f, X_mul_derivative_eulerIntegral f hf⟩
  · rintro ⟨hg, hd⟩
    exact derivative.ext (X_mul_cancel ((X_mul_derivative_eulerIntegral f hf).trans hd.symm))
      ((constantCoeff_eulerIntegral f).trans hg.symm)

end PowerSeries
