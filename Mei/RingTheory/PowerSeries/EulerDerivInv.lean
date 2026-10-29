/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat

/-!
# Inverting the Euler derivation

The Euler derivation `f ↦ X * derivative f` multiplies the coefficient of degree
`j` by `j`. Over a rational algebra, `eulerDerivInv` divides the positive-degree
coefficients by their degrees and sets the constant coefficient to zero. It
inverts the Euler derivation on series without constant term. Applied to a formal
logarithm, this gives the potential whose ray exponential acts by that wall
function.
-/

public section

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The inverse of the Euler derivation `X * d/dX`: integration against `dX / X`,
with zero integration constant. The constant coefficient of the input is discarded. -/
def eulerDerivInv : PowerSeries R →ₗ[R] PowerSeries R where
  toFun f := mk fun j => (j : ℚ)⁻¹ • coeff j f
  map_add' f g := by ext j; simp [smul_add]
  map_smul' r f := by ext j; simp

/-- Inverting the Euler derivation divides each positive-degree coefficient by its degree. -/
@[simp]
theorem coeff_eulerDerivInv (f : PowerSeries R) (j : ℕ) :
    coeff j (eulerDerivInv f) = (j : ℚ)⁻¹ • coeff j f := by
  simp [eulerDerivInv]

/-- The inverse Euler derivation uses zero integration constant. -/
@[simp]
theorem constantCoeff_eulerDerivInv (f : PowerSeries R) :
    constantCoeff (eulerDerivInv f) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_eulerDerivInv]
  simp

/-- The Euler derivative recovers a series with zero constant coefficient. -/
theorem X_mul_derivative_eulerDerivInv (f : PowerSeries R)
    (hf : constantCoeff f = 0) : X * d⁄dX (eulerDerivInv f) = f := by
  ext j
  cases j with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, hf]
  | succ j =>
    simp only [coeff_succ_X_mul, coeff_derivative, coeff_eulerDerivInv]
    rw [mul_comm, ← Nat.cast_succ, ← map_natCast (algebraMap ℚ R),
      ← Algebra.smul_def, smul_smul]
    simp [Nat.cast_add_one_ne_zero]

/-- The inverse Euler derivation is the unique zero-constant series with the prescribed
Euler derivative. -/
theorem eulerDerivInv_eq_iff (f g : PowerSeries R) (hf : constantCoeff f = 0) :
    eulerDerivInv f = g ↔ constantCoeff g = 0 ∧ X * d⁄dX g = f := by
  have : HasUniqueDiv R := .of_module_rat R
  constructor
  · rintro rfl
    exact ⟨constantCoeff_eulerDerivInv f, X_mul_derivative_eulerDerivInv f hf⟩
  · rintro ⟨hg, hd⟩
    exact derivative.ext (X_mul_cancel ((X_mul_derivative_eulerDerivInv f hf).trans hd.symm))
      ((constantCoeff_eulerDerivInv f).trans hg.symm)

/-- Coefficient homomorphisms commute with integration against `dX / X`. -/
@[simp]
theorem map_eulerDerivInv {S : Type*} [CommRing S] [Algebra ℚ S]
    (φ : R →+* S) (f : PowerSeries R) :
    map φ (eulerDerivInv f) = eulerDerivInv (map φ f) := by
  ext j
  simp only [coeff_map, coeff_eulerDerivInv, map_rat_smul]

end PowerSeries
