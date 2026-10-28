/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Derivative

import Mathlib.Algebra.Algebra.Rat

/-!
# The dilogarithm power series

Over a `ℚ`-algebra, `negDilogNeg A` is the formal power series
`-Li₂(-X) = ∑_{n ≥ 1} (-1)^(n+1) Xⁿ / n² = X - X²/4 + X³/9 - ⋯`.
It is the unique power series without constant term whose logarithmic derivative
`X · d/dX` is Mathlib's `PowerSeries.log A = log(1 + X)`.

Its coefficients are the logarithmic coefficients of the dilogarithm elements
`Ψ[n] = exp(∑_{j ≥ 1} (-1)^(j+1) X_{jn} / j²)` of cluster scattering diagrams, whose wall
functions `1 + z^n` arise from the identity `X · d/dX (-Li₂(-X)) = log(1 + X)`; see
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, §1.1
(arXiv:1411.1394v2), and Nakanishi, *Cluster algebras and scattering diagrams, Part III*,
§5 (arXiv:2111.00800v6). The definition follows `PowerSeries.log`.
-/

public section

namespace PowerSeries

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The power series `-Li₂(-X) = X - X²/4 + X³/9 - ⋯`, with coefficients `(-1)^(n+1)/n²`. -/
noncomputable def negDilogNeg : PowerSeries A :=
  mk fun n ↦ if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / (n : ℚ) ^ 2)

variable {A}

@[simp]
theorem coeff_negDilogNeg (n : ℕ) :
    coeff n (negDilogNeg A) =
      if n = 0 then 0 else algebraMap ℚ A ((-1 : ℚ) ^ (n + 1) / (n : ℚ) ^ 2) :=
  coeff_mk _ _

theorem coeff_succ_negDilogNeg (n : ℕ) :
    coeff (n + 1) (negDilogNeg A) = algebraMap ℚ A ((-1 : ℚ) ^ n / ((n : ℚ) + 1) ^ 2) := by
  simp only [coeff_negDilogNeg, n.succ_ne_zero, ite_false]
  push_cast
  ring_nf

@[simp]
theorem constantCoeff_negDilogNeg : constantCoeff (negDilogNeg A) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

theorem coeff_one_negDilogNeg : coeff 1 (negDilogNeg A) = 1 := by simp

@[simp]
theorem map_negDilogNeg {A' : Type*} [CommRing A'] [Algebra ℚ A'] (f : A →+* A') :
    map f (negDilogNeg A) = negDilogNeg A' := by
  ext n
  simp only [coeff_map, coeff_negDilogNeg]
  split_ifs <;> simp [RingHom.map_rat_algebraMap]

/-- The logarithmic derivative of `-Li₂(-X)` is `log(1 + X)`. -/
theorem X_mul_derivative_negDilogNeg : X * d⁄dX (negDilogNeg A) = log A := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [coeff_succ_X_mul, coeff_derivative, coeff_negDilogNeg, coeff_log,
      n.succ_ne_zero, ite_false]
    have hn : ((n : A) + 1) = algebraMap ℚ A ((n + 1 : ℕ) : ℚ) := by simp
    rw [hn, ← map_mul]
    congr 1
    field_simp

/-- `-Li₂(-X)` is the power series without constant term whose logarithmic derivative is
`log(1 + X)`. -/
theorem eq_negDilogNeg_iff (f : A⟦X⟧) :
    f = negDilogNeg A ↔ constantCoeff f = 0 ∧ X * d⁄dX f = log A := by
  refine ⟨fun h => h ▸ ⟨constantCoeff_negDilogNeg, X_mul_derivative_negDilogNeg⟩, ?_⟩
  rintro ⟨h0, hd⟩
  ext n
  cases n with
  | zero => simpa using h0
  | succ n =>
    have h := congrArg (coeff (n + 1)) (hd.trans X_mul_derivative_negDilogNeg.symm)
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, coeff_derivative] at h
    have hu : IsUnit ((n : A) + 1) := by
      simpa using (algebraMap ℚ A).isUnit_map (Ne.isUnit (n.cast_add_one_ne_zero (R := ℚ)))
    exact hu.mul_left_injective h

end PowerSeries
