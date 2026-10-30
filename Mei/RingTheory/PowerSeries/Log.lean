/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
import TauCeti.RingTheory.PowerSeries.Log

/-!
# Coefficient naturality of formal logarithms

The formal logarithm of a constant-one series commutes with coefficient maps
between rational algebras. This allows logarithmic wall labels to specialize
with their wall functions. We use Mathlib's `PowerSeries.map_subst` and `map_log`.
The linear coefficient of a constant-one series agrees with that of its logarithm,
by the logarithmic derivative identity `PowerSeries.logDeriv_mul`.
-/

public section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]

/-- Specializing a constant-one series commutes with its formal logarithm. -/
@[simp]
theorem map_logOf (φ : R →+* S) (f : PowerSeries R) (hf : constantCoeff f = 1) :
    map φ (logOf f) = logOf (map φ f) := by
  have hs := map_subst (h := φ)
    (HasSubst.of_constantCoeff_zero' (by simp [hf]) : HasSubst (f - 1)) (log R)
  rw [map_log] at hs
  simpa only [PowerSeries.map, logOf_eq, map_sub, map_one] using hs

/-- A constant-one series and its formal logarithm have the same linear coefficient. -/
theorem coeff_one_logOf {f : PowerSeries R} (hf : constantCoeff f = 1) :
    coeff 1 (logOf f) = coeff 1 f := by
  have h := congrArg (coeff 0) (logDeriv_mul f hf)
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, hf, mul_one,
    ← coeff_zero_eq_constantCoeff_apply, coeff_logDeriv, coeff_derivative] at h
  simpa using h

end PowerSeries
