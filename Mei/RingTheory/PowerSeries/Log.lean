/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Log

/-!
# Coefficient naturality of formal logarithms

The formal logarithm of a constant-one series commutes with coefficient maps
between rational algebras. This allows logarithmic wall labels to specialize
with their wall functions. We use Mathlib's `PowerSeries.map_subst` and `map_log`.
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

end PowerSeries
