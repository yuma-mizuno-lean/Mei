/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic
public import Mei.RingTheory.FilteredAlgebra.Exp.Basic
public import Mei.RingTheory.PowerSeries.Nilpotent.Log

/-!
# Evaluating the logarithm in a filtered completion

The formal scalar logarithm evaluated at an element of the first completed
ideal is the completed logarithm of one plus that element. This identifies
power-series coefficients with exponential coordinates for function walls.
It uses `PowerSeries.nilpotentAeval_log` at every finite quotient.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]
  [Algebra ℚ A] (F : AlgFiltration A)

/-- The evaluated formal logarithm is the completed logarithm of one plus the
evaluation point. -/
@[simp]
theorem completedAeval_log (x : F.completionIdeal 1) :
    F.completedAeval x (PowerSeries.log R) =
      F.completedLog ⟨1 + x, by simpa using x.property⟩ := by
  apply F.completion_ext
  intro k
  simp only [F.projection_completedAeval, PowerSeries.nilpotentAeval_log,
    F.projection_completedLog, map_add, map_one]

/-- The formal logarithm of any constant-one series evaluates to the completed
logarithm of its value. -/
@[simp]
theorem completedAeval_logOf (x : F.completionIdeal 1) (f : PowerSeries R)
    (hf : PowerSeries.constantCoeff f = 1) :
    F.completedAeval x (PowerSeries.logOf f) =
      F.completedLog ⟨F.completedAeval x f, F.completedAeval_sub_one_mem_first x f hf⟩ := by
  apply F.completion_ext
  intro k
  simp only [F.projection_completedAeval, PowerSeries.nilpotentAeval_logOf _ _ hf,
    F.projection_completedLog]

end Mei.AlgFiltration
