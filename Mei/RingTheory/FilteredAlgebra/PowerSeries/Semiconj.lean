/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic
public import Mei.RingTheory.PowerSeries.Nilpotent.Semiconj
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Rescaling completed power-series evaluation

Evaluating a power series at `a • x` in the first completed ideal agrees with
evaluating its scalar rescaling at `x`. The proof uses the corresponding identity
on each nilpotent quotient. Completed conjugation is supplied separately by
`completedAeval_conj` in `PowerSeries.Basic`.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Scaling a positive completed evaluation point rescales the scalar power series. -/
theorem completedAeval_smul (x : F.completionIdeal 1) (a : R) (G : PowerSeries R) :
    F.completedAeval (a • x) G = F.completedAeval x (PowerSeries.rescale a G) := by
  apply F.completion_ext
  intro k
  rw [projection_completedAeval, projection_completedAeval]
  have hs : F.projection k ((a • x : F.completionIdeal 1) : F.completion) =
      a • F.projection k x := by
    rw [Submodule.coe_smul_of_tower]
    simpa only [projectionₐ_apply] using
      map_smul (F.projectionₐ (R := R) k) a (x : F.completion)
  calc
    _ = PowerSeries.nilpotentAeval ((F.isNilpotent_projection x.property k).smul a) G := by
      congr 2
    _ = _ := PowerSeries.nilpotentAeval_smul _ a G

end Mei.AlgFiltration
