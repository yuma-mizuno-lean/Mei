/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Algebra automorphisms from completed scalar series

A unit power series evaluated at a positive completed element acts by inner
algebra automorphisms, and the inverse series supplies the inverse automorphism.
Filtration preservation and coefficient transport are provided by the twisted
series action API, whose scalar-one case is this conjugation.

The construction uses the existing conjugation action of units and completed
power series evaluation; the coefficient algebra need not be commutative.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Evaluated unit series act on the completion by algebra automorphisms. -/
noncomputable def completedSeriesAction (x : F.completionIdeal 1) :
    (PowerSeries R)ˣ →* (F.completion ≃ₐ[R] F.completion) :=
  (MulSemiringAction.toAlgAut (ConjAct F.completionˣ) R F.completion).comp
    (ConjAct.toConjAct.toMonoidHom.comp (Units.map (F.completedAeval x).toMonoidHom))

/-- The series action is conjugation by its completed evaluation. -/
theorem completedSeriesAction_apply (x : F.completionIdeal 1) (H : (PowerSeries R)ˣ)
    (a : F.completion) :
    F.completedSeriesAction x H a =
      F.completedAeval x (H : PowerSeries R) * a *
        F.completedAeval x (↑(H⁻¹) : PowerSeries R) := by
  -- This apply lemma exposes the defining ConjAct action and Units.map value;
  -- both evaluate pointwise, so the displayed product is definitionally equal.
  rfl

/-- Reversing the unit series gives the inverse algebra automorphism. -/
@[simp]
theorem completedSeriesAction_inv (x : F.completionIdeal 1) (H : (PowerSeries R)ˣ) :
    F.completedSeriesAction x (H⁻¹) = (F.completedSeriesAction x H).symm :=
  map_inv (F.completedSeriesAction x) H

end Mei.AlgFiltration
