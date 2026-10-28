/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Scalars through polynomials in power series algebras

The polynomial action on power series agrees with the action of the coefficient
scalars. This scalar tower permits restricting polynomial-algebra equivalences
to the original coefficient ring, including when that ring is itself an algebra.
-/

public section

namespace MvPowerSeries

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Scalar extension into power series factors through the polynomial algebra. -/
instance isScalarTower_mvPolynomial :
    IsScalarTower R (MvPolynomial σ S) (MvPowerSeries σ S) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    simp [algebraMap_apply', algebraMap_apply]

end MvPowerSeries
