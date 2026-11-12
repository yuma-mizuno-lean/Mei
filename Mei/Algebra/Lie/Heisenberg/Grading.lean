/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Truncation.Basic
public import TauCeti.Algebra.Lie.Heisenberg.Grading

/-!
# Heisenberg truncations

TauCeti supplies the grading of the Heisenberg Lie algebra. Its degree-one
and degree-two pieces give the truncation ideals for Mei's positive degrees.
-/

public section

namespace Mei

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

/-- The Heisenberg grading is supported on strictly positive integer degrees. -/
instance heisenbergGrading_isPositiveGrading :
    IsPositiveGrading PositiveDegrees.nonnegIntegers (heisenbergGrading R) where
  eq_bot n hn := by
    apply (TauCeti.heisenbergGrading_isPositiveGrading R).eq_bot
    simpa only [TauCeti.PositiveDegrees.mem_nonnegIntegers_monoid,
      PositiveDegrees.mem_nonnegIntegers_monoid] using hn

private theorem degreeIdeal_heisenbergGrading_eq (k : ℕ) :
    PositiveDegrees.nonnegIntegers.degreeIdeal (heisenbergGrading R) k =
      TauCeti.PositiveDegrees.nonnegIntegers.degreeIdeal (heisenbergGrading R) k := by
  apply LieSubmodule.toSubmodule_injective
  have hdegree : PositiveDegrees.nonnegIntegers.degree =
      TauCeti.PositiveDegrees.nonnegIntegers.degree := by
    apply AddMonoidHom.ext
    intro n
    simp only [PositiveDegrees.nonnegIntegers_degree, TauCeti.PositiveDegrees.nonnegIntegers_degree]
  rw [PositiveDegrees.degreeIdeal_toSubmodule, TauCeti.PositiveDegrees.degreeIdeal_toSubmodule,
    PositiveDegrees.degreeSubmodule_def, TauCeti.PositiveDegrees.degreeSubmodule_def, hdegree]

/-- The Heisenberg terms strictly above degree one form its center. -/
@[simp]
theorem degreeIdeal_heisenbergGrading_one :
    PositiveDegrees.nonnegIntegers.degreeIdeal (heisenbergGrading R) 1 =
      LieAlgebra.center R (heisenberg R) := by
  rw [degreeIdeal_heisenbergGrading_eq, TauCeti.degreeIdeal_heisenbergGrading_one]

/-- The Heisenberg degree ideal vanishes from order two onwards. -/
@[simp]
theorem degreeIdeal_heisenbergGrading_eq_bot {k : ℕ} (hk : 2 ≤ k) :
    PositiveDegrees.nonnegIntegers.degreeIdeal (heisenbergGrading R) k = ⊥ := by
  rw [degreeIdeal_heisenbergGrading_eq, TauCeti.degreeIdeal_heisenbergGrading_eq_bot R hk]

end Mei
