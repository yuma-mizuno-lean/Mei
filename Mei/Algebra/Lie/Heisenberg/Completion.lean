/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.Heisenberg.BCH
public import Mei.Algebra.Lie.Heisenberg.Grading

/-!
# Noncommutation in the completed Heisenberg BCH group

The completed exponentials of the standard Heisenberg generators do not commute.
We transport `exp_heisenbergX_mul_exp_heisenbergY_ne` to the completion through
its order-two truncation, whose degree ideal vanishes.
-/

public section

noncomputable section

namespace Mei

open TauCeti PositiveDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The completed exponentials of the standard Heisenberg generators do not commute
over a nontrivial coefficient ring. -/
theorem expToCompletion_heisenbergX_mul_expToCompletion_heisenbergY_ne [Nontrivial R] :
    nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R) *
        nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R) ≠
      nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergY R) *
        nonnegIntegers.expToCompletion (heisenbergGrading R) (heisenbergX R) := by
  intro he
  have hinj : Function.Injective (nonnegIntegers.degreeIdeal (heisenbergGrading R) 2).mkQ := by
    rw [← LieHom.ker_eq_bot, LieIdeal.mkQ_ker,
      degreeIdeal_heisenbergGrading_eq_bot R le_rfl]
  have h2 := congrArg (CompletedGroup.projection 2) he
  rw [map_mul, map_mul, projection_expToCompletion, projection_expToCompletion] at h2
  apply exp_heisenbergX_mul_exp_heisenbergY_ne R
  apply LieHom.bchGroupMap_injective hinj
  rw [map_mul, map_mul, LieHom.bchGroupMap_exp, LieHom.bchGroupMap_exp]
  -- The order-two tower object is the concrete truncated BCH group.
  exact h2

end Mei
