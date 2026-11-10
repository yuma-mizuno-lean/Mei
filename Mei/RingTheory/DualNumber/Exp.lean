/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.DualNumber
public import Mei.RingTheory.TrivSqZeroExt.Exp
public import TauCeti.RingTheory.Nilpotent.Exp.Basic

/-!
# Nilpotent exponentials in the dual numbers

In the dual numbers `R[ε]` over `ℚ`, Mathlib's finite exponential `IsNilpotent.exp` of `ε` is
`1 + ε`.

Over a nontrivial `ℚ`-algebra `R`, for instance `R = ℚ` with `ℚ[ε] ≅ ℚ[X]/(X²)`, the unit
`exp ε` of `R[ε]` is not `1`, yet conjugation by it fixes every element of `R[ε]`, since `ε` is
central.

## Main results

* `IsNilpotent.exp_eps`: `exp ε = 1 + ε`.
* `DualNumber.nilpotentExpUnit_eps_ne_one`: the unit `exp ε` is not `1`.
* `DualNumber.toConjAct_nilpotentExpUnit_eps_smul`: conjugation by `exp ε` is the identity.

The first is the algebraic counterpart of Mathlib's `DualNumber.exp_eps` for the analytic
exponential.
-/

public section

open TrivSqZeroExt DualNumber

namespace IsNilpotent

variable {R : Type*} [Ring R] [Module ℚ R]

/-- The finite exponential of `ε` in the dual numbers is `1 + ε`. -/
@[simp]
theorem exp_eps : exp (ε : R[ε]) = 1 + ε :=
  exp_inr 1

end IsNilpotent

namespace DualNumber

variable {R : Type*} [Ring R] [Algebra ℚ R]

/-- The unit `exp ε` of the dual numbers over a nontrivial `ℚ`-algebra is not `1`. -/
theorem nilpotentExpUnit_eps_ne_one [Nontrivial R] :
    TauCeti.nilpotentExpUnit (isNilpotent_eps (R := R)) ≠ 1 := by
  intro h
  have := congrArg (fun u : R[ε]ˣ => snd (u : R[ε])) h
  simp at this

/-- Conjugation by the unit `exp ε` fixes every element of the dual numbers. -/
@[simp]
theorem toConjAct_nilpotentExpUnit_eps_smul (a : R[ε]) :
    ConjAct.toConjAct (TauCeti.nilpotentExpUnit (isNilpotent_eps (R := R))) • a = a := by
  have hcomm : Commute (TauCeti.nilpotentExpUnit (isNilpotent_eps (R := R)) : R[ε]) a := by
    rw [TauCeti.coe_nilpotentExpUnit, IsNilpotent.exp_eps]
    exact (Commute.one_left a).add_left (commute_eps_left a)
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, hcomm.eq, mul_assoc, Units.mul_inv,
    mul_one]

end DualNumber
