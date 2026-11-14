/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.CategoryTheory.ActionAsFunctor.Basic
public import Mei.RingTheory.DualNumber.Exp

/-!
# The conjugation action of the dual numbers does not detect `exp ε`

Let `R` be a nontrivial `ℚ`-algebra, for instance `R = ℚ` with `ℚ[ε] ≅ ℚ[X]/(X²)`. The units
of `R[ε]` act on `R[ε]` by conjugation, giving the functor
`CategoryTheory.actionAsFunctor (ConjAct R[ε]ˣ) R[ε]` on `SingleObj (ConjAct R[ε]ˣ)`. This functor
sends the label `exp ε = 1 + ε`, which is not `1`, to the identity of `R[ε]`; so it is not
faithful.

## Main results

* `DualNumber.actionAsFunctor_conjAct_map_nilpotentExpUnit_eps`: the conjugation functor sends
  `exp ε` to the identity.
* `DualNumber.not_faithful_actionAsFunctor_conjAct`: the conjugation functor is not faithful.
-/

public section

open CategoryTheory

namespace DualNumber

variable (R : Type*) [Ring R] [Algebra ℚ R]

/-- The conjugation action of the units of `R[ε]`, viewed as a functor on `SingleObj`, sends the
label `exp ε` to the identity of `R[ε]`. -/
theorem actionAsFunctor_conjAct_map_nilpotentExpUnit_eps :
    (actionAsFunctor (ConjAct R[ε]ˣ) R[ε]).map
        (X := SingleObj.star _) (Y := SingleObj.star _)
        (ConjAct.toConjAct (TauCeti.nilpotentExpUnit (isNilpotent_eps (R := R)))) =
      𝟙 _ := by
  ext a
  exact (actionAsFunctor_map_apply _ _ _ a).trans (toConjAct_nilpotentExpUnit_eps_smul a)

/-- Over a nontrivial `ℚ`-algebra `R`, the conjugation action of the units of `R[ε]`,
viewed as a functor on `SingleObj`, is not faithful. -/
theorem not_faithful_actionAsFunctor_conjAct [Nontrivial R] :
    ¬ (actionAsFunctor (ConjAct R[ε]ˣ) R[ε]).Faithful := by
  rw [actionAsFunctor.faithful_iff_faithfulSMul]
  intro _
  refine nilpotentExpUnit_eps_ne_one (R := R) (ConjAct.toConjAct.injective ?_)
  exact FaithfulSMul.eq_of_smul_eq_smul fun a => by
    rw [toConjAct_nilpotentExpUnit_eps_smul, map_one, one_smul]

end DualNumber
