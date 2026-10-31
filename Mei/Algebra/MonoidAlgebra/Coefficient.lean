/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Weighted coefficient extension

A multiplicative weight on an additive monoid gives an algebra map that extends
scalars and multiplies each monomial by its weight, retaining its exponent.
The weights need not be units, so this includes polynomial coefficient
specializations. The construction uses Mathlib's `AddMonoidAlgebra.lift` and
`AddMonoidAlgebra.singleHom`.
-/

public noncomputable section

namespace Mei.AddMonoidAlgebra

open _root_.AddMonoidAlgebra

variable (R : Type*) {S Γ : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddMonoid Γ]

/-- Extend coefficients and multiply each monomial by its multiplicative weight,
without changing its exponent. -/
def coefficientTwist (χ : Multiplicative Γ →* S) : R[Γ] →ₐ[R] S[Γ] :=
  lift R _ _ (singleHom.comp (χ.prod (MonoidHom.id _)))

/-- A monomial retains its exponent and acquires the prescribed weight. -/
@[simp]
theorem coefficientTwist_single (χ : Multiplicative Γ →* S) (q : Γ) (r : R) :
    coefficientTwist R χ (single q r) =
      single q (algebraMap R S r * χ (.ofAdd q)) := by
  simp [coefficientTwist, lift_single, Algebra.smul_def, singleHom, single_mul_single]

end Mei.AddMonoidAlgebra
