/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Monomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# The ordinary monomial presentation

The standard basis of an additive monoid algebra presents its exponent pieces
as free rank-one modules. This includes the degree lattice of principal
coefficients, and supports restriction and truncation of monomials without
assuming that the coefficient ring is a field.

We use Mathlib's `AddMonoidAlgebra.basis` and exponent grading.
-/

public noncomputable section

namespace Mei.AddMonoidAlgebra

open _root_.AddMonoidAlgebra

variable {R Γ : Type*} [CommSemiring R]

/-- The standard exponent basis, as a monomial presentation of the additive monoid algebra. -/
def monomialPresentation : Mei.MonomialPresentation (grade R : Γ → Submodule R R[Γ]) where
  basis := basis Γ R
  grade_eq_span p := by
    ext x
    rw [mem_grade_iff', Submodule.mem_span_singleton]
    simp [basis_apply, LinearMap.mem_range, smul_single, eq_comm]

/-- The presentation uses the existing exponent basis and its coordinates. -/
@[simp]
theorem monomialPresentation_basis :
    (monomialPresentation (R := R) (Γ := Γ)).basis = basis Γ R := (rfl)

end Mei.AddMonoidAlgebra
