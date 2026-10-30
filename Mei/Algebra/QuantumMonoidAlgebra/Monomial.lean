/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Basic
public import Mei.LinearAlgebra.GradedModule.Monomial.Basic

/-!
# The quantum monomial presentation

The standard quantum basis presents each exponent piece as a free rank-one
module. The twisting form changes multiplication but leaves this presentation
and its degree truncations unchanged. We use `QuantumMonoidAlgebra.basis` and
the existing twisted exponent grading.
-/

public noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]

/-- The standard monomials form the monomial presentation of the quantum algebra.
No alternating-form or nontriviality hypothesis is needed. -/
def monomialPresentation (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) :
    MonomialPresentation (grade q β) where
  basis := basis q β
  grade_eq_span p := by
    ext x
    rw [mem_grade_iff, Submodule.mem_span_singleton, basis_apply]

/-- The presentation uses the existing quantum basis and its coordinates. -/
@[simp]
theorem monomialPresentation_basis (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) :
    (monomialPresentation q β).basis = basis q β := (rfl)

end Mei.QuantumMonoidAlgebra
