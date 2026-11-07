/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Basic
public import Mathlib.Algebra.Group.Units.Basic

/-!
# Units represented by quantum monomials

Quantum monomials are units for every integral bilinear form. The inverse has a
necessary diagonal factor; no alternating hypothesis is used. The unit is the
existing twisted-monoid-algebra unit, and conjugation depends only on the skew
part of the form.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- The existing twisted basis unit at an additive exponent. -/
def monomialUnit (p : Γ) : (QuantumMonoidAlgebra q β)ˣ :=
  Units.map ((twistedEquiv q β).symm : _ →* _)
    (TauCeti.TwistedMonoidAlgebra.isUnit_of (k := R) (α := factorSet q β)
      (Multiplicative.ofAdd p)).unit

/-- Forgetting the unit structure recovers the quantum monomial. -/
@[simp]
theorem coe_monomialUnit (p : Γ) :
    (monomialUnit q β p : QuantumMonoidAlgebra q β) = monomial q β p := by
  simp [monomialUnit]

/-- The inverse includes the diagonal factor, even for nonalternating forms. -/
@[simp]
theorem coe_monomialUnit_inv (p : Γ) :
    (↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) =
      ((q ^ β p p : Rˣ) : R) • monomial q β (-p) := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [coe_monomialUnit, mul_smul_comm, diagonal_smul_monomial_mul_neg]

/-- Right conjugation of a monomial is its skew-character rescaling. -/
theorem monomialUnit_inv_mul_monomial_mul (p n : Γ) :
    (↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) * monomial q β n *
        monomialUnit q β p =
      ((q ^ (β n p - β p n) : Rˣ) : R) • monomial q β n := by
  have h := congrArg (fun a => (↑(monomialUnit q β p)⁻¹ : QuantumMonoidAlgebra q β) * a)
    (monomial_semiconjBy_skew q β n p).eq
  rw [← coe_monomialUnit q β p, ← mul_assoc, Units.inv_mul, one_mul,
    ← mul_assoc] at h
  exact h.symm

end Mei.QuantumMonoidAlgebra
