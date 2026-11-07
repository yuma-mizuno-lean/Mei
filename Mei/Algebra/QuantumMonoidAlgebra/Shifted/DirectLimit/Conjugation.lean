/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Monomial

/-!
# The lattice action by global monomial conjugation

Although quantum monomials multiply with a bilinear phase, their conjugations
form a genuine lattice action: the scalar phases cancel. This action is defined
on the entire global coefficient algebra, not just finite monomials, and works
for arbitrary integral bilinear forms.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)

/-- The diagonal correction expresses global conjugation using ordinary monomials. -/
theorem directLimitMonomialRightConj_eq_smul (p : Γ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    directLimitMonomialRightConj q β d hspan p x =
      ((q ^ β p p : Rˣ) : R) •
        (directLimitMonomial q β d hspan (-p) * x * directLimitMonomial q β d hspan p) := by
  rw [directLimitMonomialRightConj_apply, coe_directLimitMonomialUnit_inv,
    smul_mul_assoc, smul_mul_assoc]

/-- Successive right conjugations add their lattice exponents on every coefficient. -/
theorem directLimitMonomialRightConj_add_apply (p s : Γ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    directLimitMonomialRightConj q β d hspan (p + s) x =
      directLimitMonomialRightConj q β d hspan p
        (directLimitMonomialRightConj q β d hspan s x) := by
  let z := directLimitMonomial q β d hspan
  have hprod :
      z (-p) * (z (-s) * x * z s) * z p =
        ((q ^ β (-p) (-s) : Rˣ) : R) • (((q ^ β s p : Rˣ) : R) •
          (z (-(p + s)) * x * z (p + s))) := by
    calc
      _ = (z (-p) * z (-s)) * x * (z s * z p) := by simp only [mul_assoc]
      _ = _ := by
        simp only [z, directLimitMonomial_mul, smul_mul_assoc, mul_smul_comm, neg_add,
          add_comm s p]
        rw [smul_comm]
  simp only [directLimitMonomialRightConj_eq_smul, mul_smul_comm, smul_mul_assoc]
  rw [hprod]
  simp only [smul_smul, ← Units.val_mul, ← zpow_add]
  congr 3
  simp only [map_add, LinearMap.add_apply, map_neg, LinearMap.neg_apply, neg_neg]
  abel

/-- The zero lattice exponent acts trivially. -/
@[simp]
theorem directLimitMonomialRightConj_zero :
    directLimitMonomialRightConj q β d hspan 0 = 1 := by
  apply AlgEquiv.ext
  intro x
  simp only [directLimitMonomialRightConj_eq_smul, neg_zero, directLimitMonomial_zero,
    one_mul, mul_one, map_zero, zpow_zero, Units.val_one, one_smul,
    AlgEquiv.one_apply]

/-- Monomial conjugation is a genuine lattice representation in global algebra automorphisms. -/
def directLimitMonomialConjAction : Multiplicative Γ →*
    (d.ShiftedDirectLimit (grade q β) ≃ₐ[R] d.ShiftedDirectLimit (grade q β)) where
  toFun p := directLimitMonomialRightConj q β d hspan p.toAdd
  map_one' := directLimitMonomialRightConj_zero q β d hspan
  map_mul' p s := AlgEquiv.ext fun x => directLimitMonomialRightConj_add_apply q β d hspan
    p.toAdd s.toAdd x

/-- Evaluation of the lattice representation is right monomial conjugation. -/
@[simp]
theorem directLimitMonomialConjAction_apply (p : Γ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    directLimitMonomialConjAction q β d hspan (Multiplicative.ofAdd p) x =
      directLimitMonomialRightConj q β d hspan p x := by
  -- This application only projects the defining map record and its unchanged underlying function.
  rfl

end Mei.QuantumMonoidAlgebra
