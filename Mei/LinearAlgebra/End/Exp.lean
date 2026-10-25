/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Exponentials of nilpotent associative derivations

A nilpotent linear endomorphism satisfying the Leibniz rule exponentiates to an algebra
automorphism, also for noncommutative algebras. Its inverse is the exponential of the
negative endomorphism. This packages Mathlib's `Module.End.exp_mul_of_derivation` and
`IsNilpotent.exp_neg_mul_exp_self`; the inverse construction follows `LieDerivation.exp`.
-/

public section

namespace Module.End

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Module ℚ A]

/-- The finite exponential of a nilpotent associative derivation is an algebra automorphism.
Multiplication in the coefficient algebra need not commute. -/
noncomputable def expAlgEquiv (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) : A ≃ₐ[R] A :=
  AlgEquiv.ofLinearEquiv
    { toLinearMap := IsNilpotent.exp D
      invFun a := IsNilpotent.exp (-D : Module.End R A) a
      left_inv a := by
        simpa only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          Module.End.mul_apply, Module.End.one_apply] using
          DFunLike.congr_fun hD.exp_neg_mul_exp_self a
      right_inv a := by
        simpa only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          Module.End.mul_apply, Module.End.one_apply] using
          DFunLike.congr_fun hD.exp_mul_exp_neg_self a }
    (by
      have h1 : D 1 = 0 := by
        have := hder 1 1
        simp only [one_mul, mul_one] at this
        exact (add_eq_left.mp this.symm)
      simpa using IsNilpotent.exp_smul_eq_sum (a := D) (m := (1 : A))
        (k := 1) (by simpa using h1) hD)
    (Module.End.exp_mul_of_derivation R A D hder hD)

/-- The automorphism is the finite operator exponential. -/
@[simp]
theorem expAlgEquiv_apply (D : Module.End R A) (hder) (hD) (a : A) :
    D.expAlgEquiv hder hD a = IsNilpotent.exp D a := (rfl)

/-- The inverse automorphism is the finite exponential of the negative operator. -/
@[simp]
theorem expAlgEquiv_symm_apply (D : Module.End R A) (hder) (hD) (a : A) :
    (D.expAlgEquiv hder hD).symm a = IsNilpotent.exp (-D) a := (rfl)

end Module.End
