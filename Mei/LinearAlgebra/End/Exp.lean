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

A nilpotent linear endomorphism satisfying the associative Leibniz rule exponentiates to an
algebra automorphism, with inverse the exponential of its negative. The algebra may be
noncommutative. This packages Mathlib's `Module.End.exp_mul_of_derivation` and
`IsNilpotent.isUnit_exp`; the fixed-vector formula uses `IsNilpotent.exp_smul_eq_sum`.
-/

public section

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module ℚ M]

/-- Exponentiating a nilpotent endomorphism fixes every vector in its kernel. -/
theorem exp_apply_eq_self (D : Module.End R M) (hD : IsNilpotent D) {m : M}
    (hm : D m = 0) : IsNilpotent.exp D m = m := by
  have h : (D ^ 1) • m = 0 := by simpa using hm
  simpa using IsNilpotent.exp_smul_eq_sum h hD

variable {A : Type*} [Ring A] [Algebra R A] [Module ℚ A]

/-- The exponential of a nilpotent associative derivation is an algebra automorphism. -/
noncomputable def expAlgEquiv (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) :
    A ≃ₐ[R] A :=
  AlgEquiv.ofBijective
    (AlgHom.ofLinearMap (IsNilpotent.exp D)
      (exp_apply_eq_self D hD (by simpa using hder 1 1))
      (exp_mul_of_derivation R A D hder hD))
    ((Module.End.isUnit_iff _).mp hD.isUnit_exp)

/-- The automorphism acts by Mathlib's finite exponential. -/
@[simp]
theorem expAlgEquiv_apply (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) (a : A) :
    D.expAlgEquiv hder hD a = IsNilpotent.exp D a := (rfl)

/-- The inverse acts by the finite exponential of the negative endomorphism. -/
@[simp]
theorem expAlgEquiv_symm_apply (D : Module.End R A)
    (hder : ∀ a b, D (a * b) = a * D b + D a * b) (hD : IsNilpotent D) (a : A) :
    (D.expAlgEquiv hder hD).symm a = IsNilpotent.exp (-D) a := by
  apply (D.expAlgEquiv hder hD).injective
  simp only [AlgEquiv.apply_symm_apply, expAlgEquiv_apply]
  exact (LinearMap.congr_fun hD.exp_mul_exp_neg_self a).symm

end Module.End
