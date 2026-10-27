/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Nilpotent.Exp

/-!
# Exponentiating derivations with nilpotent coefficients

Multiplying a derivation by a nilpotent element in its kernel gives a nilpotent
endomorphism. On an eigenvector of the original derivation its exponential is
multiplication by the exponential of the weighted coefficient. This allows
degree derivations, which need not be nilpotent themselves, to produce finite
exponential automorphisms. We use Mathlib's finite exponential and Tau Ceti's
exponential of multiplication operators.
-/

public section

noncomputable section

namespace Derivation

variable {R A : Type*} [CommSemiring R]

section Semiring

variable [CommSemiring A] [Algebra R A]

/-- Powers of a derivation multiplied by a coefficient in its kernel factor
as multiplication by the coefficient's power followed by the derivation's power. -/
theorem smul_toLinearMap_pow (D : Derivation R A A) {x : A} (hx : D x = 0) (k : ℕ) :
    (x • D).toLinearMap ^ k =
      LinearMap.mulLeft R (x ^ k) * D.toLinearMap ^ k := by
  have hc : Commute (LinearMap.mulLeft R x) D.toLinearMap := by
    ext a
    simp [Derivation.leibniz, hx, smul_eq_mul]
  have he : (x • D).toLinearMap = LinearMap.mulLeft R x * D.toLinearMap := by
    ext a
    rfl
  rw [he, hc.mul_pow, LinearMap.pow_mulLeft]

/-- A nilpotent coefficient killed by a derivation makes its multiple nilpotent,
with the same vanishing-power bound as the coefficient. -/
theorem smul_toLinearMap_pow_eq_zero (D : Derivation R A A) {x : A}
    (hx : D x = 0) {k : ℕ} (hk : x ^ k = 0) : (x • D).toLinearMap ^ k = 0 := by
  rw [D.smul_toLinearMap_pow hx, hk]
  simp

end Semiring

variable [CommRing A] [Algebra R A] [Algebra ℚ A]

/-- On a vector of weight `r`, exponentiating a derivation with an invariant
nilpotent coefficient multiplies by `exp (r • x)`. -/
theorem exp_smul_toLinearMap_apply (D : Derivation R A A) {x : A}
    (hx : D x = 0) (hn : IsNilpotent x) {r : R} {a : A} (ha : D a = r • a) :
    IsNilpotent.exp (x • D).toLinearMap a = IsNilpotent.exp (r • x) * a := by
  obtain ⟨k, hk⟩ := hn
  have hp (j : ℕ) : (D.toLinearMap ^ j) a = r ^ j • a := by
    induction j with
    | zero => simp
    | succ j ih => simp [pow_succ', Module.End.mul_apply, ih, ha, smul_smul, mul_comm]
  have ht (j : ℕ) : ((x • D).toLinearMap ^ j) a =
      (LinearMap.mulLeft R (r • x) ^ j) a := by
    rw [D.smul_toLinearMap_pow hx, Module.End.mul_apply, hp, LinearMap.pow_mulLeft]
    simp [smul_pow]
  have hr : (r • x) ^ k = 0 := by simp [smul_pow, hk]
  rw [IsNilpotent.exp_eq_sum (D.smul_toLinearMap_pow_eq_zero hx hk),
    ← IsNilpotent.exp_mulLeft_apply (R := R) ⟨k, hr⟩ a,
    IsNilpotent.exp_eq_sum (a := LinearMap.mulLeft R (r • x))
      (by rw [LinearMap.pow_mulLeft, hr]; simp)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, ht]

end Derivation
