/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Ring.Units
public import Mathlib.Tactic.LinearCombination

/-!
# Identities for units in rings

Invertibility of a difference of powers of a unit and its inverse implies
invertibility of the corresponding even-power difference from one.
The binomial pentagon identity rewrites products of integer powers of binomial units;
it supplies the algebraic calculation in dilogarithm pentagon actions.
-/

public section

namespace Units

/-- If `q ^ n - q⁻¹ ^ n` is a unit, then so is `(q ^ 2) ^ n - 1`. -/
theorem isUnit_sq_pow_sub_one {R : Type*} [Ring R] (q : Rˣ) (n : ℕ)
    (h : IsUnit ((q : R) ^ n - ((q⁻¹ : Rˣ) : R) ^ n)) :
    IsUnit (((q : R) ^ 2) ^ n - 1) := by
  have hinv : (q : R) ^ n * ((q⁻¹ : Rˣ) : R) ^ n = 1 := by
    rw [← q.commute_coe_inv.mul_pow]
    simp
  have he : (q : R) ^ n * ((q : R) ^ n - ((q⁻¹ : Rˣ) : R) ^ n) =
      ((q : R) ^ 2) ^ n - 1 := by
    rw [mul_sub, hinv, ← pow_add, ← Nat.two_mul, pow_mul]
  rw [← he]
  exact (q.isUnit.pow n).mul h

/-- The unit identity behind the pentagon: if `U₁ = 1 + x`, `U₂ = 1 + y`,
`V = 1 + U₂ x`, `P = 1 + U₁⁻¹ x y` and `W = 1 + P⁻¹ U₁⁻¹ y`, then `V = P U₁` and
`U₂ = W P`, so `V^a U₂^b z = W^b P^(a + b) U₁^a z`. -/
theorem pentagon {K : Type*} [CommRing K] {x y w : K} {U₁ U₂ V P W : Kˣ}
    (hU₁ : (U₁ : K) = 1 + x) (hU₂ : (U₂ : K) = 1 + y) (hw : w = x * y)
    (hV : (V : K) = 1 + ↑(U₂ ^ (1 : ℤ)) * x) (hP : (P : K) = 1 + ↑(U₁ ^ (-1 : ℤ)) * w)
    (hW : (W : K) = 1 + ↑(P ^ (-1 : ℤ)) * (↑(U₁ ^ (-1 : ℤ)) * y)) (a b : ℤ) (z : K) :
    ↑(V ^ a) * (↑(U₂ ^ b) * z) = ↑(W ^ b) * (↑(P ^ (a + b)) * (↑(U₁ ^ a) * z)) := by
  subst hw
  simp only [zpow_one] at hV
  simp only [zpow_neg_one] at hP hW
  have h₁ := U₁.inv_mul
  have hP' := P.inv_mul
  have hVP : V = P * U₁ := by
    apply Units.ext
    rw [Units.val_mul, hV, hP, hU₂]
    linear_combination (-(x * y)) * h₁ - hU₁
  have hWP : U₂ = W * P := by
    apply Units.ext
    rw [Units.val_mul, hW, hU₂]
    linear_combination (-(↑U₁⁻¹ * y)) * hP' - hP - y * h₁ + (↑U₁⁻¹ * y) * hU₁
  have key : V ^ a * U₂ ^ b = W ^ b * P ^ (a + b) * U₁ ^ a := by
    rw [hVP, hWP, mul_zpow, mul_zpow, zpow_add]
    simp only [mul_assoc, mul_comm]
  simpa only [Units.val_mul, mul_assoc] using congrArg (fun u : Kˣ => (u : K) * z) key

end Units
