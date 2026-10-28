/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# First-order multiplicative difference equations for formal series

The equation `F(aX) = (1 + bX) F(X)`, with constant coefficient one, has a
unique solution when every `a^(n+1) - 1` is a unit, and two solutions with the
same constant coefficient agree when every `a^(n+1) - 1` is left regular. Any
solution satisfies the coefficient recurrence
`(a^(n+1) - 1) * coeff (n+1) F = b * coeff n F`. No field, characteristic-zero
or convergence assumption is required. Iterating the equation forwards and backwards
gives finite rescaling products for any solution, without a normalization hypothesis.

This coefficientwise construction uses Mathlib's `PowerSeries.mk`, `rescale`
and `Ring.inverse`. It supplies the formal difference-equation characterization
of the quantum dilogarithm, as in Tomoki Nakanishi, *Pentagon relation in quantum
cluster scattering diagrams*, §2.3, equation (2.14), arXiv:2202.01588v7.
-/

public section

noncomputable section

namespace PowerSeries

variable {R : Type*}

private theorem rescale_one_add_C_mul_X [CommSemiring R] (c b : R) :
    rescale c (1 + C b * X) = 1 + C (b * c) * X := by
  ext n
  simp only [coeff_rescale, map_add, coeff_one, coeff_C_mul, coeff_X]
  split_ifs <;> simp_all [mul_comm]

/-- Iterating a multiplicative difference equation gives a finite product,
without any assumption on the constant coefficient or the difference denominators. -/
theorem rescale_pow_of_rescale_eq [CommSemiring R] {a b : R} {F : PowerSeries R}
    (hF : rescale a F = (1 + C b * X) * F) (r : ℕ) :
    rescale (a ^ r) F = (∏ j ∈ Finset.range r, (1 + C (b * a ^ j) * X)) * F := by
  induction r with
  | zero => simp
  | succ r ih =>
    have he := congrArg (rescale (a ^ r)) hF
    rw [rescale_rescale, ← pow_succ', map_mul, rescale_one_add_C_mul_X, ih] at he
    rw [Finset.prod_range_succ]
    exact he.trans (by simp only [mul_assoc, mul_left_comm])

/-- Iterating a multiplicative difference equation backwards along a unit, the
rescaled solution times a finite product of linear factors recovers the solution.
No normalization of the solution is needed. -/
theorem rescale_inv_pow_mul_prod_of_rescale_eq [CommSemiring R] {a : Rˣ} {b : R}
    {F : PowerSeries R} (hF : rescale (a : R) F = (1 + C b * X) * F) (r : ℕ) :
    rescale (((a⁻¹ : Rˣ) : R) ^ r) F *
      (∏ j ∈ Finset.range r, (1 + C (b * ((a⁻¹ : Rˣ) : R) ^ (j + 1)) * X)) = F := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : (a : R) * ((a⁻¹ : Rˣ) : R) ^ (r + 1) =
        ((a⁻¹ : Rˣ) : R) ^ r := by
      rw [pow_succ', ← mul_assoc]
      simp
    have he := congrArg (rescale (((a⁻¹ : Rˣ) : R) ^ (r + 1))) hF
    rw [rescale_rescale, hp, map_mul, rescale_one_add_C_mul_X] at he
    rw [Finset.prod_range_succ]
    conv_rhs => rw [← ih, he]
    ring

variable [CommRing R]

/-- A multiplicative difference equation determines each coefficient from the
preceding one after multiplication by its difference denominator. -/
theorem pow_succ_sub_one_mul_coeff_succ_of_rescale_eq {a b : R} {F : PowerSeries R}
    (hF : rescale a F = (1 + C b * X) * F) (n : ℕ) :
    (a ^ (n + 1) - 1) * coeff (n + 1) F = b * coeff n F := by
  have he := congrArg (coeff (n + 1)) hF
  simp only [coeff_rescale, add_mul, one_mul, mul_assoc, map_add,
    coeff_C_mul, coeff_succ_X_mul] at he
  linear_combination he

/-- Two solutions with the same constant coefficient agree when multiplication
by each difference denominator is injective. The constant coefficient need not be one. -/
theorem eq_of_rescale_eq_one_add_C_mul_X_mul (a b : R)
    (ha : ∀ n : ℕ, IsLeftRegular (a ^ (n + 1) - 1)) {F G : PowerSeries R}
    (h₀ : constantCoeff F = constantCoeff G)
    (hF : rescale a F = (1 + C b * X) * F)
    (hG : rescale a G = (1 + C b * X) * G) : F = G := by
  ext n
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
    apply ha n
    dsimp only
    rw [pow_succ_sub_one_mul_coeff_succ_of_rescale_eq hF,
      pow_succ_sub_one_mul_coeff_succ_of_rescale_eq hG, ih]

/-- The normalized multiplicative difference equation has a unique formal
solution over any commutative ring with invertible difference denominators. -/
theorem existsUnique_rescale_eq_one_add_C_mul_X_mul (a b : R)
    (ha : ∀ n : ℕ, IsUnit (a ^ (n + 1) - 1)) :
    ∃! F : PowerSeries R, constantCoeff F = 1 ∧
      rescale a F = (1 + C b * X) * F := by
  let c : ℕ → R := fun n => ∏ j ∈ Finset.range n, b * Ring.inverse (a ^ (j + 1) - 1)
  have hc (n : ℕ) : (a ^ (n + 1) - 1) * c (n + 1) = b * c n := by
    dsimp only [c]
    rw [Finset.prod_range_succ]
    calc
      _ = (b * ∏ j ∈ Finset.range n, b * Ring.inverse (a ^ (j + 1) - 1)) *
          ((a ^ (n + 1) - 1) * Ring.inverse (a ^ (n + 1) - 1)) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ (ha n), mul_one]
  have hF : rescale a (mk c) = (1 + C b * X) * mk c := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
      simp only [coeff_rescale, coeff_mk, add_mul, one_mul, mul_assoc,
        map_add, coeff_C_mul, coeff_succ_X_mul]
      have := hc n
      linear_combination this
  refine ⟨mk c, ⟨by simp [c], hF⟩, ?_⟩
  intro G hG
  exact eq_of_rescale_eq_one_add_C_mul_X_mul a b (fun n => (ha n).isRegular.left)
    (hG.1.trans (by simp [c])) hG.2 hF

end PowerSeries
