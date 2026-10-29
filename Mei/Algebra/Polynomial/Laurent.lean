/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

/-!
# Divisibility of Laurent polynomials by constants

A Laurent polynomial is divisible by a constant `C a` exactly when all of its coefficients are
divisible by `a`, as for `Polynomial.C_dvd_iff_dvd_coeff`. Consequently `1 + T` is a
nonzerodivisor modulo every constant: if `C a` divides `(1 + T) * p`, then it divides `p`.
This is the regularity of a gluing function `1 + w` on truncated Laurent coefficient rings.
-/

public section

namespace LaurentPolynomial

open AddMonoidAlgebra

variable {R : Type*}

/-- A Laurent polynomial is divisible by a constant exactly when all its coefficients are. -/
theorem C_dvd_iff_dvd_coeff [CommSemiring R] (a : R) (p : R[T;T⁻¹]) :
    C a ∣ p ↔ ∀ n, a ∣ p.coeff n := by
  classical
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [← single_eq_C, coeff_single_zero_mul]
    exact dvd_mul_right _ _
  · intro h
    let g : R → R := fun r => if hr : r ≠ 0 ∧ a ∣ r then hr.2.choose else 0
    have hg (r : R) (hr : a ∣ r) : a * g r = r := by
      simp only [g]
      split_ifs with h'
      · exact h'.2.choose_spec.symm
      · simp_all
    refine ⟨(coeffLinearEquiv R).symm (p.coeff.mapRange g (by simp [g])),
      LaurentPolynomial.ext fun n => ?_⟩
    rw [← single_eq_C, coeff_single_zero_mul]
    simp [hg _ (h n)]

/-- Multiplication by `1 + T` is injective modulo a constant. -/
theorem C_dvd_of_C_dvd_one_add_T_mul [CommRing R] {a : R} {p : R[T;T⁻¹]}
    (h : C a ∣ (1 + T 1) * p) : C a ∣ p := by
  rw [C_dvd_iff_dvd_coeff] at h ⊢
  have hcoeff (n : ℤ) : a ∣ p.coeff n + p.coeff (n - 1) := by
    have := h n
    rwa [add_mul, one_mul, coeff_add, Finsupp.add_apply, T, coeff_single_mul_apply,
      one_mul, neg_add_eq_sub] at this
  obtain ⟨N, hN⟩ := p.coeff.support.bddBelow
  have hlow (n : ℤ) (hn : n < N) : p.coeff n = 0 :=
    Finsupp.notMem_support_iff.mp fun hmem => (hN hmem).not_gt hn
  have hup (j : ℕ) : a ∣ p.coeff (N + j) := by
    induction j with
    | zero =>
      simpa [hlow (N - 1) (by omega)] using hcoeff N
    | succ j ih =>
      have := hcoeff (N + (j + 1 : ℕ))
      rw [show N + ((j + 1 : ℕ) : ℤ) - 1 = N + j by push_cast; ring] at this
      exact (dvd_add_left ih).mp this
  intro n
  rcases lt_or_ge n N with hn | hn
  · rw [hlow n hn]
    exact dvd_zero _
  · have := hup (n - N).toNat
    rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this

end LaurentPolynomial
