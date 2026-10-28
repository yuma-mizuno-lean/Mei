/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Group.Semiconj.Defs

/-!
# Evaluating series at a monomial over a noncommutative algebra

For an element `x` of an associative algebra, send `G(T)` to the series
`G(xT)`, whose coefficient of `T^j` is `G_j • x^j`. Scalar coefficients
commute with `x`, so this is an algebra homomorphism even when the target
algebra is noncommutative. A semiconjugacy between `x` and another element
then transports the entire series, including its inverse when it is a unit.

The coefficient calculation uses Mathlib's power-series convolution and
`SemiconjBy.pow_right`. It extends the scalar rescaling operation
`PowerSeries.rescale` to a possibly noncentral algebra element.
-/

public section

noncomputable section

namespace PowerSeries

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Evaluate a scalar series at `xT`, retaining the formal parameter `T`. -/
def evalMonomial (x : A) : R⟦X⟧ →ₐ[R] A⟦X⟧ where
  toFun G := mk fun j => coeff j G • x ^ j
  map_zero' := by ext j; simp
  map_one' := by
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  map_add' F G := by ext j; simp [add_smul]
  map_mul' F G := by
    ext j
    simp only [coeff_mk, coeff_mul, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' := Finset.mem_antidiagonal.mp hab
    simp only [smul_mul_smul_comm, ← pow_add, hab']
  commutes' r := by
    ext j
    by_cases hj : j = 0 <;> simp [hj, coeff_C, Algebra.algebraMap_eq_smul_one]

/-- Monomial evaluation multiplies the `j`th coefficient by `x^j`. -/
@[simp]
theorem coeff_evalMonomial (x : A) (G : R⟦X⟧) (j : ℕ) :
    coeff j (evalMonomial x G) = coeff j G • x ^ j := by
  simp [evalMonomial]

/-- Evaluating a constant retains the constant scalar. -/
@[simp]
theorem evalMonomial_C (x : A) (r : R) :
    evalMonomial x (C r) = C (algebraMap R A r) := by
  ext j
  by_cases hj : j = 0 <;> simp [hj, coeff_C, Algebra.algebraMap_eq_smul_one]

/-- The parameter evaluates to `xT`. -/
@[simp]
theorem evalMonomial_X (x : A) :
    evalMonomial (R := R) x X = C x * X := by
  ext j
  by_cases hj : j = 1 <;> simp [hj, coeff_X, coeff_C_mul]

/-- Scaling the algebra element agrees with rescaling the scalar series. -/
theorem evalMonomial_smul (x : A) (a : R) (G : R⟦X⟧) :
    evalMonomial (a • x) G = evalMonomial x (rescale a G) := by
  ext j
  simp [smul_pow, smul_smul, mul_comm]

/-- Compatible scalar and algebra maps commute with monomial evaluation. -/
theorem map_evalMonomial {S B : Type*} [CommSemiring S] [Semiring B] [Algebra S B]
    (φ : R →+* S) (ψ : A →+* B)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r)) (x : A) (G : R⟦X⟧) :
    map ψ (evalMonomial x G) = evalMonomial (ψ x) (map φ G) := by
  ext j
  simp [Algebra.smul_def, hψ]

/-- A semiconjugacy for the algebra element transports all scalar series. -/
theorem evalMonomial_mul_C (x y : A) (a : R)
    (h : SemiconjBy y (a • x) x) (G : R⟦X⟧) :
    evalMonomial x G * C y = C y * evalMonomial x (rescale a G) := by
  rw [← evalMonomial_smul]
  ext j
  simpa only [coeff_mul_C, coeff_C_mul, coeff_evalMonomial,
    smul_mul_assoc, mul_smul_comm] using
    congrArg (fun z : A => coeff j G • z) (h.pow_right j).eq.symm

/-- Conjugation by a scalar unit series at `xT` is given by its rescaling ratio. -/
theorem evalMonomial_conj (x y : A) (a : R)
    (h : SemiconjBy y (a • x) x) (G : R⟦X⟧ˣ) :
    evalMonomial x (G : R⟦X⟧) * C y * evalMonomial x (↑(G⁻¹) : R⟦X⟧) =
      C y * evalMonomial x (rescale a (G : R⟦X⟧) * (↑(G⁻¹) : R⟦X⟧)) := by
  rw [evalMonomial_mul_C x y a h, map_mul, mul_assoc]

end PowerSeries
