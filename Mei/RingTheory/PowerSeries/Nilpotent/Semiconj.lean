/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.PowerSeries.Nilpotent.Basic
public import Mei.RingTheory.PowerSeries.Monomial

/-!
# Semiconjugacy under nilpotent power series evaluation

A scalar rescaling relation for a nilpotent algebra element transports scalar
power series across multiplication by an arbitrary algebra element. Evaluation
therefore turns the formal rescaling ratio of a unit series into its conjugation
formula in an associative algebra, which need not be commutative.

We sum the coefficients of `PowerSeries.evalMonomial_mul_C` and
`PowerSeries.evalMonomial_smul` up to a nilpotence bound, using
`PowerSeries.nilpotentAeval_eq_sum`. This is the finite-order bridge from formal
monomial series to actual algebra elements; no invertibility of the rescaling
scalar or of the element being acted on is needed.
-/

public section

namespace PowerSeries

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {x : A} (hx : IsNilpotent x)

/-- Scalar multiplication of a nilpotent evaluation point is scalar rescaling of the series. -/
theorem nilpotentAeval_smul (a : R) (G : R⟦X⟧) :
    nilpotentAeval (hx.smul a) G = nilpotentAeval hx (rescale a G) := by
  let n := hx.choose
  have hn : x ^ n = 0 := hx.choose_spec
  have hax : (a • x) ^ n = 0 := by rw [smul_pow, hn, smul_zero]
  rw [nilpotentAeval_eq_sum _ hax, nilpotentAeval_eq_sum _ hn]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [coeff_evalMonomial] using congrArg (coeff j) (evalMonomial_smul x a G)

/-- Evaluating a unit series turns its rescaling ratio into conjugation. -/
theorem nilpotentAeval_conj (y : A) (a : R) (h : SemiconjBy y (a • x) x)
    (G : R⟦X⟧ˣ) :
    nilpotentAeval hx (G : R⟦X⟧) * y * nilpotentAeval hx (↑(G⁻¹) : R⟦X⟧) =
      y * nilpotentAeval hx (rescale a (G : R⟦X⟧) * (↑(G⁻¹) : R⟦X⟧)) := by
  rw [nilpotentAeval_mul_of_semiconj hx y a h, map_mul, mul_assoc]

end PowerSeries
