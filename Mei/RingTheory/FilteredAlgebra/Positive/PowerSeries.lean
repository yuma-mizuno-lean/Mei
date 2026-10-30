/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.RingTheory.FilteredAlgebra.Positive.Basic
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Positivity of completed power series evaluations

Let `x` be an element of the first completed ideal that is positive for a subsemiring
`P`. A scalar power series whose coefficients all land in `P` evaluates at `x` to a
positive element: at order `k` the evaluation is a finite sum of coefficient multiples of
powers of a representative in `P`. In particular every power series with natural-number
coefficients, such as a geometric series `∑ xʲ` or a power `(1 + x) ^ s`, evaluates
to a positive element, although such a series need not be the canonical image of an
element of `P`. When `-1 ∈ P`, the inverse `∑ (-x)ʲ` of the unit `1 + x` is positive.
-/

public section

namespace Mei.AlgFiltration

variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B] {F : AlgFiltration B}
  {P : Subsemiring B}

/-- A power series whose coefficients map into `P` evaluates at a positive element of the
first completed ideal to a positive element. -/
theorem IsPositive.completedAeval {x : F.completionIdeal 1}
    (hx : F.IsPositive P (x : F.completion)) {f : PowerSeries R}
    (hf : ∀ i, algebraMap R B (PowerSeries.coeff i f) ∈ P) :
    F.IsPositive P (F.completedAeval x f) := by
  rw [isPositive_iff] at hx ⊢
  intro k
  obtain ⟨a, ha, hax⟩ := hx k
  refine ⟨∑ i ∈ Finset.range (k + 1), algebraMap R B (PowerSeries.coeff i f) * a ^ i,
    sum_mem fun i _ => MulMemClass.mul_mem (hf i) (_root_.pow_mem ha i), ?_⟩
  rw [F.projection_completedAeval_eq_sum, ← hax]
  simp [Algebra.smul_def]

/-- A power series with natural-number coefficients evaluates at a positive element of the
first completed ideal to a positive element. -/
theorem IsPositive.completedAeval_map_castRingHom {x : F.completionIdeal 1}
    (hx : F.IsPositive P (x : F.completion)) (g : PowerSeries ℕ) :
    F.IsPositive P (F.completedAeval x (PowerSeries.map (Nat.castRingHom R) g)) :=
  hx.completedAeval fun i => by simp

/-- If `P` contains `-1` and `x` is a positive element of the first completed ideal, then the
inverse of the unit `1 + x` is positive: it is the evaluation of the geometric series
`∑ (-1)ʲ Xʲ` at `x`. -/
theorem IsPositive.inv_of_val_eq_one_add {x : F.completionIdeal 1}
    (hx : F.IsPositive P (x : F.completion)) (hP : (-1 : B) ∈ P) {U : F.completionˣ}
    (hU : (U : F.completion) = 1 + x) : F.IsPositive P ((U⁻¹ : F.completionˣ) : F.completion) := by
  have h := congrArg (F.completedAeval (R := ℤ) x)
    (PowerSeries.mk_neg_one_pow_mul_one_add_eq_one ℤ)
  rw [map_mul, map_add, map_one, completedAeval_X, ← hU] at h
  rw [Units.inv_eq_of_mul_eq_one_left h]
  exact hx.completedAeval fun j => by simpa using _root_.pow_mem hP j

end Mei.AlgFiltration
