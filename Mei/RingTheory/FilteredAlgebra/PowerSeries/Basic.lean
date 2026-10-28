/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Algebra
public import Mei.RingTheory.PowerSeries.Nilpotent.Basic
import TauCeti.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Evaluating power series in a completed filtered algebra

An element of the first completed ideal is nilpotent at every finite order. Evaluate scalar
power series at these projections and use the existing inverse-limit algebra lift to obtain
an algebra homomorphism into the completion. Its finite projections are finite sums.

The scalar ring is any commutative ring, and the filtered algebra can be noncommutative.
No topology or separatedness assumption is needed.
-/

public section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

/-- Evaluate scalar power series at an element of the first completed ideal. -/
noncomputable def completedAeval (x : F.completionIdeal 1) :
    PowerSeries R →ₐ[R] F.completion :=
  F.liftₐ (fun k => PowerSeries.nilpotentAeval (F.isNilpotent_projection x.property k))
    (fun {k l} h => by
      ext f
      rw [AlgHom.comp_apply]
      rw [PowerSeries.map_nilpotentAeval]
      congr 2
      exact F.factor_projection h x)

/-- At finite order, completed evaluation is evaluation at the nilpotent projection. -/
@[simp]
theorem projection_completedAeval (x : F.completionIdeal 1) (k : ℕ) (f : PowerSeries R) :
    F.projection k (F.completedAeval x f) =
      PowerSeries.nilpotentAeval (F.isNilpotent_projection x.property k) f := by
  simp [completedAeval]

/-- At order `k`, only the first `k + 1` scalar coefficients contribute. -/
theorem projection_completedAeval_eq_sum (x : F.completionIdeal 1) (k : ℕ)
    (f : PowerSeries R) :
    F.projection k (F.completedAeval x f) =
      ∑ i ∈ Finset.range (k + 1), PowerSeries.coeff i f • F.projection k x ^ i := by
  rw [F.projection_completedAeval]
  exact PowerSeries.nilpotentAeval_eq_sum _ (F.projection_pow_eq_zero x.property k) f

/-- Constants evaluate to their scalar images in the completion. -/
@[simp]
theorem completedAeval_C (x : F.completionIdeal 1) (r : R) :
    F.completedAeval x (PowerSeries.C r) = algebraMap R F.completion r :=
  (F.completedAeval x).commutes r

/-- The variable evaluates to the chosen completed element. -/
@[simp]
theorem completedAeval_X (x : F.completionIdeal 1) :
    F.completedAeval (R := R) x PowerSeries.X = x := by
  apply F.completion_ext
  intro k
  simp

/-- On polynomials, completed evaluation is ordinary polynomial algebra evaluation. -/
@[simp]
theorem completedAeval_coe (x : F.completionIdeal 1) (p : Polynomial R) :
    F.completedAeval x (p : PowerSeries R) = Polynomial.aeval (x : F.completion) p := by
  rw [PowerSeries.algHom_coe_eq_aeval, F.completedAeval_X]

/-- A series with zero constant coefficient evaluates into the first completed ideal. -/
theorem completedAeval_mem_first (x : F.completionIdeal 1) {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) :
    F.completedAeval x f ∈ F.completionIdeal 1 := by
  rw [F.completionIdeal_succ 0, RingHom.mem_ker,
    F.projection_completedAeval_eq_sum]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]

/-- A series with invertible constant coefficient evaluates to a unit. -/
theorem isUnit_completedAeval (x : F.completionIdeal 1) {f : PowerSeries R}
    (hf : IsUnit (PowerSeries.constantCoeff f)) : IsUnit (F.completedAeval x f) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hf).map (F.completedAeval x)

/-- The formal inverse at an invertible constant coefficient evaluates to the inverse unit. -/
@[simp]
theorem completedAeval_invOfUnit (x : F.completionIdeal 1) (f : PowerSeries R) (u : Rˣ)
    (hf : PowerSeries.constantCoeff f = u) :
    F.completedAeval x (PowerSeries.invOfUnit f u) = Ring.inverse (F.completedAeval x f) := by
  apply left_inv_eq_right_inv (a := F.completedAeval x f)
  · rw [← map_mul, PowerSeries.invOfUnit_mul f u hf, map_one]
  · exact Ring.mul_inverse_cancel _ (F.isUnit_completedAeval x (hf ▸ u.isUnit))

/-- A scalar commutation factor rescales completed power-series evaluation. -/
theorem completedAeval_mul_of_semiconj (x : F.completionIdeal 1) (y : F.completion) (a : R)
    (h : SemiconjBy y (a • (x : F.completion)) x) (f : PowerSeries R) :
    F.completedAeval x f * y = y * F.completedAeval x (PowerSeries.rescale a f) := by
  apply F.completion_ext
  intro k
  simp only [map_mul, F.projection_completedAeval]
  apply PowerSeries.nilpotentAeval_mul_of_semiconj
  have hk := congrArg (F.projectionₐ (R := R) k) h
  simp only [map_mul, map_smul] at hk
  simpa only [SemiconjBy, F.projectionₐ_apply] using hk

/-- Conjugation by an evaluated unit series is its scalar rescaling ratio. -/
theorem completedAeval_conj (x : F.completionIdeal 1) (y : F.completion) (a : R)
    (h : SemiconjBy y (a • (x : F.completion)) x) (f : (PowerSeries R)ˣ) :
    F.completedAeval x (f : PowerSeries R) * y *
        F.completedAeval x (↑(f⁻¹) : PowerSeries R) =
      y * F.completedAeval x
        (PowerSeries.rescale a (f : PowerSeries R) * (↑(f⁻¹) : PowerSeries R)) := by
  rw [F.completedAeval_mul_of_semiconj x y a h, map_mul, mul_assoc]

end Mei.AlgFiltration
