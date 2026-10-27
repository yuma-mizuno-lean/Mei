/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.PowerSeries.DifferenceEquation
public import Mei.Algebra.Ring.Units

/-!
# The formal quantum dilogarithm

For a unit `q` such that every `q^j - q^(-j)`, `j > 0`, is a unit, construct
the unique power series with constant coefficient one satisfying
`Ψ(q² X) = (1 + q X) Ψ(X)`. Iterating this equation gives the finite products
that appear in conjugation by a quantum dilogarithm.

The construction uses Mathlib's `PowerSeries.mk`, `PowerSeries.rescale` and
`Ring.inverse` through the general difference-equation API, including
`PowerSeries.existsUnique_rescale_eq_one_add_C_mul_X_mul`. No convergence, field or
characteristic assumption is needed. The convention is that of Nakanishi,
*Pentagon relation in quantum cluster scattering diagrams*, §2.3, equations (2.14) and (2.21),
arXiv:2202.01588v7.
-/

public section

noncomputable section

namespace Units

open PowerSeries

variable {R : Type*} [CommRing R] (q : Rˣ)
  (hq : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - (↑q⁻¹ : R) ^ (n + 1)))

include hq in
private theorem dilogDenominators (n : ℕ) :
    IsUnit (((q : R) ^ 2) ^ (n + 1) - 1) :=
  q.isUnit_sq_pow_sub_one (n + 1) (hq n)

/-- The quantum dilogarithm with constant coefficient one, characterized by
`Ψ(q² X) = (1 + q X) Ψ(X)`. The hypothesis supplies all its denominators. -/
def quantumDilogarithm : PowerSeries R :=
  (existsUnique_rescale_eq_one_add_C_mul_X_mul ((q : R) ^ 2) (q : R)
    (dilogDenominators q hq)).exists.choose

private theorem quantumDilogarithm_spec :
    constantCoeff (quantumDilogarithm q hq) = 1 ∧
      rescale ((q : R) ^ 2) (quantumDilogarithm q hq) =
        (1 + C (q : R) * X) * quantumDilogarithm q hq :=
  (existsUnique_rescale_eq_one_add_C_mul_X_mul ((q : R) ^ 2) (q : R)
    (dilogDenominators q hq)).exists.choose_spec

/-- The constant coefficient is one. -/
@[simp]
theorem constantCoeff_quantumDilogarithm : constantCoeff (quantumDilogarithm q hq) = 1 :=
  (quantumDilogarithm_spec q hq).1

/-- The defining q-difference equation. -/
theorem rescale_quantumDilogarithm :
    rescale ((q : R) ^ 2) (quantumDilogarithm q hq) =
      (1 + C (q : R) * X) * quantumDilogarithm q hq :=
  (quantumDilogarithm_spec q hq).2

/-- The coefficient recurrence forced by the q-difference equation. -/
theorem coeff_quantumDilogarithm_succ (n : ℕ) :
    ((q : R) ^ (2 * (n + 1)) - 1) * coeff (n + 1) (quantumDilogarithm q hq) =
      (q : R) * coeff n (quantumDilogarithm q hq) := by
  simpa only [← pow_mul] using
    coeff_succ_mul_sub_of_rescale_eq (rescale_quantumDilogarithm q hq) n

/-- The coefficient recursion, with inverses taken only of units. -/
theorem coeff_succ_quantumDilogarithm (n : ℕ) :
    coeff (n + 1) (quantumDilogarithm q hq) =
      (q : R) * coeff n (quantumDilogarithm q hq) *
        Ring.inverse (((q : R) ^ 2) ^ (n + 1) - 1) := by
  rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ (dilogDenominators q hq n), mul_comm]
  exact coeff_succ_mul_sub_of_rescale_eq (rescale_quantumDilogarithm q hq) n

/-- The quantum dilogarithm is an invertible series. -/
@[simp]
theorem isUnit_quantumDilogarithm : IsUnit (quantumDilogarithm q hq) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)

/-- Constant coefficient one and the q-difference equation uniquely determine the series. -/
theorem quantumDilogarithm_unique (f : PowerSeries R) (hzero : constantCoeff f = 1)
    (heq : rescale ((q : R) ^ 2) f = (1 + C (q : R) * X) * f) :
    f = quantumDilogarithm q hq := by
  exact eq_of_rescale_eq_one_add_C_mul_X_mul _ _
    (fun n => (dilogDenominators q hq n).isRegular.left)
    (hzero.trans (constantCoeff_quantumDilogarithm q hq).symm)
    heq (rescale_quantumDilogarithm q hq)

/-- Positive even rescalings multiply the dilogarithm by a finite product of linear factors. -/
theorem rescale_pow_quantumDilogarithm (r : ℕ) :
    rescale ((q : R) ^ (2 * r)) (quantumDilogarithm q hq) =
      (∏ j ∈ Finset.range r, (1 + C ((q : R) ^ (2 * j + 1)) * X)) *
        quantumDilogarithm q hq := by
  have hp (j : ℕ) : (q : R) * (q : R) ^ (2 * j) = (q : R) ^ (2 * j + 1) := by
    rw [pow_succ, mul_comm]
  simpa only [← pow_mul, hp] using
    rescale_pow_of_rescale_eq (rescale_quantumDilogarithm q hq) r

/-- Dividing a positive rescaling by the dilogarithm yields its finite ray multiplier. -/
theorem rescale_pow_quantumDilogarithm_mul_inv (r : ℕ) :
    rescale ((q : R) ^ (2 * r)) (quantumDilogarithm q hq) *
        invOfUnit (quantumDilogarithm q hq) 1 =
      ∏ j ∈ Finset.range r, (1 + C ((q : R) ^ (2 * j + 1)) * X) := by
  rw [rescale_pow_quantumDilogarithm, mul_assoc,
    PowerSeries.mul_invOfUnit _ 1 (by simp), mul_one]

/-- Negative even rescalings cancel a finite product of inverse-parameter linear factors. -/
theorem rescale_inv_pow_quantumDilogarithm_mul_prod (r : ℕ) :
    rescale ((↑q⁻¹ : R) ^ (2 * r)) (quantumDilogarithm q hq) *
      (∏ j ∈ Finset.range r, (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X)) =
        quantumDilogarithm q hq := by
  have hp (j : ℕ) : (q : R) * (↑q⁻¹ : R) ^ (2 * (j + 1)) =
      (↑q⁻¹ : R) ^ (2 * j + 1) := by
    have hexp : 2 * (j + 1) = 1 + (2 * j + 1) := by omega
    rw [hexp, pow_add, pow_one, ← mul_assoc]
    simp
  have he := rescale_inv_pow_of_rescale_eq (a := q ^ 2)
    (rescale_quantumDilogarithm q hq) r
  simp only [Units.inv_pow_eq_pow_inv, ← pow_mul, hp] at he
  rw [he, mul_right_comm, ← Finset.prod_mul_distrib]
  have hcancel : ∀ j : ℕ, Ring.inverse (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X) *
      (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X) = (1 : PowerSeries R) := by
    intro j
    exact Ring.inverse_mul_cancel _ (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp))
  simp only [hcancel, Finset.prod_const_one, one_mul]

/-- Dividing a negative rescaling by the dilogarithm gives the product of inverse linear factors. -/
theorem rescale_inv_pow_quantumDilogarithm_mul_inv (r : ℕ) :
    rescale ((↑q⁻¹ : R) ^ (2 * r)) (quantumDilogarithm q hq) *
        invOfUnit (quantumDilogarithm q hq) 1 =
      ∏ j ∈ Finset.range r,
        invOfUnit (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X) 1 := by
  let P : PowerSeries R :=
    ∏ j ∈ Finset.range r, (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X)
  let Q : PowerSeries R :=
    ∏ j ∈ Finset.range r, invOfUnit (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X) 1
  have hPQ : P * Q = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    exact PowerSeries.mul_invOfUnit _ 1 (by simp)
  have h := rescale_inv_pow_quantumDilogarithm_mul_prod q hq r
  calc
    _ = rescale ((↑q⁻¹ : R) ^ (2 * r)) (quantumDilogarithm q hq) * P * Q *
        invOfUnit (quantumDilogarithm q hq) 1 := by rw [mul_assoc _ P, hPQ, mul_one]
    _ = quantumDilogarithm q hq * Q * invOfUnit (quantumDilogarithm q hq) 1 := by rw [h]
    _ = Q * (quantumDilogarithm q hq * invOfUnit (quantumDilogarithm q hq) 1) := by ring
    _ = _ := by rw [PowerSeries.mul_invOfUnit _ 1 (by simp), mul_one]

/-- Coefficient maps preserving the parameter preserve the quantum dilogarithm. -/
@[simp]
theorem map_quantumDilogarithm {S : Type*} [CommRing S] (φ : R →+* S) :
    PowerSeries.map φ (quantumDilogarithm q hq) =
      quantumDilogarithm (Units.map φ.toMonoidHom q) (fun n => by
        simpa only [Units.coe_map, Units.coe_map_inv, RingHom.toMonoidHom_eq_coe,
          MonoidHom.coe_ofClass, ← map_pow, ← map_sub] using (hq n).map φ) := by
  apply quantumDilogarithm_unique
  · simpa only [← coeff_zero_eq_constantCoeff_apply, coeff_map, map_one] using
      congrArg φ (constantCoeff_quantumDilogarithm q hq)
  · have h := congrArg (PowerSeries.map φ) (rescale_quantumDilogarithm q hq)
    simpa only [← PowerSeries.rescale_map, map_pow, Units.coe_map, map_mul, map_add,
      map_one, PowerSeries.map_C, PowerSeries.map_X, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass] using h

end Units
