/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# The formal quantum dilogarithm

For a unit `q` such that every `q^j - q^(-j)`, `j > 0`, is a unit, construct
the unique power series with constant coefficient one satisfying
`Ψ(q² X) = (1 + q X) Ψ(X)`. Iterating this equation gives the finite products
that appear in conjugation by a quantum dilogarithm.

The construction uses Mathlib's `PowerSeries.mk`, `PowerSeries.rescale` and
`PowerSeries.invOfUnit`; no convergence, field or characteristic assumption is
needed. The convention is that of Nakanishi, *Pentagon relation in quantum
cluster scattering diagrams*, §2.3, equations (2.14) and (2.21),
arXiv:2202.01588v7.
-/

public section

noncomputable section

namespace Units

open PowerSeries

variable {R : Type*} [CommRing R] (q : Rˣ)
  (hq : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - (↑q⁻¹ : R) ^ (n + 1)))

private def dilogDenominator (n : ℕ) : Rˣ := q ^ (n + 1) * (hq n).unit

private theorem dilogDenominator_val (n : ℕ) :
    (dilogDenominator q hq n : R) = (q : R) ^ (2 * (n + 1)) - 1 := by
  simp only [dilogDenominator, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, mul_sub]
  simp only [← mul_pow, Units.mul_inv, one_pow, ← pow_two, ← pow_mul, mul_comm]

/-- The quantum dilogarithm with constant coefficient one, characterized by
`Ψ(q² X) = (1 + q X) Ψ(X)`. The hypothesis supplies all its denominators. -/
def quantumDilogarithm : PowerSeries R :=
  PowerSeries.mk fun n => ((∏ j ∈ Finset.range n, q * (dilogDenominator q hq j)⁻¹ : Rˣ) : R)

private theorem coeff_quantumDilogarithm (n : ℕ) :
    coeff n (quantumDilogarithm q hq) =
      ((∏ j ∈ Finset.range n, q * (dilogDenominator q hq j)⁻¹ : Rˣ) : R) := by
  simp [quantumDilogarithm]

/-- The constant coefficient is one. -/
@[simp]
theorem constantCoeff_quantumDilogarithm : constantCoeff (quantumDilogarithm q hq) = 1 := by
  simp [quantumDilogarithm, PowerSeries.constantCoeff_mk]

/-- The coefficient recurrence forced by the q-difference equation. -/
theorem coeff_quantumDilogarithm_succ (n : ℕ) :
    ((q : R) ^ (2 * (n + 1)) - 1) * coeff (n + 1) (quantumDilogarithm q hq) =
      (q : R) * coeff n (quantumDilogarithm q hq) := by
  rw [← dilogDenominator_val q hq n]
  simp only [coeff_quantumDilogarithm, Finset.prod_range_succ, Units.val_mul]
  calc
    _ = (q : R) * ((∏ j ∈ Finset.range n, q * (dilogDenominator q hq j)⁻¹ : Rˣ) : R) *
        ((dilogDenominator q hq n : R) * ↑(dilogDenominator q hq n)⁻¹) := by ring
    _ = _ := by simp

/-- The defining q-difference equation. -/
theorem rescale_quantumDilogarithm :
    rescale ((q : R) ^ 2) (quantumDilogarithm q hq) =
      (1 + C (q : R) * X) * quantumDilogarithm q hq := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have h := coeff_quantumDilogarithm_succ q hq n
    simp only [coeff_rescale, add_mul, one_mul, mul_assoc,
      map_add, coeff_C_mul, coeff_succ_X_mul]
    linear_combination h

/-- The quantum dilogarithm is an invertible series. -/
theorem isUnit_quantumDilogarithm : IsUnit (quantumDilogarithm q hq) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)

/-- Constant coefficient one and the q-difference equation uniquely determine the series. -/
theorem quantumDilogarithm_unique (f : PowerSeries R) (hzero : constantCoeff f = 1)
    (heq : rescale ((q : R) ^ 2) f = (1 + C (q : R) * X) * f) :
    f = quantumDilogarithm q hq := by
  ext n
  induction n with
  | zero => simpa using hzero
  | succ n hn =>
    have h := congrArg (coeff (n + 1)) heq
    simp only [coeff_rescale, add_mul, one_mul, mul_assoc, map_add,
      coeff_C_mul, coeff_succ_X_mul, ← pow_mul] at h
    have hd := coeff_quantumDilogarithm_succ q hq n
    apply (dilogDenominator q hq n).isUnit.mul_left_cancel
    rw [dilogDenominator_val]
    linear_combination h - hd + (q : R) * hn

/-- Positive even rescalings multiply the dilogarithm by a finite product of linear factors. -/
theorem rescale_pow_quantumDilogarithm (r : ℕ) :
    rescale ((q : R) ^ (2 * r)) (quantumDilogarithm q hq) =
      (∏ j ∈ Finset.range r, (1 + C ((q : R) ^ (2 * j + 1)) * X)) *
        quantumDilogarithm q hq := by
  induction r with
  | zero => simp
  | succ r hr =>
    calc
      _ = rescale ((q : R) ^ (2 * r))
          (rescale ((q : R) ^ 2) (quantumDilogarithm q hq)) := by
        have hp : (q : R) ^ 2 * (q : R) ^ (2 * r) =
            (q : R) ^ (2 * (r + 1)) := by ring
        rw [rescale_rescale, hp]
      _ = rescale ((q : R) ^ (2 * r))
          ((1 + C (q : R) * X) * quantumDilogarithm q hq) := by
        rw [rescale_quantumDilogarithm]
      _ = _ := by
        simp only [map_mul, map_add, map_one, rescale_C, rescale_X, hr,
          Finset.prod_range_succ]
        rw [← mul_assoc (C (q : R)) (C ((q : R) ^ (2 * r))), ← C.map_mul]
        have hpow : (q : R) * (q : R) ^ (2 * r) = (q : R) ^ (2 * r + 1) := by ring
        rw [hpow]
        ring

/-- Dividing a positive rescaling by the dilogarithm yields its finite ray multiplier. -/
theorem rescale_pow_quantumDilogarithm_mul_inv (r : ℕ) :
    rescale ((q : R) ^ (2 * r)) (quantumDilogarithm q hq) *
        invOfUnit (quantumDilogarithm q hq) 1 =
      ∏ j ∈ Finset.range r, (1 + C ((q : R) ^ (2 * j + 1)) * X) := by
  rw [rescale_pow_quantumDilogarithm, mul_assoc,
    PowerSeries.mul_invOfUnit _ 1 (by simp), mul_one]

private theorem rescale_inv_sq_quantumDilogarithm :
    rescale ((↑q⁻¹ : R) ^ 2) (quantumDilogarithm q hq) *
      (1 + C (↑q⁻¹ : R) * X) = quantumDilogarithm q hq := by
  have h := congrArg (rescale ((↑q⁻¹ : R) ^ 2)) (rescale_quantumDilogarithm q hq)
  simp only [rescale_rescale, ← mul_pow, Units.mul_inv, one_pow, rescale_one,
    RingHom.id_apply, map_mul, map_add, map_one, rescale_C, rescale_X] at h
  have hi : (q : R) * (↑q⁻¹ : R) ^ 2 = ↑q⁻¹ := by
    rw [pow_two, ← mul_assoc, Units.mul_inv, one_mul]
  rw [← mul_assoc, ← C.map_mul, hi, mul_comm] at h
  exact h.symm

/-- Negative even rescalings cancel a finite product of inverse-parameter linear factors. -/
theorem rescale_inv_pow_quantumDilogarithm_mul_prod (r : ℕ) :
    rescale ((↑q⁻¹ : R) ^ (2 * r)) (quantumDilogarithm q hq) *
      (∏ j ∈ Finset.range r, (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X)) =
        quantumDilogarithm q hq := by
  induction r with
  | zero => simp
  | succ r hr =>
    have h := congrArg (rescale ((↑q⁻¹ : R) ^ (2 * r)))
      (rescale_inv_sq_quantumDilogarithm q hq)
    simp only [map_mul, map_add, map_one, rescale_C, rescale_X, rescale_rescale] at h
    have hp : (↑q⁻¹ : R) ^ 2 * (↑q⁻¹ : R) ^ (2 * r) =
        (↑q⁻¹ : R) ^ (2 * (r + 1)) := by ring
    have hc : (↑q⁻¹ : R) * (↑q⁻¹ : R) ^ (2 * r) =
        (↑q⁻¹ : R) ^ (2 * r + 1) := by ring
    rw [hp, ← mul_assoc, ← C.map_mul, hc] at h
    rw [Finset.prod_range_succ]
    calc
      _ = (rescale ((↑q⁻¹ : R) ^ (2 * (r + 1))) (quantumDilogarithm q hq) *
          (1 + C ((↑q⁻¹ : R) ^ (2 * r + 1)) * X)) *
            ∏ j ∈ Finset.range r, (1 + C ((↑q⁻¹ : R) ^ (2 * j + 1)) * X) := by ring
      _ = _ := by rw [h, hr]

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
