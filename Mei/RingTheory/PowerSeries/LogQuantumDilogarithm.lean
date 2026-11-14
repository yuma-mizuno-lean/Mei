/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.RingTheory.PowerSeries.Log
public import Mei.RingTheory.PowerSeries.QuantumDilogarithm
import TauCeti.RingTheory.PowerSeries.Log

/-!
# The logarithm of the formal quantum dilogarithm

Let `R` be a commutative `ℚ`-algebra and `q` a unit such that every `q^k - q^(-k)`, `k > 0`,
is a unit. The formal logarithm `L = log Ψ_q` of the quantum dilogarithm satisfies the additive
`q`-difference equation `L(q² T) = log(1 + q T) + L(T)`
(`Units.rescale_logOf_quantumDilogarithm`). Comparing coefficients gives
`log Ψ_q(T) = ∑_{k ≥ 1} (-1)^(k-1) T^k / (k (q^k - q^(-k)))`
(`Units.coeff_succ_logOf_quantumDilogarithm`, `Units.logOf_quantumDilogarithm`).

The difference equation is the formal logarithm of the defining equation
`Ψ_q(q² T) = (1 + q T) Ψ_q(T)`, by `PowerSeries.logOf_rescale` and Tau Ceti's
`PowerSeries.logOf_mul`. This is the expansion of the quantum dilogarithm in Nakanishi,
*Pentagon relation in quantum cluster scattering diagrams*, §2.3, arXiv:2202.01588v7.
-/

public section

noncomputable section

namespace Units

open PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R] (q : Rˣ)
  (hq : ∀ k : ℕ, IsUnit ((q : R) ^ (k + 1) - (↑q⁻¹ : R) ^ (k + 1)))

/-- The logarithm of the quantum dilogarithm has zero constant coefficient. -/
@[simp]
theorem constantCoeff_logOf_quantumDilogarithm :
    constantCoeff (logOf (q.quantumDilogarithm hq)) = 0 :=
  constantCoeff_logOf (constantCoeff_quantumDilogarithm q hq)

/-- The logarithm `L` of the quantum dilogarithm satisfies `L(q² T) = log(1 + q T) + L(T)`. -/
theorem rescale_logOf_quantumDilogarithm :
    rescale ((q : R) ^ 2) (logOf (q.quantumDilogarithm hq)) =
      rescale (q : R) (log R) + logOf (q.quantumDilogarithm hq) := by
  have hΨ := constantCoeff_quantumDilogarithm q hq
  have hX : rescale (q : R) (1 + X) = 1 + C (q : R) * X := by
    rw [map_add, map_one, rescale_X]
  rw [← logOf_rescale _ _ hΨ, rescale_quantumDilogarithm,
    logOf_mul (by simp) hΨ, ← logOf_one_add_X, ← logOf_rescale _ _ (by simp), hX]

/-- The coefficient of `T^(k+1)` in `log Ψ_q(T)` is `(-1)^k / ((k + 1) (q^(k+1) - q^(-(k+1))))`.
The hypothesis `hq` makes every denominator `q^(k+1) - q^(-(k+1))` a unit. -/
@[simp]
theorem coeff_succ_logOf_quantumDilogarithm (k : ℕ) :
    coeff (k + 1) (logOf (q.quantumDilogarithm hq)) =
      algebraMap ℚ R ((-1 : ℚ) ^ k / (k + 1)) *
        Ring.inverse ((q : R) ^ (k + 1) - (↑q⁻¹ : R) ^ (k + 1)) := by
  have h := congrArg (coeff (k + 1)) (rescale_logOf_quantumDilogarithm q hq)
  simp only [coeff_rescale, map_add, coeff_log, Nat.add_one_ne_zero, ↓reduceIte] at h
  -- Clear the common unit factor `q^(k+1)` of `(q²)^(k+1) - 1` and `q^(k+1)`.
  have hinv : (q : R) ^ (k + 1) * (↑q⁻¹ : R) ^ (k + 1) = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  have hs : (-1 : ℚ) ^ (k + 1 + 1) = (-1) ^ k := by
    rw [pow_add, pow_add]
    norm_num
  rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hq k)]
  apply (q.isUnit.pow (k + 1)).mul_left_cancel
  rw [Nat.cast_add_one, hs] at h
  linear_combination h - (coeff (k + 1) (logOf (q.quantumDilogarithm hq))) * hinv

/-- The expansion `log Ψ_q(T) = ∑_{k ≥ 1} (-1)^(k-1) T^k / (k (q^k - q^(-k)))`, under the
hypothesis `hq` that every `q^k - q^(-k)`, `k > 0`, is a unit. -/
theorem logOf_quantumDilogarithm :
    logOf (q.quantumDilogarithm hq) = PowerSeries.mk fun k => if k = 0 then 0 else
      algebraMap ℚ R ((-1 : ℚ) ^ (k + 1) / k) * Ring.inverse ((q : R) ^ k - (↑q⁻¹ : R) ^ k) := by
  ext (_ | k)
  · simp
  · simp only [coeff_succ_logOf_quantumDilogarithm, coeff_mk, Nat.add_one_ne_zero, ↓reduceIte,
      pow_succ, mul_neg_one, neg_neg, Nat.cast_succ]

end Units
