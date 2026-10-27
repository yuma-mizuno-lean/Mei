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

For a unit `q` with all `q^(n+1) - q^(-(n+1))` invertible, construct the unique
series `Ψ` with constant coefficient one and `Ψ(q²X) = (1 + qX) Ψ(X)`.
The series is a unit, is natural under coefficient homomorphisms, and its finite
rescalings yield the products used in quantum wall actions.

We use the coefficient recurrence and uniqueness from
`PowerSeries.existsUnique_rescale_eq_one_add_C_mul_X_mul`. Our normalization is
Tomoki Nakanishi, *Pentagon relation in quantum cluster scattering diagrams*,
§2.3, equation (2.14); the finite products are those of (2.21),
arXiv:2202.01588v7. No infinite product convergence is asserted or needed.
-/

public section

noncomputable section

namespace PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem quantumDilog_denominators (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1)))
    (n : ℕ) : IsUnit (((q : R) ^ 2) ^ (n + 1) - 1) :=
  q.isUnit_sq_pow_sub_one (n + 1) (h n)

/-- The normalized formal quantum dilogarithm. Its defining difference equation
uses the indicated invertible quantum denominators. -/
def quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) :
    PowerSeries R :=
  (existsUnique_rescale_eq_one_add_C_mul_X_mul ((q : R) ^ 2) (q : R)
    (quantumDilog_denominators q h)).exists.choose

private theorem quantumDilog_spec (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) :
    constantCoeff (quantumDilog q h) = 1 ∧
      rescale ((q : R) ^ 2) (quantumDilog q h) = (1 + C (q : R) * X) * quantumDilog q h :=
  (existsUnique_rescale_eq_one_add_C_mul_X_mul ((q : R) ^ 2) (q : R)
    (quantumDilog_denominators q h)).exists.choose_spec

/-- The quantum dilogarithm has constant coefficient one. -/
@[simp]
theorem constantCoeff_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) :
    constantCoeff (quantumDilog q h) = 1 := (quantumDilog_spec q h).1

/-- The defining quantum difference equation. -/
theorem rescale_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) :
    rescale ((q : R) ^ 2) (quantumDilog q h) =
      (1 + C (q : R) * X) * quantumDilog q h := (quantumDilog_spec q h).2

/-- The normalized quantum difference equation characterizes the series. -/
theorem eq_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1)))
    {F : PowerSeries R} (h₀ : constantCoeff F = 1)
    (hF : rescale ((q : R) ^ 2) F = (1 + C (q : R) * X) * F) : F = quantumDilog q h :=
  eq_of_rescale_eq_one_add_C_mul_X_mul _ _
    (fun n => (quantumDilog_denominators q h n).isRegular.left)
    (h₀.trans (constantCoeff_quantumDilog q h).symm) hF (rescale_quantumDilog q h)

/-- The normalized series is invertible over arbitrary commutative coefficient rings. -/
@[simp]
theorem isUnit_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) :
    IsUnit (quantumDilog q h) :=
  isUnit_iff_constantCoeff.mpr (by simp)

/-- The coefficient recursion, with inverses taken only of units. -/
theorem coeff_succ_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) (n : ℕ) :
    coeff (n + 1) (quantumDilog q h) =
      (q : R) * coeff n (quantumDilog q h) * Ring.inverse (((q : R) ^ 2) ^ (n + 1) - 1) := by
  rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ (quantumDilog_denominators q h n), mul_comm]
  exact coeff_succ_mul_sub_of_rescale_eq (rescale_quantumDilog q h) n

/-- Coefficient homomorphisms preserve the normalized quantum dilogarithm.
The target denominator hypotheses follow by mapping the source units. -/
@[simp]
theorem map_quantumDilog (φ : R →+* S) (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) :
    (quantumDilog q h).map φ = quantumDilog (Units.map φ.toMonoidHom q)
      (fun n => by simpa using (h n).map φ) := by
  have hmap : ((Units.map φ.toMonoidHom q : Sˣ) : S) = φ (q : R) :=
    Units.coe_map φ.toMonoidHom q
  apply eq_quantumDilog
  · rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [coeff_map, coeff_zero_eq_constantCoeff_apply, constantCoeff_quantumDilog, map_one]
  · rw [hmap]
    simpa only [← rescale_map, map_pow, map_mul, map_add, map_one, map_C, map_X] using
      congrArg (PowerSeries.map φ) (rescale_quantumDilog q h)

/-- Positive finite rescalings give the odd-power product in quantum ray actions,
including the empty product. -/
theorem rescale_pow_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) (r : ℕ) :
    rescale ((q : R) ^ (2 * r)) (quantumDilog q h) =
      (∏ j ∈ Finset.range r, (1 + C ((q : R) ^ (2 * j + 1)) * X)) * quantumDilog q h := by
  have hq (j : ℕ) : (q : R) * (q : R) ^ (2 * j) = (q : R) ^ (2 * j + 1) := by
    rw [pow_succ, mul_comm]
  simpa only [← pow_mul, hq] using
    rescale_pow_of_rescale_eq (rescale_quantumDilog q h) r

/-- Negative finite rescalings give the product of inverses with negative odd
powers, in the normalization used for reverse quantum crossings. -/
theorem rescale_inv_pow_quantumDilog (q : Rˣ)
    (h : ∀ n : ℕ, IsUnit ((q : R) ^ (n + 1) - ((q⁻¹ : Rˣ) : R) ^ (n + 1))) (r : ℕ) :
    rescale (((q⁻¹ : Rˣ) : R) ^ (2 * r)) (quantumDilog q h) =
      (∏ j ∈ Finset.range r,
        Ring.inverse (1 + C (((q⁻¹ : Rˣ) : R) ^ (2 * j + 1)) * X)) * quantumDilog q h := by
  have hq (j : ℕ) : (q : R) * ((q⁻¹ : Rˣ) : R) ^ (2 * (j + 1)) =
      ((q⁻¹ : Rˣ) : R) ^ (2 * j + 1) := by
    have hexp : 2 * (j + 1) = 1 + (2 * j + 1) := by omega
    rw [hexp, pow_add, pow_one, ← mul_assoc]
    simp
  have he := rescale_inv_pow_of_rescale_eq (a := q ^ 2) (rescale_quantumDilog q h) r
  simp only [Units.inv_pow_eq_pow_inv, ← pow_mul, hq] at he
  exact he

end PowerSeries
