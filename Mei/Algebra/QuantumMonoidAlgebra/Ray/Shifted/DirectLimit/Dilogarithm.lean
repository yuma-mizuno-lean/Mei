/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit.Monomial
public import Mei.RingTheory.FilteredAlgebra.QuantumDilogarithm

/-!
# Global quantum dilogarithm actions

The quantum dilogarithm acts on Laurent monomials in the global coefficient
algebra by finite products when the pairing is nonnegative, and by products of
inverse linear factors when it is nonpositive. The input exponent can lie outside
the positive monoid. Only the ray generator has to have positive degree.

The formal rescaling identities are those of Nakanishi, *Pentagon relation in
quantum cluster scattering diagrams*, §2.3, equations (2.14) and (2.21),
arXiv:2202.01588v7, evaluated using the existing filtered-completion API.
-/

public noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)
  (n : d.monoid) (hn : 0 < d.degree n)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "x" => completedRayGenerator q β d.monoid d.degree
  (fun _ h => d.degree_nonneg h) n hn

private local instance : Ring (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Algebra R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Module R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Algebra R (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Ring (F).completion := inferInstance
private local instance : Algebra R (F).completion := inferInstance
private local instance : Module R (F).completion := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) :=
  inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance : AddCommMonoid (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : AddCommGroup (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Ring (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Algebra R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance

local notation "E" => positiveCompletionToDirectLimit q β d
local notation "z" => directLimitMonomial q β d hspan

private theorem embed_rayGenerator : E (x : (F).completion) = z n := by
  rw [coe_completedRayGenerator, positiveCompletionToDirectLimit_toCompletion q β d hspan]
  simpa only [coe_positiveMonomial] using (directLimitMonomial_eq q β d hspan n).symm

private theorem embed_inverse_linear (c : R) :
    E (Ring.inverse (1 + c • (x : (F).completion))) =
      Ring.inverse (1 + c • z n) := by
  have hu : IsUnit (1 + c • (x : (F).completion)) := by
    -- Typed map equalities keep the completion coercions stable during elaboration.
    have hm : (F).completedAeval x (PowerSeries.C c * PowerSeries.X) =
        algebraMap R (F).completion c * (x : (F).completion) :=
      (((F).completedAeval x).map_mul' _ _).trans
        (congrArg₂ (fun a b : (F).completion => a * b)
          ((F).completedAeval_C x c) ((F).completedAeval_X x))
    have he : (F).completedAeval x (1 + PowerSeries.C c * PowerSeries.X) =
        1 + algebraMap R (F).completion c * (x : (F).completion) :=
      (((F).completedAeval x).map_add' _ _).trans
        (congrArg₂ (fun a b : (F).completion => a + b) ((F).completedAeval x).map_one hm)
    have hs := he.trans (congrArg (fun a : (F).completion => 1 + a)
      (Algebra.smul_def c (x : (F).completion)).symm)
    exact hs ▸ (F).isUnit_completedAeval x (by simp)
  simpa only [map_add, map_one, _root_.map_smul, embed_rayGenerator q β d hspan n hn] using
    hu.map_ringInverse E

variable (hβ : β.IsAlt)
  (hq : ∀ j : ℕ, IsUnit ((q : R) ^ (j + 1) - (↑q⁻¹ : R) ^ (j + 1)))

include hβ

/-- For nonnegative pairing, the action on an arbitrary ambient monomial is a
finite ordered product in the global coefficient algebra. -/
theorem directLimitRayAction_quantumDilogarithm_of_nonneg (p : Γ) (r : ℕ)
    (hr : β n p = r) :
    directLimitRayAction q β d n hn (Units.quantumDilogarithmUnit q hq) (z p) =
      z p * ((List.range r).map fun j => 1 + ((q : R) ^ (2 * j + 1)) • z n).prod := by
  have he : ((q ^ (β n p - β p n) : Rˣ) : R) = (q : R) ^ (2 * r) := by
    rw [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul, hr,
      ← Nat.cast_ofNat, ← Nat.cast_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  have ha := directLimitRayAction_monomial q β d hspan n hn p
    (Units.quantumDilogarithmUnit q hq)
  simp only [Units.coe_quantumDilogarithmUnit, Units.coe_quantumDilogarithmUnit_inv, he] at ha
  have hb := congrArg E ((F).completedAeval_quantumDilogarithm_ratio_of_nonneg x q hq r)
  have hc : E (((List.range r).map fun j =>
      1 + ((q : R) ^ (2 * j + 1)) • (x : (F).completion)).prod) =
      ((List.range r).map fun j => 1 + ((q : R) ^ (2 * j + 1)) • z n).prod := by
    simp only [map_list_prod, List.map_map, Function.comp_def, map_add, map_one, _root_.map_smul,
      embed_rayGenerator q β d hspan n hn]
  exact ha.trans (congrArg (fun a => z p * a) (hb.trans hc))

/-- For nonpositive pairing, the global action is a finite product of inverse
linear factors. These inverses exist over any coefficient ring satisfying the
quantum-dilogarithm denominator hypotheses. -/
theorem directLimitRayAction_quantumDilogarithm_of_nonpos (p : Γ) (r : ℕ)
    (hr : β n p = -(r : ℤ)) :
    directLimitRayAction q β d n hn (Units.quantumDilogarithmUnit q hq) (z p) =
      z p * ((List.range r).map fun j =>
        Ring.inverse (1 + ((↑q⁻¹ : R) ^ (2 * j + 1)) • z n)).prod := by
  have he : ((q ^ (β n p - β p n) : Rˣ) : R) = (↑q⁻¹ : R) ^ (2 * r) := by
    rw [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul, hr, mul_neg,
      zpow_neg, ← inv_zpow, ← Nat.cast_ofNat, ← Nat.cast_mul, zpow_natCast,
      Units.val_pow_eq_pow_val]
  have ha := directLimitRayAction_monomial q β d hspan n hn p
    (Units.quantumDilogarithmUnit q hq)
  simp only [Units.coe_quantumDilogarithmUnit, Units.coe_quantumDilogarithmUnit_inv, he] at ha
  have hb := congrArg E ((F).completedAeval_quantumDilogarithm_ratio_of_nonpos x q hq r)
  have hc : E (((List.range r).map fun j =>
      Ring.inverse (1 + ((↑q⁻¹ : R) ^ (2 * j + 1)) • (x : (F).completion))).prod) =
      ((List.range r).map fun j =>
        Ring.inverse (1 + ((↑q⁻¹ : R) ^ (2 * j + 1)) • z n)).prod := by
    simp only [map_list_prod, List.map_map, Function.comp_def,
      embed_inverse_linear q β d hspan n hn]
  exact ha.trans (congrArg (fun a => z p * a) (hb.trans hc))

/-- Pairing one gives the two Laurent monomials of the quantum wall crossing. -/
theorem directLimitRayAction_quantumDilogarithm_of_pairing_one (p : Γ)
    (hp : β n p = 1) :
    directLimitRayAction q β d n hn (Units.quantumDilogarithmUnit q hq) (z p) =
      z p + z (p + n) := by
  have h := directLimitRayAction_quantumDilogarithm_of_nonneg q β d hspan n hn hβ hq
    p 1 (by simpa using hp)
  have he : (q : R) * ((q ^ β p n : Rˣ) : R) = 1 := by
    rw [← hβ.neg_eq n p, hp, zpow_neg_one]
    exact q.val_inv
  simpa only [List.range_succ, List.range_zero, List.map_append, List.map_nil,
    List.map_cons, List.prod_append, List.prod_nil, List.prod_cons, Nat.mul_zero,
    zero_add, pow_one, one_mul, mul_one, mul_add, mul_smul_comm,
    directLimitMonomial_mul, smul_smul, he, one_smul] using h

/-- Pairing two gives coefficients `1`, `q + q⁻¹`, and `1`, including for
ambient exponents outside the positive monoid. -/
theorem directLimitRayAction_quantumDilogarithm_of_pairing_two (p : Γ)
    (hp : β n p = 2) :
    directLimitRayAction q β d n hn (Units.quantumDilogarithmUnit q hq) (z p) =
      z p + ((q : R) + (↑q⁻¹ : R)) • z (p + n) + z (p + 2 • (n : Γ)) := by
  have h := directLimitRayAction_quantumDilogarithm_of_nonneg q β d hspan n hn hβ hq
    p 2 (by simpa using hp)
  have hpn : β p n = -2 := (hβ.neg_eq n p).symm.trans (congrArg Neg.neg hp)
  have hpn' : β (p + n) n = -2 := by rw [map_add, LinearMap.add_apply, hpn, hβ n, add_zero]
  have h₁ : (q : R) * ((q ^ (-2 : ℤ) : Rˣ) : R) = ↑q⁻¹ := by
    rw [← Units.val_mul]
    have hu : q * q ^ (-2 : ℤ) = q⁻¹ := by
      calc
        _ = q ^ (1 : ℤ) * q ^ (-2 : ℤ) := by rw [zpow_one]
        _ = q ^ (-1 : ℤ) := by rw [← zpow_add]; norm_num
        _ = q⁻¹ := zpow_neg_one q
    exact congrArg Units.val hu
  have h₃ : (q : R) ^ 3 * ((q ^ (-2 : ℤ) : Rˣ) : R) = q := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
    have hu : q ^ 3 * q ^ (-2 : ℤ) = q := by
      rw [← zpow_natCast, ← zpow_add]
      norm_num
    exact congrArg Units.val hu
  have hi : (q : R) ^ 3 * ((↑q⁻¹ : R) * ((q ^ (-2 : ℤ) : Rˣ) : R)) = 1 := by
    rw [mul_left_comm, h₃]
    exact q.inv_val
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_nil,
    List.map_cons, List.prod_append, List.prod_nil, List.prod_cons, one_mul, mul_one] at h
  norm_num only at h
  have hf : z p * (1 + (q : R) • z n) = z p + (↑q⁻¹ : R) • z (p + n) := by
    simp only [mul_add, mul_one, mul_smul_comm, directLimitMonomial_mul, hpn,
      smul_smul, h₁]
  rw [pow_one, ← mul_assoc, hf] at h
  simp only [add_mul, mul_add, mul_one, mul_smul_comm, smul_mul_assoc,
    directLimitMonomial_mul, hpn, hpn', smul_add, smul_smul, h₃, hi, one_smul] at h
  refine h.trans ?_
  rw [add_smul, two_smul, add_assoc p (n : Γ) n]
  abel

end Mei.QuantumMonoidAlgebra
