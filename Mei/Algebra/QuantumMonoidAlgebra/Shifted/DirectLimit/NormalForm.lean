/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Positive.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Translation

/-!
# Monomial normal forms of global quantum coefficients

Every global coefficient is a negative positive-monoid monomial times a positive
completed coefficient. For a fixed monomial the positive coefficient is unique.
The result includes infinite families and arbitrary bilinear quantum twists.
The spanning hypothesis is used by the existing embedding of ordinary monomials.
No localization universal property is asserted here.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => d.ShiftedDirectLimit (grade q β)

omit [DecidableEq Γ] in
/-- Completed translation of the zero chart gives the usual positive coordinates. -/
theorem shiftedCompletedMonomialEquiv_positiveCompletionShiftEquiv_zero (p : Γ)
    (a : (F).completion) :
    shiftedCompletedMonomialEquiv q β p 0 d (positiveCompletionShiftEquiv q β d 0 a) =
      positiveCompletionShiftEquiv q β d (p + 0) a := by
  apply (d.shiftedFiltration (grade q β) (p + 0)).completion_ext
  intro k
  refine (Ideal.Quotient.mk_surjective ((F).projection k a)).elim fun b hb => ?_
  have h0 := projection_positiveCompletionShiftEquiv_of_projection q β d 0 k a b hb.symm
  have hp := projection_positiveCompletionShiftEquiv_of_projection q β d (p + 0) k a b hb.symm
  have ht := projection_shiftedCompletedMonomialEquiv q β p 0 d k
    (positiveCompletionShiftEquiv q β d 0 a)
  simp only [h0, Submodule.mapQ_apply, LinearEquiv.coe_coe] at ht
  have hf : shiftedMonomialEquiv q β d.monoid p 0 (positiveShiftEquiv q β d 0 b) =
      positiveShiftEquiv q β d (p + 0) b := by
    apply Subtype.ext
    simp only [coe_shiftedMonomialEquiv, coe_positiveShiftEquiv, add_zero, monomial_zero,
      one_mul]
  exact ht.trans ((congrArg Submodule.Quotient.mk hf).trans hp.symm)

variable (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)

/-- Monomial times a positive completion is exactly its translated chart coordinate. -/
theorem directLimitMonomial_mul_positiveCompletionToDirectLimit (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (a : (F).completion) :
    directLimitMonomial q β d hspan p * positiveCompletionToDirectLimit q β d a =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (positiveCompletionShiftEquiv q β d p a) := by
  have hzero : (0 : Γ) - d.coefficientOrigin 0 ∈ d.monoid := d.zero_coefficientOrigin_mem
  have hsum : p + 0 - d.coefficientOrigin s ∈ d.monoid := by simpa only [add_zero] using hp
  have ht := directLimitMonomial_mul_toShiftedDirectLimitOfChart q β d hspan p 0 0 s
    hzero hsum (positiveCompletionShiftEquiv q β d 0 a)
  have hc := congrArg (d.toShiftedDirectLimitOfChart (grade q β) (p + 0) s hsum)
    (shiftedCompletedMonomialEquiv_positiveCompletionShiftEquiv_zero q β d p a)
  have he := congrArg (fun z : G => directLimitMonomial q β d hspan p * z)
    (positiveCompletionToDirectLimit_apply q β d a)
  have hcast := toShiftedDirectLimitOfChart_positiveCompletionShiftEquiv_congr q β d
    (add_zero p) s hsum hp a
  exact (he).trans <|
    (ht).trans <|
    (hc).trans <|
    hcast

/-- For a fixed origin, the positive completed factor is uniquely determined. -/
theorem directLimitMonomial_mul_positiveCompletionToDirectLimit_injective (p : Γ) :
    Function.Injective (fun a =>
      directLimitMonomial q β d hspan p * positiveCompletionToDirectLimit q β d a) := by
  intro a b h
  apply positiveCompletionToDirectLimit_injective q β d
  have hc := congrArg (fun z : G => (↑(directLimitMonomialUnit q β d hspan p)⁻¹ : G) * z) h
  simpa only [← coe_directLimitMonomialUnit, ← mul_assoc, Units.inv_mul, one_mul] using hc

/-- A single negative positive-monoid exponent suffices for every global coefficient. -/
theorem exists_directLimitMonomial_mul_positiveCompletionToDirectLimit (x : G) :
    ∃ n : d.monoid, ∃ a : (F).completion,
      x = directLimitMonomial q β d hspan (-(n : Γ)) *
        positiveCompletionToDirectLimit q β d a := by
  refine (d.exists_toShiftedDirectLimit (grade q β) x).elim fun s hs => ?_
  refine hs.elim fun b hb => ?_
  let a := (positiveCompletionShiftEquiv q β d (d.coefficientOrigin s)).symm b
  have hp : d.coefficientOrigin s - d.coefficientOrigin s ∈ d.monoid := by simp
  have ht := directLimitMonomial_mul_positiveCompletionToDirectLimit q β d hspan
    (d.coefficientOrigin s) s hp a
  have he := congrArg (d.toShiftedDirectLimitOfChart (grade q β) (d.coefficientOrigin s) s hp)
    ((positiveCompletionShiftEquiv q β d (d.coefficientOrigin s)).apply_symm_apply b)
  have hc : d.toShiftedDirectLimitOfChart (grade q β) (d.coefficientOrigin s) s hp b =
      d.toShiftedDirectLimit (grade q β) s b := by
    rw [PositiveDegrees.toShiftedDirectLimitOfChart_apply,
      PositiveDegrees.shiftedCompletedInclusion_refl]
  refine ⟨s.sum, a, ?_⟩
  simpa only [PositiveDegrees.coefficientOrigin_eq_neg_sum] using
    (ht.trans (he.trans (hc.trans hb))).symm

end Mei.QuantumMonoidAlgebra
