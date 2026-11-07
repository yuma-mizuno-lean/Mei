/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Units
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map
public import Mei.RingTheory.FilteredAlgebra.AlgHom
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Products of shifted coefficients for arbitrary quantum forms

Normalized monomial units give right conjugation without an alternating-form
assumption. Its character is the skew part of the form. Restriction to positive
coefficients preserves every degree and every filtration term. Products in
translated completed coordinates have the full bilinear scalar phase and this
normalized conjugation.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)

/-- Conjugation that moves a coefficient to the right of the origin monomial. -/
def monomialRightConjSkew (s : Γ) :
    QuantumMonoidAlgebra q β ≃ₐ[R] QuantumMonoidAlgebra q β :=
  MulSemiringAction.toAlgAut (ConjAct (QuantumMonoidAlgebra q β)ˣ) R
    (QuantumMonoidAlgebra q β) (ConjAct.toConjAct (monomialUnit q β s)⁻¹)

/-- Right conjugation places the normalized inverse monomial on the left. -/
theorem monomialRightConjSkew_apply (s : Γ) (a : QuantumMonoidAlgebra q β) :
    monomialRightConjSkew q β s a =
      (↑(monomialUnit q β s)⁻¹ : QuantumMonoidAlgebra q β) * a * monomial q β s := by
  simp only [monomialRightConjSkew, MulSemiringAction.toAlgAut_apply,
    MulSemiringAction.toAlgEquiv_apply, ConjAct.units_smul_def,
    ConjAct.ofConjAct_toConjAct, inv_inv, coe_monomialUnit]

/-- Right conjugation by the zero monomial is the identity. -/
@[simp]
theorem monomialRightConjSkew_zero (a : QuantumMonoidAlgebra q β) :
    monomialRightConjSkew q β 0 a = a := by
  simp only [monomialRightConjSkew_apply, coe_monomialUnit_inv, map_zero, zpow_zero,
    Units.val_one, one_smul, neg_zero, monomial_zero, one_mul, mul_one]

/-- The skew character controls conjugation for every bilinear form. -/
@[simp]
theorem monomialRightConjSkew_monomial (s u : Γ) :
    monomialRightConjSkew q β s (monomial q β u) =
      ((q ^ (β u s - β s u) : Rˣ) : R) • monomial q β u := by
  simpa only [monomialRightConjSkew_apply, coe_monomialUnit] using
    monomialUnit_inv_mul_monomial_mul q β s u

/-- Right monomial conjugation preserves every homogeneous piece. -/
private theorem monomialRightConjSkew_mem_grade (s : Γ) {u : Γ}
    {a : QuantumMonoidAlgebra q β} (ha : a ∈ grade q β u) :
    monomialRightConjSkew q β s a ∈ grade q β u := by
  obtain ⟨r, rfl⟩ := (mem_grade_iff q β u a).mp ha
  rw [_root_.map_smul, monomialRightConjSkew_monomial]
  exact (grade q β u).smul_mem r ((grade q β u).smul_mem _
    ((mem_grade_iff q β u _).mpr ⟨1, one_smul _ _⟩))

/-- A supported positive subalgebra is stable under right monomial conjugation. -/
private theorem monomialRightConjSkew_mem_positive (P : AddSubmonoid Γ) (s : Γ)
    {a : QuantumMonoidAlgebra q β} (ha : a ∈ positiveSubalgebra q β P) :
    monomialRightConjSkew q β s a ∈ positiveSubalgebra q β P := by
  have h : positiveSubalgebra q β P ≤
      (positiveSubalgebra q β P).comap (monomialRightConjSkew q β s).toAlgHom := by
    apply (supportedSubalgebra_le_iff (grade q β) P _).mpr
    intro u hu a ha
    exact le_supportedSubalgebra (grade q β) P hu
      (monomialRightConjSkew_mem_grade q β s ha)
  exact h ha

/-- Restrict right monomial conjugation to positive coefficients. -/
def positiveMonomialRightConjSkew (P : AddSubmonoid Γ) (s : Γ) :
    positiveSubalgebra q β P →ₐ[R] positiveSubalgebra q β P :=
  ((monomialRightConjSkew q β s).toAlgHom.comp (positiveSubalgebra q β P).val).codRestrict
    (positiveSubalgebra q β P) (fun a => monomialRightConjSkew_mem_positive q β P s a.property)

/-- Restriction keeps the original ambient algebra conjugation. -/
@[simp]
theorem coe_positiveMonomialRightConjSkew (P : AddSubmonoid Γ) (s : Γ)
    (a : positiveSubalgebra q β P) :
    (positiveMonomialRightConjSkew q β P s a : QuantumMonoidAlgebra q β) =
      monomialRightConjSkew q β s a := by
  -- codRestrict retains the ambient map and changes only its codomain.
  rfl

/-- Right conjugation at the zero origin fixes every positive coefficient. -/
@[simp]
theorem positiveMonomialRightConjSkew_zero (P : AddSubmonoid Γ)
    (a : positiveSubalgebra q β P) : positiveMonomialRightConjSkew q β P 0 a = a := by
  apply Subtype.ext
  simp only [coe_positiveMonomialRightConjSkew, monomialRightConjSkew_zero]

/-- Positive monomials have the same diagonal character as ambient monomials. -/
@[simp]
theorem positiveMonomialRightConjSkew_monomial (P : AddSubmonoid Γ) (s : Γ)
    (u : P) :
    positiveMonomialRightConjSkew q β P s (positiveMonomial q β P u) =
      ((q ^ (β u s - β s u) : Rˣ) : R) • positiveMonomial q β P u := by
  apply Subtype.ext
  simpa only [coe_positiveMonomial, Subalgebra.coe_smul,
    coe_positiveMonomialRightConjSkew] using
    monomialRightConjSkew_monomial q β s u

/-- Restricting monomial conjugation keeps the inherited grading fixed. -/
private theorem positiveMonomialRightConjSkew_mem_grading (P : AddSubmonoid Γ) (s : Γ)
    {u : Γ} {a : positiveSubalgebra q β P}
    (ha : a ∈ (positiveSubalgebra q β P).grading (grade q β) u) :
    positiveMonomialRightConjSkew q β P s a ∈
      (positiveSubalgebra q β P).grading (grade q β) u := by
  apply (Subalgebra.mem_grading_iff _ _).mpr
  rw [coe_positiveMonomialRightConjSkew]
  exact monomialRightConjSkew_mem_grade q β s ((Subalgebra.mem_grading_iff _ _).mp ha)

variable (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ u ∈ P, 0 ≤ δ u)

local notation "F" => positiveFiltration q β P δ hδ

/-- Monomial conjugation preserves every positive coefficient filtration term. -/
theorem positiveMonomialRightConjSkew_filtration_le (s : Γ) (k : ℕ) :
    (F).ideal k ≤ ((F).ideal k).comap (positiveMonomialRightConjSkew q β P s) := by
  classical
  rw [positiveFiltration_ideal, GradedAlgebra.degreeIdeal_le_iff]
  intro u hu a ha
  rw [Ideal.mem_comap]
  exact GradedAlgebra.le_degreeIdeal _ δ _ hu _
    (positiveMonomialRightConjSkew_mem_grading q β P s ha)

/-- Right monomial conjugation extends through the existing filtered algebra completion map. -/
def completedMonomialRightConjSkew (s : Γ) : (F).completion →ₐ[R] (F).completion :=
  (F).mapCompletionₐ (F) (positiveMonomialRightConjSkew q β P s) id monotone_id
    (fun k => positiveMonomialRightConjSkew_filtration_le q β P δ hδ s (k + 1))

/-- Forgetting scalars gives the filtered ring map of positive monomial conjugation. -/
@[simp]
theorem coe_completedMonomialRightConjSkew (s : Γ) :
    (completedMonomialRightConjSkew q β P δ hδ s : (F).completion →+* (F).completion) =
      (F).mapCompletion (F) (positiveMonomialRightConjSkew q β P s).toRingHom
        id monotone_id
        (fun k => positiveMonomialRightConjSkew_filtration_le q β P δ hδ s (k + 1)) :=
  (F).coe_mapCompletionₐ (F) _ id monotone_id _

/-- Each completed conjugation is computed by the corresponding quotient algebra map. -/
@[simp]
theorem projection_completedMonomialRightConjSkew (s : Γ) (k : ℕ)
    (a : (F).completion) :
    (F).projection k (completedMonomialRightConjSkew q β P δ hδ s a) =
      Ideal.quotientMapₐ ((F).ideal (k + 1)) (positiveMonomialRightConjSkew q β P s)
        (positiveMonomialRightConjSkew_filtration_le q β P δ hδ s (k + 1))
        ((F).projection k a) :=
  (F).projection_mapCompletionₐ (F) _ id monotone_id _ k a

/-- Completed right conjugation at the zero origin is the identity. -/
@[simp]
theorem completedMonomialRightConjSkew_zero (a : (F).completion) :
    completedMonomialRightConjSkew q β P δ hδ 0 a = a := by
  apply (F).completion_ext
  intro k
  let b : positiveSubalgebra q β P := Quotient.out ((F).projection k a)
  have hb : Ideal.Quotient.mk ((F).ideal (k + 1)) b = (F).projection k a :=
    Ideal.Quotient.mk_out _
  have h := projection_completedMonomialRightConjSkew q β P δ hδ 0 k a
  simpa only [← hb, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    positiveMonomialRightConjSkew_zero] using h

/-- Conjugation commutes with the canonical map to the positive completion. -/
@[simp]
theorem completedMonomialRightConjSkew_toCompletion (s : Γ)
    (a : positiveSubalgebra q β P) :
    completedMonomialRightConjSkew q β P δ hδ s ((F).toCompletion a) =
      (F).toCompletion (positiveMonomialRightConjSkew q β P s a) :=
  (F).mapCompletionₐ_toCompletion (F) _ id monotone_id _ a

/-- Products in translated coordinates have a scalar phase and right conjugation. -/
theorem shiftedMul_positiveShiftEquiv_skew (d : PositiveDegrees Γ) (p s : Γ)
    (a b : positiveSubalgebra q β d.monoid) :
    shiftedMul (grade q β) d.monoid p s
        (positiveShiftEquiv q β d p a) (positiveShiftEquiv q β d s b) =
      positiveShiftEquiv q β d (p + s)
        (((q ^ β p s : Rˣ) : R) • (positiveMonomialRightConjSkew q β d.monoid s a * b)) := by
  apply Subtype.ext
  simp only [coe_shiftedMul, coe_positiveShiftEquiv, Subalgebra.coe_smul,
    Subalgebra.coe_mul, coe_positiveMonomialRightConjSkew, monomialRightConjSkew_apply]
  rw [mul_smul_comm, ← smul_mul_assoc, ← monomial_mul]
  simp only [← mul_assoc]
  rw [mul_assoc (monomial q β p) (monomial q β s)
    (↑(monomialUnit q β s)⁻¹ : QuantumMonoidAlgebra q β),
    ← coe_monomialUnit q β s, Units.mul_inv, mul_one]

section Product

variable (d : PositiveDegrees Γ)

local notation "D" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

/-- Products of arbitrary completed shifted coefficients have the same corrected coordinates. -/
theorem shiftedCompletionMul_positiveCompletionShiftEquiv_skew
    (p s : Γ) (a b : (D).completion) :
    d.shiftedCompletionMul (grade q β) p s
        (positiveCompletionShiftEquiv q β d p a)
        (positiveCompletionShiftEquiv q β d s b) =
      positiveCompletionShiftEquiv q β d (p + s)
        (((q ^ β p s : Rˣ) : R) •
          (completedMonomialRightConjSkew q β d.monoid d.degree
            (fun _ h => d.degree_nonneg h) s a * b)) := by
  classical
  apply (d.shiftedFiltration (grade q β) (p + s)).completion_ext
  intro k
  let a₀ : positiveSubalgebra q β d.monoid := Quotient.out ((D).projection k a)
  let b₀ : positiveSubalgebra q β d.monoid := Quotient.out ((D).projection k b)
  have ha : Ideal.Quotient.mk ((D).ideal (k + 1)) a₀ = (D).projection k a :=
    Ideal.Quotient.mk_out _
  have hb : Ideal.Quotient.mk ((D).ideal (k + 1)) b₀ = (D).projection k b :=
    Ideal.Quotient.mk_out _
  have ht : (D).projection k (completedMonomialRightConjSkew q β d.monoid d.degree
        (fun _ h => d.degree_nonneg h) s a) =
      Ideal.Quotient.mk ((D).ideal (k + 1))
        (positiveMonomialRightConjSkew q β d.monoid s a₀) := by
    rw [projection_completedMonomialRightConjSkew, ← ha,
      Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
  have hab : (D).projection k
        (((q ^ β p s : Rˣ) : R) •
          (completedMonomialRightConjSkew q β d.monoid d.degree
            (fun _ h => d.degree_nonneg h) s a * b)) =
      Ideal.Quotient.mk ((D).ideal (k + 1))
        (((q ^ β p s : Rˣ) : R) •
          (positiveMonomialRightConjSkew q β d.monoid s a₀ * b₀)) :=
    AlgFiltration.projection_smul_mul_of_projections (D) (((q ^ β p s : Rˣ) : R))
      (positiveMonomialRightConjSkew q β d.monoid s a₀) b₀ _ b k ht hb.symm
  have hpa := projection_positiveCompletionShiftEquiv_of_projection q β d p k a a₀ ha.symm
  have hpb := projection_positiveCompletionShiftEquiv_of_projection q β d s k b b₀ hb.symm
  have hprod := d.projection_shiftedCompletionMul (grade q β) p s k
    (positiveCompletionShiftEquiv q β d p a)
    (positiveCompletionShiftEquiv q β d s b)
    (positiveShiftEquiv q β d p a₀) (positiveShiftEquiv q β d s b₀)
    hpa.symm hpb.symm
  have hcoord := congrArg (fun z : shiftedSubmodule (grade q β) d.monoid (p + s) =>
    (Submodule.Quotient.mk z : (d.shiftedFiltration (grade q β) (p + s)).quotient k))
    (shiftedMul_positiveShiftEquiv_skew q β d p s a₀ b₀)
  have hr := projection_positiveCompletionShiftEquiv_of_projection q β d (p + s) k _ _ hab
  exact hprod.trans (hcoord.trans hr.symm)

end Product

end Mei.QuantumMonoidAlgebra
