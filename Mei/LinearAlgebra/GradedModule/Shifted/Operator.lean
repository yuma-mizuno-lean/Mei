/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.LinearMap
public import Mei.LinearAlgebra.GradedModule.Shifted.Finite

/-!
# Homogeneous operators into finite shifted coefficients

Linear maps from an arbitrary input module into a finite shifted quotient are
exactly the direct sum of maps into the retained ambient homogeneous pieces.
Finiteness is on the degree cutoff; no finite generation or projectivity of the
input module is needed. The comparison reads whole homogeneous components
pointwise and commutes with quotient transitions.

These operator coefficients allow statements about all incoming coefficients
simultaneously, while retaining the quotient carrier used by filtered actions.
The variable-input construction is used in Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open scoped DirectSum

namespace Mei.PositiveDegrees

variable {Γ R M H : Type*} [AddCommGroup Γ] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid H] [Module R H]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

/-- Homogeneous operator coefficients at finite order identify with all linear maps
into the shifted quotient, without a finite-generation assumption on the input. -/
def operatorCoefficientsEquiv (k : ℕ) :
    (⨁ n : d.cutoff k, H →ₗ[R] ℳ (p + n.val)) ≃ₗ[R]
      (H →ₗ[R] (d.shiftedFiltration ℳ p).quotient k) :=
  (DirectSum.linearMapEquivOfFintype (fun n : d.cutoff k => ℳ (p + n.val))).trans
    (LinearEquiv.congrRight (d.shiftedQuotientEquivDirectSum ℳ p k).symm)

/-- Evaluating an assembled family sums the included homogeneous coefficients. -/
theorem operatorCoefficientsEquiv_apply (k : ℕ)
    (f : ⨁ n : d.cutoff k, H →ₗ[R] ℳ (p + n.val)) (x : H) :
    operatorCoefficientsEquiv d ℳ p k f x =
      ∑ n : d.cutoff k, d.shiftedQuotientInclusion ℳ p k n (f n x) := by
  simp only [operatorCoefficientsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.congrRight_apply_apply, shiftedQuotientEquivDirectSum_symm_apply,
    DirectSum.linearMapEquivOfFintype_apply]

/-- Decomposing a linear family reads its ambient components pointwise. -/
@[simp]
theorem operatorCoefficientsEquiv_symm_apply (k : ℕ)
    (f : H →ₗ[R] (d.shiftedFiltration ℳ p).quotient k) (n : d.cutoff k) (x : H) :
    (operatorCoefficientsEquiv d ℳ p k).symm f n x =
      d.shiftedQuotientComponent ℳ p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n) (f x) := by
  simp only [operatorCoefficientsEquiv, LinearEquiv.symm_trans_apply,
    DirectSum.linearMapEquivOfFintype_symm_apply,
    LinearEquiv.congrRight_symm_apply_apply, LinearEquiv.symm_symm,
    PositiveDegrees.shiftedQuotientEquivDirectSum_apply]

/-- Evaluation of an assembled family recovers each prescribed homogeneous map. -/
@[simp]
theorem shiftedQuotientComponent_operatorCoefficientsEquiv (k : ℕ)
    (f : ⨁ n : d.cutoff k, H →ₗ[R] ℳ (p + n.val)) (n : d.cutoff k) (x : H) :
    d.shiftedQuotientComponent ℳ p (p + n.val) k
      (d.degree_add_val_sub_self_le p k n)
        (operatorCoefficientsEquiv d ℳ p k f x) = f n x := by
  rw [← operatorCoefficientsEquiv_symm_apply, LinearEquiv.symm_apply_apply]

/-- A homogeneous operator is the corresponding quotient inclusion after evaluation. -/
@[simp]
theorem operatorCoefficientsEquiv_lof (k : ℕ) (n : d.cutoff k)
    (f : H →ₗ[R] ℳ (p + n.val)) (x : H) :
    operatorCoefficientsEquiv d ℳ p k
      (DirectSum.lof R (d.cutoff k) (fun n => H →ₗ[R] ℳ (p + n.val)) n f) x =
        d.shiftedQuotientInclusion ℳ p k n (f x) := by
  simp only [operatorCoefficientsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.congrRight_apply_apply, DirectSum.linearMapEquivOfFintype_lof,
    shiftedQuotientEquivDirectSum_symm_lof]

/-- Lower the cutoff of homogeneous operator coefficients using the existing quotient
transition. All input parameters are retained. -/
def operatorTransition {k l : ℕ} (hkl : k ≤ l) :
    (⨁ n : d.cutoff l, H →ₗ[R] ℳ (p + n.val)) →ₗ[R]
      (⨁ n : d.cutoff k, H →ₗ[R] ℳ (p + n.val)) :=
  (operatorCoefficientsEquiv d ℳ p k).symm.toLinearMap.comp
    ((LinearMap.llcomp R H _ _ ((d.shiftedFiltration ℳ p).transition hkl)).comp
      (operatorCoefficientsEquiv d ℳ p l).toLinearMap)

/-- Evaluation and quotient transition commute with operator truncation. -/
@[simp]
theorem operatorCoefficientsEquiv_operatorTransition {k l : ℕ} (hkl : k ≤ l)
    (f : ⨁ n : d.cutoff l, H →ₗ[R] ℳ (p + n.val)) (x : H) :
    operatorCoefficientsEquiv d ℳ p k (operatorTransition d ℳ p hkl f) x =
      (d.shiftedFiltration ℳ p).transition hkl (operatorCoefficientsEquiv d ℳ p l f x) := by
  simp [operatorTransition]

/-- Operator truncation leaves every retained homogeneous map unchanged. -/
@[simp]
theorem operatorTransition_apply {k l : ℕ} (hkl : k ≤ l)
    (f : ⨁ n : d.cutoff l, H →ₗ[R] ℳ (p + n.val)) (n : d.cutoff k) (x : H) :
    operatorTransition d ℳ p hkl f n x =
      f ⟨n.val, d.cutoff_mono hkl n.property⟩ x := by
  rw [← shiftedQuotientComponent_operatorCoefficientsEquiv,
    operatorCoefficientsEquiv_operatorTransition,
    PositiveDegrees.shiftedQuotientComponent_transition]
  exact shiftedQuotientComponent_operatorCoefficientsEquiv d ℳ p l f
    ⟨n.val, d.cutoff_mono hkl n.property⟩ x

/-- Truncation at the same order is the identity on operator coefficients. -/
@[simp]
theorem operatorTransition_refl (k : ℕ) :
    operatorTransition (H := H) d ℳ p (le_refl k) = LinearMap.id := by
  ext f n x
  simp

/-- Successive operator truncations agree with direct truncation. -/
@[simp]
theorem operatorTransition_comp {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (operatorTransition (H := H) d ℳ p hkl).comp (operatorTransition d ℳ p hlm) =
      operatorTransition d ℳ p (hkl.trans hlm) := by
  ext f n x
  simp

end Mei.PositiveDegrees
