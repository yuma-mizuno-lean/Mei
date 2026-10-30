/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Basic
public import Mei.Algebra.PositiveDegrees.Completion

/-!
# Homogeneous components of completed shifted modules

A homogeneous component of a completed shifted coefficient can be read from any
finite quotient retaining its relative degree. The quotient components descend
the existing degree-completion API for the relative grading. Transport to the
ambient homogeneous piece preserves its quotient and cutoff laws; the existing
product comparison supplies component extensionality. Each finite projection is
represented by the sum of its retained ambient components.

The shifted coefficient completion is the one used in Travis Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §2.1
(arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

private def shiftedPieceToAmbient (q : Γ) :
    shiftedGrading ℳ d.monoid p (q - p) →ₗ[R] ℳ q := by
  have hpq : p + (q - p) = q := by abel
  exact ((shiftedSubmodule ℳ d.monoid p).subtype.submoduleComap (ℳ q)).comp
    (Submodule.inclusion (by rw [shiftedGrading_def, hpq]))

omit [DecidableEq Γ] [DirectSum.Decomposition ℳ] in
/-- The ambient transport preserves the underlying coefficient. -/
private theorem coe_shiftedPieceToAmbient (q : Γ)
    (x : shiftedGrading ℳ d.monoid p (q - p)) :
    (d.shiftedPieceToAmbient ℳ p q x : M) = (x : shiftedSubmodule ℳ d.monoid p) := by
  -- Both constituent maps are submodule inclusions; the index transport changes only membership.
  rfl

/-- The ambient degree-`q` component of a finite shifted quotient retaining that degree. -/
def shiftedQuotientComponent (q : Γ) (k : ℕ) (h : d.degree (q - p) ≤ k) :
    (d.shiftedFiltration ℳ p).quotient k →ₗ[R] ℳ q :=
  (d.shiftedPieceToAmbient ℳ p q).comp
    (d.quotientComponent (shiftedGrading ℳ d.monoid p) (d.shiftedFiltration ℳ p)
      (d.shiftedFiltration_succ ℳ p) k (q - p) h)

/-- On a representative, the quotient component is the original homogeneous projection. -/
@[simp]
theorem shiftedQuotientComponent_mk (q : Γ) (k : ℕ) (h : d.degree (q - p) ≤ k)
    (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedQuotientComponent ℳ p q k h (Submodule.Quotient.mk x) =
      DirectSum.decompose ℳ (x : M) q := by
  rw [shiftedQuotientComponent, LinearMap.comp_apply, quotientComponent_mk]
  apply Subtype.ext
  rw [coe_shiftedPieceToAmbient, coe_decompose_shiftedGrading]
  congr 2 <;> abel_nf

/-- An included homogeneous coefficient has zero quotient component in every other degree. -/
@[simp↓]
theorem shiftedQuotientComponent_mk_shiftedInclusion_of_ne (q : Γ) (k : ℕ)
    (h : d.degree (q - p) ≤ k) (n : d.monoid) (hnq : p + n ≠ q)
    (x : ℳ (p + n)) :
    d.shiftedQuotientComponent ℳ p q k h
      (Submodule.Quotient.mk (shiftedInclusion ℳ d.monoid p n x)) = 0 := by
  rw [shiftedQuotientComponent_mk]
  apply Subtype.ext
  simp only [coe_shiftedInclusion, ZeroMemClass.coe_zero]
  exact DirectSum.decompose_of_mem_ne ℳ x.property hnq

/-- Lowering the cutoff leaves every retained homogeneous component unchanged. -/
@[simp]
theorem shiftedQuotientComponent_transition (q : Γ) {k l : ℕ} (hkl : k ≤ l)
    (hk : d.degree (q - p) ≤ k) (x : (d.shiftedFiltration ℳ p).quotient l) :
    d.shiftedQuotientComponent ℳ p q k hk ((d.shiftedFiltration ℳ p).transition hkl x) =
      d.shiftedQuotientComponent ℳ p q l (hk.trans (Int.ofNat_le.mpr hkl)) x := by
  simp only [shiftedQuotientComponent, LinearMap.comp_apply, quotientComponent_transition]

/-- The ambient degree-`q` homogeneous component of a completed shifted coefficient. -/
def shiftedHomogeneousComponent (q : Γ) : d.ShiftedCoefficients ℳ p →ₗ[R] ℳ q :=
  (d.shiftedPieceToAmbient ℳ p q).comp
    (d.completionComponent (shiftedGrading ℳ d.monoid p) (d.shiftedFiltration ℳ p)
      (d.shiftedFiltration_succ ℳ p) (q - p))

/-- A completed component can be read at any cutoff that retains its relative degree. -/
theorem shiftedHomogeneousComponent_eq (q : Γ) (k : ℕ) (hk : d.degree (q - p) ≤ k)
    (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedHomogeneousComponent ℳ p q x =
      d.shiftedQuotientComponent ℳ p q k hk ((d.shiftedFiltration ℳ p).projection k x) := by
  simp only [shiftedHomogeneousComponent, shiftedQuotientComponent, LinearMap.comp_apply,
    d.completionComponent_eq_quotientComponent _ _ _ (q - p) k hk]

/-- The completed component of an original coefficient is its direct-sum component. -/
@[simp]
theorem shiftedHomogeneousComponent_of (q : Γ) (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedHomogeneousComponent ℳ p q ((d.shiftedFiltration ℳ p).of x) =
      DirectSum.decompose ℳ (x : M) q := by
  rw [shiftedHomogeneousComponent, LinearMap.comp_apply, completionComponent_of]
  apply Subtype.ext
  rw [coe_shiftedPieceToAmbient, coe_decompose_shiftedGrading]
  congr 2 <;> abel_nf

/-- Relative completed components and ambient shifted components have the same value. -/
@[simp]
theorem coe_completionComponent_shiftedGrading (n : Γ) (x : d.ShiftedCoefficients ℳ p) :
    ((d.completionComponent (shiftedGrading ℳ d.monoid p) (d.shiftedFiltration ℳ p)
      (d.shiftedFiltration_succ ℳ p) n x : shiftedSubmodule ℳ d.monoid p) : M) =
      d.shiftedHomogeneousComponent ℳ p (p + n) x := by
  rw [shiftedHomogeneousComponent, LinearMap.comp_apply, coe_shiftedPieceToAmbient,
    add_sub_cancel_left]

/-- Every finite projection is represented by the finite sum of its retained
ambient homogeneous components. -/
theorem projection_eq_sum_shiftedHomogeneousComponent (k : ℕ)
    (x : d.ShiftedCoefficients ℳ p) :
    (d.shiftedFiltration ℳ p).projection k x =
      Submodule.Quotient.mk
        (∑ n ∈ (d.finite_cutoff k).toFinset.attach,
          shiftedInclusion ℳ d.monoid p ⟨n.val, (d.mem_cutoff.mp
            ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
            (d.shiftedHomogeneousComponent ℳ p (p + n.val) x)) := by
  classical
  let e := d.completionEquivPi (shiftedGrading ℳ d.monoid p)
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration_succ ℳ p)
    (fun n hn => shiftedGrading_eq_bot ℳ d.monoid p hn)
  have h := d.projection_completionEquivPi_symm (shiftedGrading ℳ d.monoid p)
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration_succ ℳ p)
    (fun n hn => shiftedGrading_eq_bot ℳ d.monoid p hn) (e x) k
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum, coe_shiftedInclusion]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [e, completionEquivPi_apply] using
    d.coe_completionComponent_shiftedGrading ℳ p n.val x

/-- A finite shifted coefficient is the sum of its retained homogeneous components.
The sum runs over actual degrees of the positive monoid. -/
theorem quotient_eq_sum_shiftedQuotientComponent (k : ℕ)
    (x : (d.shiftedFiltration ℳ p).quotient k) :
    x = Submodule.Quotient.mk
      (∑ n ∈ (d.finite_cutoff k).toFinset.attach,
        shiftedInclusion ℳ d.monoid p ⟨n.val, (d.mem_cutoff.mp
          ((d.finite_cutoff k).mem_toFinset.mp n.property)).1⟩
          (d.shiftedQuotientComponent ℳ p (p + n.val) k
            (by simpa only [add_sub_cancel_left] using
              (d.mem_cutoff.mp ((d.finite_cutoff k).mem_toFinset.mp n.property)).2) x)) := by
  classical
  obtain ⟨m, rfl⟩ := (d.shiftedFiltration ℳ p).submodule (k + 1) |>.mkQ_surjective x
  have he := d.projection_eq_sum_shiftedHomogeneousComponent ℳ p k
    ((d.shiftedFiltration ℳ p).of m)
  simpa only [ModuleFiltration.projection_of, Submodule.mkQ_apply, shiftedQuotientComponent_mk,
    shiftedHomogeneousComponent_of] using he

/-- Completed coefficients have no components outside the shifted support. -/
@[simp]
theorem shiftedHomogeneousComponent_eq_zero {q : Γ} (hq : q - p ∉ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) : d.shiftedHomogeneousComponent ℳ p q x = 0 := by
  have hz := (d.completionComponent (shiftedGrading ℳ d.monoid p)
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration_succ ℳ p) (q - p) x).property
  have hz' : (d.completionComponent (shiftedGrading ℳ d.monoid p)
      (d.shiftedFiltration ℳ p) (d.shiftedFiltration_succ ℳ p) (q - p) x :
      shiftedSubmodule ℳ d.monoid p) = 0 := by
    simpa only [shiftedGrading_eq_bot ℳ d.monoid p hq, Submodule.mem_bot] using hz
  apply Subtype.ext
  rw [shiftedHomogeneousComponent, LinearMap.comp_apply, coe_shiftedPieceToAmbient]
  exact congrArg (fun a : shiftedSubmodule ℳ d.monoid p => (a : M)) hz'

/-- All homogeneous components together distinguish completed shifted coefficients. -/
theorem shiftedCoefficients_ext {x y : d.ShiftedCoefficients ℳ p}
    (h : ∀ q, d.shiftedHomogeneousComponent ℳ p q x =
      d.shiftedHomogeneousComponent ℳ p q y) : x = y := by
  apply (d.completionEquivPi (shiftedGrading ℳ d.monoid p) (d.shiftedFiltration ℳ p)
    (d.shiftedFiltration_succ ℳ p) (fun n hn => shiftedGrading_eq_bot ℳ d.monoid p hn)).injective
  funext n
  simp only [completionEquivPi_apply]
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg Subtype.val (h (p + n))
  simp only [shiftedHomogeneousComponent, LinearMap.comp_apply,
    coe_shiftedPieceToAmbient] at he
  have hn : p + n - p = n := by abel
  rw [hn] at he
  exact he

end Mei.PositiveDegrees
