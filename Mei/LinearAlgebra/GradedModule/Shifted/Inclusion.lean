/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component
public import Mei.Algebra.PositiveDegrees.Naturality

/-!
# Inclusions between shifted coefficient supports

When `p - q` belongs to the positive monoid, support in `p + P` implies support
in `q + P`. The inclusion keeps the ambient coefficients unchanged. Relative
orders can only increase, so the identity cutoff gives a map of completions.
All ambient homogeneous components are preserved, making the completed map
injective even though its finite quotient maps need not be injective.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  (p q : Γ) (hpq : p - q ∈ d.monoid)

/-- The finite quotient map induced by containment of shifted supports. -/
def shiftedQuotientMap (k : ℕ) :
    (d.shiftedFiltration ℳ p).quotient k →ₗ[R] (d.shiftedFiltration ℳ q).quotient k :=
  ((d.shiftedFiltration ℳ p).submodule (k + 1)).mapQ
    ((d.shiftedFiltration ℳ q).submodule (k + 1))
    (shiftedSupportInclusion ℳ d.monoid p q hpq)
    (d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))

/-- The finite quotient map keeps the representative's ambient coefficients. -/
@[simp]
theorem shiftedQuotientMap_mk (k : ℕ) (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedQuotientMap ℳ p q hpq k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (shiftedSupportInclusion ℳ d.monoid p q hpq x) :=
  Submodule.mapQ_apply _ _ _ x

/-- The identity cutoff extends origin inclusion to shifted completions. -/
def shiftedCompletedInclusion : d.ShiftedCoefficients ℳ p →ₗ[R] d.ShiftedCoefficients ℳ q :=
  (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration ℳ q)
    (shiftedSupportInclusion ℳ d.monoid p q hpq) id monotone_id
    (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))

/-- The support inclusion is the completion map with identity cutoff modulus. -/
theorem shiftedCompletedInclusion_def :
    d.shiftedCompletedInclusion ℳ p q hpq =
      (d.shiftedFiltration ℳ p).completionMap (d.shiftedFiltration ℳ q)
        (shiftedSupportInclusion ℳ d.monoid p q hpq) id monotone_id
        (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1)) := (rfl)

/-- The completed inclusion has the corresponding finite quotient maps as projections. -/
@[simp]
theorem projection_shiftedCompletedInclusion (k : ℕ) (x : d.ShiftedCoefficients ℳ p) :
    (d.shiftedFiltration ℳ q).projection k (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedQuotientMap ℳ p q hpq k ((d.shiftedFiltration ℳ p).projection k x) :=
  ModuleFiltration.projection_completionMap _ _ _ _ _ _ k x

/-- The completed inclusion extends inclusion of ordinary shifted coefficients. -/
@[simp]
theorem shiftedCompletedInclusion_of (x : shiftedSubmodule ℳ d.monoid p) :
    d.shiftedCompletedInclusion ℳ p q hpq ((d.shiftedFiltration ℳ p).of x) =
      (d.shiftedFiltration ℳ q).of (shiftedSupportInclusion ℳ d.monoid p q hpq x) :=
  ModuleFiltration.completionMap_of _ _ _ _ _ _ x

/-- The identity-cutoff inclusion preserves every completed filtration order. -/
theorem shiftedCompletedInclusion_mem_completedFiltration (k : ℕ)
    {x : d.ShiftedCoefficients ℳ p}
    (hx : x ∈ (d.shiftedFiltration ℳ p).completedFiltration.submodule k) :
    d.shiftedCompletedInclusion ℳ p q hpq x ∈
      (d.shiftedFiltration ℳ q).completedFiltration.submodule k := by
  cases k with
  | zero => simp
  | succ k =>
    exact ModuleFiltration.completionMap_mem_completedFiltration _ _ _ _ _ _ k hx

omit hpq q in
/-- Inclusion from a shifted support into itself is the identity. -/
@[simp]
theorem shiftedCompletedInclusion_refl (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedCompletedInclusion ℳ p p (by simp) x = x := by
  have hi : shiftedSupportInclusion ℳ d.monoid p p (by simp) = LinearMap.id := by
    ext a
    simp only [coe_shiftedSupportInclusion, LinearMap.id_apply]
  simp only [shiftedCompletedInclusion, hi, ModuleFiltration.completionMap_id,
    LinearMap.id_apply]

/-- Nested support inclusions compose. -/
theorem shiftedCompletedInclusion_trans (r : Γ) (hqr : q - r ∈ d.monoid)
    (hpr : p - r ∈ d.monoid) (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedCompletedInclusion ℳ q r hqr (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedCompletedInclusion ℳ p r hpr x := by
  have hi : (shiftedSupportInclusion ℳ d.monoid q r hqr).comp
      (shiftedSupportInclusion ℳ d.monoid p q hpq) =
        shiftedSupportInclusion ℳ d.monoid p r hpr := by
    ext a
    simp only [LinearMap.comp_apply, coe_shiftedSupportInclusion]
  have h := ModuleFiltration.completionMap_comp
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration ℳ q)
    (shiftedSupportInclusion ℳ d.monoid p q hpq) id monotone_id
    (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))
    (d.shiftedFiltration ℳ r) (shiftedSupportInclusion ℳ d.monoid q r hqr)
    id monotone_id (fun k => d.shiftedSupportInclusion_filtered ℳ q r hqr (k + 1))
  simpa only [hi, Function.id_comp, LinearMap.comp_apply, shiftedCompletedInclusion] using
    (congrArg (fun f => f x) h).symm

variable [DecidableEq Γ] [DirectSum.Decomposition ℳ]

/-- Origin inclusion preserves every ambient homogeneous component. -/
@[simp]
theorem shiftedHomogeneousComponent_inclusion (u : Γ) (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedHomogeneousComponent ℳ q u (d.shiftedCompletedInclusion ℳ p q hpq x) =
      d.shiftedHomogeneousComponent ℳ p u x := by
  have hhom (n : Γ) (a : shiftedSubmodule ℳ d.monoid p)
      (ha : a ∈ shiftedGrading ℳ d.monoid p n) :
      shiftedSupportInclusion ℳ d.monoid p q hpq a ∈
        shiftedGrading ℳ d.monoid q (p + n - q) := by
    apply (mem_shiftedGrading ℳ d.monoid q).mpr
    rw [coe_shiftedSupportInclusion]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (mem_shiftedGrading ℳ d.monoid p).mp ha
  have h := d.completionComponent_completionMap_of_injective d
    (shiftedGrading ℳ d.monoid p) (shiftedGrading ℳ d.monoid q)
    (d.shiftedFiltration ℳ p) (d.shiftedFiltration ℳ q)
    (d.shiftedFiltration_succ ℳ p) (d.shiftedFiltration_succ ℳ q)
    (shiftedSupportInclusion ℳ d.monoid p q hpq) (fun n => p + n - q) hhom
    id monotone_id (fun k => d.shiftedSupportInclusion_filtered ℳ p q hpq (k + 1))
    (by intro a b h; simpa using congrArg (fun n : Γ => n + q) h) (u - p) x
  apply Subtype.ext
  have h' := congrArg (fun a : shiftedSubmodule ℳ d.monoid q => (a : M)) h
  rw [coe_shiftedSupportInclusion, coe_completionComponent_shiftedGrading,
    coe_completionComponent_shiftedGrading] at h'
  -- The ambient component maps have degree-dependent codomains, so `simp` does
  -- not normalize their indices under the coercions. Rewrite the source index
  -- first; this also turns the target index into `q + (u - q)`.
  have hp : p + (u - p) = u := by abel
  have hq : q + (u - q) = u := by abel
  rw [hp, hq] at h'
  exact h'

/-- The completed support inclusion is injective, as it preserves all components. -/
theorem shiftedCompletedInclusion_injective :
    Function.Injective (d.shiftedCompletedInclusion ℳ p q hpq) := by
  intro x y h
  apply d.shiftedCoefficients_ext ℳ p
  intro u
  simpa only [d.shiftedHomogeneousComponent_inclusion ℳ p q hpq] using
    congrArg (d.shiftedHomogeneousComponent ℳ q u) h


end Mei.PositiveDegrees
