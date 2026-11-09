/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit

/-!
# Compatible actions on global shifted coefficients

An action by linear equivalences on each translated completion descends to the
module direct limit when it commutes with translated support inclusions. Both
completed Lie actions and quantum ray actions use this common construction.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M G : Type*} [AddCommGroup Γ] [Ring R]
  [AddCommGroup M] [Module R M] [DecidableEq Γ] [Monoid G]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  (act : ∀ p, G →* (d.ShiftedCoefficients ℳ p ≃ₗ[R] d.ShiftedCoefficients ℳ p))
  (hact : ∀ (p q : Γ) (hpq : p - q ∈ d.monoid) (g : G)
    (x : d.ShiftedCoefficients ℳ p),
    d.shiftedCompletedInclusion ℳ p q hpq (act p g x) =
      act q g (d.shiftedCompletedInclusion ℳ p q hpq x))

private def compatibleDirectLimitEquiv (g : G) :
    d.ShiftedDirectLimit ℳ ≃ₗ[R] d.ShiftedDirectLimit ℳ :=
  Module.DirectLimit.congr (fun s => act (d.coefficientOrigin s) g) (by
    intro s t h
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coefficientInclusion_eq]
    exact (hact _ _ (d.coefficientOrigin_sub_mem h) g x).symm)

private theorem compatibleDirectLimitEquiv_apply (g : G) (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    d.compatibleDirectLimitEquiv ℳ act hact g (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit ℳ s (act (d.coefficientOrigin s) g x) := by
  simp only [compatibleDirectLimitEquiv, toShiftedDirectLimit_apply]
  apply Module.DirectLimit.congr_apply_of

/-- Descend a compatible family of linear actions to global coefficients. -/
def shiftedDirectLimitAction : G →*
    (d.ShiftedDirectLimit ℳ ≃ₗ[R] d.ShiftedDirectLimit ℳ) :=
  MonoidHom.mk' (d.compatibleDirectLimitEquiv ℳ act hact) (by
    intro g h
    apply LinearEquiv.ext
    intro x
    obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ x
    simp only [mul_apply_eq_comp, compatibleDirectLimitEquiv_apply, map_mul])

/-- The descended action agrees with its defining action in every canonical chart. -/
@[simp]
theorem shiftedDirectLimitAction_toShiftedDirectLimit (g : G) (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) :
    d.shiftedDirectLimitAction ℳ act hact g (d.toShiftedDirectLimit ℳ s x) =
      d.toShiftedDirectLimit ℳ s (act (d.coefficientOrigin s) g x) :=
  d.compatibleDirectLimitEquiv_apply ℳ act hact g s x

/-- Any containing chart intertwines the descended action at an arbitrary origin. -/
@[simp]
theorem shiftedDirectLimitAction_toShiftedDirectLimitOfChart (g : G) (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedDirectLimitAction ℳ act hact g (d.toShiftedDirectLimitOfChart ℳ p s hp x) =
      d.toShiftedDirectLimitOfChart ℳ p s hp (act p g x) := by
  simp only [toShiftedDirectLimitOfChart_apply, shiftedDirectLimitAction_toShiftedDirectLimit]
  exact congrArg (d.toShiftedDirectLimit ℳ s) (hact _ _ hp g x).symm

end Mei.PositiveDegrees
