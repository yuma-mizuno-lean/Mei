/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit
public import Mei.LinearAlgebra.GradedModule.Shifted.Reconstruction

/-!
# Ambient components of direct-limit shifted coefficients

The direct limit of shifted completions embeds linearly into the product of
ambient homogeneous pieces. Its image is exactly the families supported in one
of the multiset-indexed translates. Under the explicit condition that every
lattice degree is a difference of positive degrees, these are exactly the families
supported in some translate of the positive monoid.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- Read all ambient components of a direct-limit coefficient. -/
def shiftedDirectLimitComponents : d.ShiftedDirectLimit ℳ →ₗ[R] ∀ u, ℳ u :=
  Module.DirectLimit.lift R (Multiset d.monoid)
    (fun s => d.ShiftedCoefficients ℳ (d.coefficientOrigin s))
    (fun s t h => d.coefficientInclusion ℳ s t h)
    (fun s => LinearMap.pi (fun u => d.shiftedHomogeneousComponent ℳ (d.coefficientOrigin s) u))
    (by
      intro s t h x
      funext u
      simp only [LinearMap.pi_apply, coefficientInclusion_eq,
        shiftedHomogeneousComponent_inclusion])

/-- A chart inclusion keeps every ambient homogeneous coefficient. -/
@[simp]
theorem shiftedDirectLimitComponents_toShiftedDirectLimit (s : Multiset d.monoid)
    (x : d.ShiftedCoefficients ℳ (d.coefficientOrigin s)) (u : Γ) :
    d.shiftedDirectLimitComponents ℳ (d.toShiftedDirectLimit ℳ s x) u =
      d.shiftedHomogeneousComponent ℳ (d.coefficientOrigin s) u x := by
  simp only [shiftedDirectLimitComponents, toShiftedDirectLimit_apply,
    Module.DirectLimit.lift_of, LinearMap.pi_apply]

/-- An arbitrary-origin embedding also preserves all ambient components. -/
@[simp]
theorem shiftedDirectLimitComponents_toShiftedDirectLimitOfChart (p : Γ)
    (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients ℳ p) (u : Γ) :
    d.shiftedDirectLimitComponents ℳ (d.toShiftedDirectLimitOfChart ℳ p s hp x) u =
      d.shiftedHomogeneousComponent ℳ p u x := by
  rw [toShiftedDirectLimitOfChart_apply, shiftedDirectLimitComponents_toShiftedDirectLimit,
    shiftedHomogeneousComponent_inclusion]

/-- Ambient coefficients distinguish direct-limit elements. -/
theorem shiftedDirectLimitComponents_injective :
    Function.Injective (d.shiftedDirectLimitComponents ℳ) := by
  apply Module.DirectLimit.lift_injective
  intro s x y h
  apply d.shiftedCoefficients_ext ℳ (d.coefficientOrigin s)
  intro u
  exact congrFun h u

/-- The image consists precisely of families supported in a multiset-indexed translate. -/
theorem mem_range_shiftedDirectLimitComponents_iff (x : ∀ u, ℳ u) :
    x ∈ LinearMap.range (d.shiftedDirectLimitComponents ℳ) ↔
      ∃ s : Multiset d.monoid, ∀ u, u - d.coefficientOrigin s ∉ d.monoid → x u = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit ℳ a
    refine ⟨s, ?_⟩
    intro u hu
    rw [shiftedDirectLimitComponents_toShiftedDirectLimit]
    exact d.shiftedHomogeneousComponent_eq_zero ℳ (d.coefficientOrigin s) hu a
  · rintro ⟨s, hs⟩
    refine ⟨d.toShiftedDirectLimit ℳ s
      (d.shiftedCoefficientsOfComponents ℳ (d.coefficientOrigin s) x hs), ?_⟩
    funext u
    rw [shiftedDirectLimitComponents_toShiftedDirectLimit, shiftedHomogeneousComponent_ofComponents]

/-- When positive differences span the lattice, the image is all families supported
in any translate of the positive monoid, with no finite-support requirement. -/
theorem mem_range_shiftedDirectLimitComponents_iff_of_spanning
    (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b) (x : ∀ u, ℳ u) :
    x ∈ LinearMap.range (d.shiftedDirectLimitComponents ℳ) ↔
      ∃ p : Γ, ∀ u, u - p ∉ d.monoid → x u = 0 := by
  rw [mem_range_shiftedDirectLimitComponents_iff]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨d.coefficientOrigin s, hs⟩
  · rintro ⟨p, hp⟩
    obtain ⟨s, hs⟩ := d.exists_coefficientOrigin_of_spanning hspan p
    refine ⟨s, ?_⟩
    intro u hu
    apply hp u
    intro hup
    apply hu
    have h := d.monoid.add_mem hup hs
    simpa only [sub_add_sub_cancel] using h

end Mei.PositiveDegrees
