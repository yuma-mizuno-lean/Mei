/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.Inclusion
public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Inclusion

/-!
# Multiplication of global shifted coefficients

Completed products in individual translated supports give a bilinear multiplication
on the module direct limit. The product is independent of the containing charts
and agrees with multiplication in every pair of translated supports.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

/-- Multiply two completed charts and include the product in the sum chart. -/
def shiftedDirectLimitChartMul (s t : Multiset d.monoid) :
    d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s) →ₗ[R]
      d.ShiftedCoefficients 𝒜 (d.coefficientOrigin t) →ₗ[R] d.ShiftedDirectLimit 𝒜 :=
  (d.shiftedCompletionMul 𝒜 (d.coefficientOrigin s) (d.coefficientOrigin t)).compr₂
    (d.toShiftedDirectLimitOfChart 𝒜 (d.coefficientOrigin s + d.coefficientOrigin t)
      (s + t) (d.add_sub_coefficientOrigin_mem (by simp) (by simp)))

omit [DirectSum.Decomposition 𝒜] in
/-- The chart product uses the original completed shifted multiplication. -/
theorem shiftedDirectLimitChartMul_apply (s t : Multiset d.monoid)
    (x : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s))
    (y : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin t)) :
    d.shiftedDirectLimitChartMul 𝒜 s t x y =
      d.toShiftedDirectLimitOfChart 𝒜 (d.coefficientOrigin s + d.coefficientOrigin t)
        (s + t) (d.add_sub_coefficientOrigin_mem (by simp) (by simp))
        (d.shiftedCompletionMul 𝒜 (d.coefficientOrigin s) (d.coefficientOrigin t) x y) :=
  (rfl)

private theorem shiftedDirectLimitChartMul_inclusion (s s' t t' : Multiset d.monoid)
    (hs : s ≤ s') (ht : t ≤ t')
    (x : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s))
    (y : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin t)) :
    d.shiftedDirectLimitChartMul 𝒜 s' t'
        (d.coefficientInclusion 𝒜 s s' hs x) (d.coefficientInclusion 𝒜 t t' ht y) =
      d.shiftedDirectLimitChartMul 𝒜 s t x y := by
  have hsum := d.sub_add_mem (d.coefficientOrigin_sub_mem hs)
    (d.coefficientOrigin_sub_mem ht)
  simp only [shiftedDirectLimitChartMul, LinearMap.compr₂_apply, coefficientInclusion_eq]
  rw [← d.shiftedCompletedInclusion_shiftedCompletionMul 𝒜
    (d.coefficientOrigin s) (d.coefficientOrigin t)
    (d.coefficientOrigin s') (d.coefficientOrigin t')
    (d.coefficientOrigin_sub_mem hs) (d.coefficientOrigin_sub_mem ht) hsum x y]
  exact d.toShiftedDirectLimitOfChart_inclusion 𝒜 _ _ hsum (s + t) (s' + t') _ _ _

private def shiftedDirectLimitMulRight (s : Multiset d.monoid) :
    d.ShiftedDirectLimit 𝒜 →ₗ[R]
      d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s) →ₗ[R] d.ShiftedDirectLimit 𝒜 :=
  Module.DirectLimit.lift R (Multiset d.monoid)
    (fun t => d.ShiftedCoefficients 𝒜 (d.coefficientOrigin t))
    (fun t t' h => d.coefficientInclusion 𝒜 t t' h)
    (fun t => (d.shiftedDirectLimitChartMul 𝒜 s t).flip)
    (by
      intro t t' h y
      apply LinearMap.ext
      intro x
      have hh := d.shiftedDirectLimitChartMul_inclusion 𝒜 s s t t' le_rfl h x y
      simpa only [LinearMap.flip_apply, coefficientInclusion_eq,
        shiftedCompletedInclusion_refl] using hh)

/-- Bilinear multiplication on the direct limit of completed translated supports. -/
def shiftedDirectLimitMul : d.ShiftedDirectLimit 𝒜 →ₗ[R]
    d.ShiftedDirectLimit 𝒜 →ₗ[R] d.ShiftedDirectLimit 𝒜 :=
  Module.DirectLimit.lift R (Multiset d.monoid)
    (fun s => d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s))
    (fun s s' h => d.coefficientInclusion 𝒜 s s' h)
    (fun s => (d.shiftedDirectLimitMulRight 𝒜 s).flip)
    (by
      intro s s' h x
      apply LinearMap.ext
      intro y
      obtain ⟨t, z, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 y
      simp only [LinearMap.flip_apply, shiftedDirectLimitMulRight,
        toShiftedDirectLimit_apply, Module.DirectLimit.lift_of]
      have hh := d.shiftedDirectLimitChartMul_inclusion 𝒜 s s' t t h le_rfl x z
      simpa only [coefficientInclusion_eq, shiftedCompletedInclusion_refl] using hh)

/-- The descended bilinear map is the completed product on each pair of charts. -/
theorem shiftedDirectLimitMul_toShiftedDirectLimit (s t : Multiset d.monoid)
    (x : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s))
    (y : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin t)) :
    d.shiftedDirectLimitMul 𝒜 (d.toShiftedDirectLimit 𝒜 s x)
        (d.toShiftedDirectLimit 𝒜 t y) = d.shiftedDirectLimitChartMul 𝒜 s t x y := by
  simp only [shiftedDirectLimitMul, shiftedDirectLimitMulRight,
    toShiftedDirectLimit_apply, Module.DirectLimit.lift_of, LinearMap.flip_apply]

/-- Products of arbitrary translated supports give the same global multiplication. -/
theorem shiftedDirectLimitMul_toShiftedDirectLimitOfChart (p q : Γ)
    (s t : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hq : q - d.coefficientOrigin t ∈ d.monoid)
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) :
    d.shiftedDirectLimitMul 𝒜 (d.toShiftedDirectLimitOfChart 𝒜 p s hp x)
        (d.toShiftedDirectLimitOfChart 𝒜 q t hq y) =
      d.toShiftedDirectLimitOfChart 𝒜 (p + q) (s + t)
        (d.add_sub_coefficientOrigin_mem hp hq)
        (d.shiftedCompletionMul 𝒜 p q x y) := by
  have hsum := d.sub_add_mem hp hq
  rw [d.toShiftedDirectLimitOfChart_apply 𝒜 p s hp,
    d.toShiftedDirectLimitOfChart_apply 𝒜 q t hq,
    shiftedDirectLimitMul_toShiftedDirectLimit, shiftedDirectLimitChartMul_apply,
    ← d.shiftedCompletedInclusion_shiftedCompletionMul 𝒜 p q
      (d.coefficientOrigin s) (d.coefficientOrigin t) hp hq hsum x y]
  exact d.toShiftedDirectLimitOfChart_inclusion 𝒜 _ _ hsum (s + t) (s + t) _ _ _

end Mei.PositiveDegrees
