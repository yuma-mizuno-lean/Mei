/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Inclusion

/-!
# Quantum ray actions on the direct limit of translated coefficient modules

Compatibility with support inclusions descends the existing shifted ray actions to
Mathlib's module direct limit. Every finite multiset chart is equivariant, as is
every arbitrary-origin chart contained in one of them. The construction is linear
and uses the skew part of any integral bilinear form. No assertion of a global
coefficient algebra or its multiplication is made here.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (n : d.monoid) (hn : 0 < d.degree n)

private def rayDirectLimitEquiv (H : (PowerSeries R)ˣ) :
    d.ShiftedDirectLimit (grade q β) ≃ₗ[R] d.ShiftedDirectLimit (grade q β) :=
  Module.DirectLimit.congr
    (fun s => shiftedRayAction q β d n hn (d.coefficientOrigin s) H)
    (by
      intro s t h
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, PositiveDegrees.coefficientInclusion_eq]
      exact (shiftedCompletedInclusion_shiftedRayAction q β d n hn
        (d.coefficientOrigin s) (d.coefficientOrigin t)
        (d.coefficientOrigin_sub_mem h) H x).symm)

private theorem rayDirectLimitEquiv_apply (H : (PowerSeries R)ˣ)
    (s : Multiset d.monoid) (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    rayDirectLimitEquiv q β d n hn H (d.toShiftedDirectLimit (grade q β) s x) =
      d.toShiftedDirectLimit (grade q β) s
        (shiftedRayAction q β d n hn (d.coefficientOrigin s) H x) := by
  simp only [rayDirectLimitEquiv, PositiveDegrees.toShiftedDirectLimit_apply]
  apply Module.DirectLimit.congr_apply_of

private theorem rayDirectLimitEquiv_mul (H K : (PowerSeries R)ˣ) :
    rayDirectLimitEquiv q β d n hn (H * K) =
      rayDirectLimitEquiv q β d n hn H * rayDirectLimitEquiv q β d n hn K := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨s, a, ha⟩ := d.exists_toShiftedDirectLimit (grade q β) x
  rw [← ha]
  simp only [LinearEquiv.mul_apply, rayDirectLimitEquiv_apply,
    (shiftedRayAction q β d n hn (d.coefficientOrigin s)).map_mul]

/-- Unit power series act on the direct limit by the compatible shifted ray actions. -/
def directLimitRayAction : (PowerSeries R)ˣ →*
    (d.ShiftedDirectLimit (grade q β) ≃ₗ[R] d.ShiftedDirectLimit (grade q β)) :=
  MonoidHom.mk' (rayDirectLimitEquiv q β d n hn) (rayDirectLimitEquiv_mul q β d n hn)

/-- The direct-limit action restricts to the original action in every multiset chart. -/
@[simp]
theorem directLimitRayAction_toShiftedDirectLimit (H : (PowerSeries R)ˣ)
    (s : Multiset d.monoid) (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s)) :
    directLimitRayAction q β d n hn H (d.toShiftedDirectLimit (grade q β) s x) =
      d.toShiftedDirectLimit (grade q β) s
        (shiftedRayAction q β d n hn (d.coefficientOrigin s) H x) :=
  rayDirectLimitEquiv_apply q β d n hn H s x

/-- Any containing chart gives an equivariant embedding of the arbitrary-origin action. -/
theorem directLimitRayAction_toShiftedDirectLimitOfChart (H : (PowerSeries R)ˣ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients (grade q β) p) :
    directLimitRayAction q β d n hn H (d.toShiftedDirectLimitOfChart (grade q β) p s hp x) =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (shiftedRayAction q β d n hn p H x) := by
  simp only [PositiveDegrees.toShiftedDirectLimitOfChart_apply,
    directLimitRayAction_toShiftedDirectLimit]
  exact congrArg (d.toShiftedDirectLimit (grade q β) s)
    (shiftedCompletedInclusion_shiftedRayAction q β d n hn p (d.coefficientOrigin s) hp H x).symm

/-- Reversed crossings induce the inverse direct-limit action. -/
@[simp]
theorem directLimitRayAction_inv (H : (PowerSeries R)ˣ) :
    directLimitRayAction q β d n hn (H⁻¹) = (directLimitRayAction q β d n hn H).symm :=
  map_inv (directLimitRayAction q β d n hn) H

end Mei.QuantumMonoidAlgebra
