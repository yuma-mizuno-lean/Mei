/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.SkewProduct
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Global quantum ray algebra actions for arbitrary bilinear forms

Unit ray series act on global coefficients by algebra automorphisms for every
integral bilinear form. The action agrees with the global linear ray action,
respects multiplication of series, and commutes with arbitrary-origin chart
embeddings. No alternating or positive-difference spanning hypothesis is needed.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (n : d.monoid) (hn : 0 < d.degree n)

private theorem chart_mul_eq (s t : Multiset d.monoid)
    (x : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s))
    (y : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin t)) :
    d.toShiftedDirectLimit (grade q β) s x * d.toShiftedDirectLimit (grade q β) t y =
      d.toShiftedDirectLimitOfChart (grade q β)
        (d.coefficientOrigin s + d.coefficientOrigin t) (s + t)
        (d.add_sub_coefficientOrigin_mem (by simp) (by simp))
        (d.shiftedCompletionMul (grade q β) (d.coefficientOrigin s) (d.coefficientOrigin t)
          x y) :=
  (d.shiftedDirectLimitMul_eq_mul (grade q β) _ _).symm.trans
    ((d.shiftedDirectLimitMul_toShiftedDirectLimit (grade q β) s t x y).trans
      (d.shiftedDirectLimitChartMul_apply (grade q β) s t x y))

private theorem rayDirectLimitAction_map_mul_charts (H : (PowerSeries R)ˣ)
    (s t : Multiset d.monoid)
    (a : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin s))
    (b : d.ShiftedCoefficients (grade q β) (d.coefficientOrigin t)) :
    directLimitRayAction q β d n hn H
        (d.toShiftedDirectLimit (grade q β) s a * d.toShiftedDirectLimit (grade q β) t b) =
      directLimitRayAction q β d n hn H (d.toShiftedDirectLimit (grade q β) s a) *
        directLimitRayAction q β d n hn H (d.toShiftedDirectLimit (grade q β) t b) := by
  let p := d.coefficientOrigin s
  let r := d.coefficientOrigin t
  have hp : p + r - d.coefficientOrigin (s + t) ∈ d.monoid :=
    d.add_sub_coefficientOrigin_mem (by simp only [p, sub_self, zero_mem])
      (by simp only [r, sub_self, zero_mem])
  let E := d.toShiftedDirectLimitOfChart (grade q β) (p + r) (s + t) hp
  have hprod := chart_mul_eq q β d s t a b
  have hact := directLimitRayAction_toShiftedDirectLimitOfChart q β d n hn H
    (p + r) (s + t) hp (d.shiftedCompletionMul (grade q β) p r a b)
  have hlocal := shiftedRayAction_shiftedCompletionMul_skew q β d n hn p r H a b
  have hprod' := chart_mul_eq q β d s t
    (shiftedRayAction q β d n hn p H a) (shiftedRayAction q β d n hn r H b)
  have hfactors := congrArg₂ (fun u v : d.ShiftedDirectLimit (grade q β) => u * v)
    (directLimitRayAction_toShiftedDirectLimit q β d n hn H s a)
    (directLimitRayAction_toShiftedDirectLimit q β d n hn H t b)
  exact (congrArg (directLimitRayAction q β d n hn H) hprod).trans
    (hact.trans ((congrArg E hlocal).trans (hprod'.symm.trans hfactors.symm)))

/-- The global linear ray action preserves products for every integral bilinear form. -/
theorem directLimitRayAction_map_mul_skew (H : (PowerSeries R)ˣ)
    (x y : d.ShiftedDirectLimit (grade q β)) :
    directLimitRayAction q β d n hn H (x * y) =
      directLimitRayAction q β d n hn H x * directLimitRayAction q β d n hn H y := by
  let act : d.ShiftedDirectLimit (grade q β) →ₗ[R] d.ShiftedDirectLimit (grade q β) :=
    (directLimitRayAction q β d n hn H).toLinearMap
  have he : (d.shiftedDirectLimitMul (grade q β)).compr₂ act =
      ((d.shiftedDirectLimitMul (grade q β)).compl₂ act).comp act := by
    apply Module.DirectLimit.hom_ext
    intro s
    apply LinearMap.ext
    intro a
    apply Module.DirectLimit.hom_ext
    intro t
    apply LinearMap.ext
    intro b
    have hc := rayDirectLimitAction_map_mul_charts q β d n hn H s t a b
    simpa only [LinearMap.comp_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      act, LinearEquiv.coe_coe, PositiveDegrees.toShiftedDirectLimit_apply,
      ← d.shiftedDirectLimitMul_eq_mul (grade q β)] using hc
  have hh := congrArg (fun f : d.ShiftedDirectLimit (grade q β) →ₗ[R]
    d.ShiftedDirectLimit (grade q β) →ₗ[R] d.ShiftedDirectLimit (grade q β) => f x y) he
  simpa only [LinearMap.comp_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    act, LinearEquiv.coe_coe, ← d.shiftedDirectLimitMul_eq_mul (grade q β)] using hh

private def rayDirectLimitAlgEquiv (H : (PowerSeries R)ˣ) :
    d.ShiftedDirectLimit (grade q β) ≃ₐ[R] d.ShiftedDirectLimit (grade q β) :=
  let e := directLimitRayAction q β d n hn H
  let m : d.ShiftedDirectLimit (grade q β) ≃* d.ShiftedDirectLimit (grade q β) :=
    { e.toEquiv with map_mul' := directLimitRayAction_map_mul_skew q β d n hn H }
  AlgEquiv.ofLinearEquiv e m.map_one (directLimitRayAction_map_mul_skew q β d n hn H)

private theorem rayDirectLimitAlgEquiv_mul (H K : (PowerSeries R)ˣ) :
    rayDirectLimitAlgEquiv q β d n hn (H * K) =
      rayDirectLimitAlgEquiv q β d n hn H * rayDirectLimitAlgEquiv q β d n hn K := by
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun e : d.ShiftedDirectLimit (grade q β) ≃ₗ[R]
    d.ShiftedDirectLimit (grade q β) => e x) ((directLimitRayAction q β d n hn).map_mul H K)

/-- Unit ray series act on global coefficients by algebra automorphisms. -/
def directLimitRaySkewAlgAction : (PowerSeries R)ˣ →*
    (d.ShiftedDirectLimit (grade q β) ≃ₐ[R] d.ShiftedDirectLimit (grade q β)) :=
  MonoidHom.mk' (rayDirectLimitAlgEquiv q β d n hn)
    (rayDirectLimitAlgEquiv_mul q β d n hn)

/-- The algebra action is the existing linear direct-limit action on coefficients. -/
@[simp]
theorem directLimitRaySkewAlgAction_apply (H : (PowerSeries R)ˣ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    directLimitRaySkewAlgAction q β d n hn H x = directLimitRayAction q β d n hn H x := by
  -- AlgEquiv.ofLinearEquiv and MonoidHom.mk' keep the underlying linear action.
  rfl

/-- Every arbitrary-origin coefficient embedding intertwines the algebra action. -/
theorem directLimitRaySkewAlgAction_toShiftedDirectLimitOfChart (H : (PowerSeries R)ˣ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (x : d.ShiftedCoefficients (grade q β) p) :
    directLimitRaySkewAlgAction q β d n hn H
        (d.toShiftedDirectLimitOfChart (grade q β) p s hp x) =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (shiftedRayAction q β d n hn p H x) := by
  exact (directLimitRaySkewAlgAction_apply q β d n hn H _).trans
    (directLimitRayAction_toShiftedDirectLimitOfChart q β d n hn H p s hp x)

/-- Reversing the ray crossing gives the inverse algebra automorphism. -/
@[simp]
theorem directLimitRaySkewAlgAction_inv (H : (PowerSeries R)ˣ) :
    directLimitRaySkewAlgAction q β d n hn (H⁻¹) =
      (directLimitRaySkewAlgAction q β d n hn H).symm :=
  map_inv (directLimitRaySkewAlgAction q β d n hn) H

end Mei.QuantumMonoidAlgebra
