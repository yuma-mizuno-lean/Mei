/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.SkewProduct
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Action

public import Mei.Algebra.Group.Hom.Algebra

/-!
# Global quantum ray algebra actions for arbitrary bilinear forms

Unit ray series act on global coefficients by algebra automorphisms for every
integral bilinear form. The action agrees with the global linear ray action,
respects multiplication of series, and commutes with arbitrary-origin chart
embeddings. No alternating or positive-difference spanning hypothesis is needed.
-/

public section

open TauCeti (PositiveDegrees)
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)
  (n : d.monoid) (hn : 0 < d.degree n)

/-- The global linear ray action preserves products for every integral bilinear form. -/
theorem directLimitRayAction_map_mul_skew (H : (PowerSeries R)ˣ)
    (x y : d.ShiftedDirectLimit (grade q β)) :
    directLimitRayAction q β d n hn H (x * y) =
      directLimitRayAction q β d n hn H x * directLimitRayAction q β d n hn H y := by
  rw [directLimitRayAction_eq_shiftedDirectLimitAction]
  exact d.shiftedDirectLimitAction_map_mul (grade q β) (shiftedRayAction q β d n hn)
    (shiftedCompletedInclusion_shiftedRayAction q β d n hn)
    (shiftedRayAction_shiftedCompletionMul_skew q β d n hn) H x y

/-- Unit ray series act on global coefficients by algebra automorphisms. -/
def directLimitRaySkewAlgAction : (PowerSeries R)ˣ →*
    (d.ShiftedDirectLimit (grade q β) ≃ₐ[R] d.ShiftedDirectLimit (grade q β)) :=
  (directLimitRayAction q β d n hn).toAlgAut (directLimitRayAction_map_mul_skew q β d n hn)

/-- The algebra action is the existing linear direct-limit action on coefficients. -/
@[simp]
theorem directLimitRaySkewAlgAction_apply (H : (PowerSeries R)ˣ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    directLimitRaySkewAlgAction q β d n hn H x = directLimitRayAction q β d n hn H x := by
  simp only [directLimitRaySkewAlgAction, MonoidHom.toAlgAut_apply]

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
