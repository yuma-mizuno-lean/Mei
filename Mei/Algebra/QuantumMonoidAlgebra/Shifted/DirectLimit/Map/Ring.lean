/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map.Product
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Transport

/-!
# Ring maps between global quantum coefficient algebras

The global scalar and degree coefficient map is a unital ring homomorphism
compatible with the algebra maps of scalars. The bilinear forms need not be
alternating, and no injectivity or spanning assumption is required.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ'] [DecidableEq Γ] [DecidableEq Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

/-- Global quantum coefficient transport preserves products for arbitrary bilinear forms. -/
theorem mapShiftedDirectLimit_mul (x y : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit d e T φ h (x * y) =
      mapShiftedDirectLimit d e T φ h x * mapShiftedDirectLimit d e T φ h y :=
  d.shiftedDirectLimitMap_mul_of_charts e T.toAddMonoidHom (fun hn => T.map_mem hn)
    (grade q β) (grade q' β') (fun p => mapShiftedCompletion d e T φ h p)
    (mapShiftedDirectLimit d e T φ h)
    (mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h)
    (mapShiftedCompletion_mul d e T φ h) x y

/-- Global scalar and exponent transport preserves the coefficient-algebra unit. -/
theorem mapShiftedDirectLimit_one :
    mapShiftedDirectLimit d e T φ h (1 : d.ShiftedDirectLimit (grade q β)) = 1 := by
  have hzero : (0 : Γ) - d.coefficientOrigin 0 ∈ d.monoid := d.zero_coefficientOrigin_mem
  have hzero' : T 0 - e.coefficientOrigin 0 ∈ e.monoid := by
    simpa only [T.map_zero] using e.zero_coefficientOrigin_mem
  let a := positiveShiftEquiv q β d 0 (1 : positiveSubalgebra q β d.monoid)
  let b := positiveShiftEquiv q' β' e (T 0)
    (positiveMap φ T.toAddMonoidHom h d.monoid e.monoid (fun _ hn => T.map_mem hn) 1)
  have ha : (a : QuantumMonoidAlgebra q β) = 1 := by
    simp only [a, coe_positiveShiftEquiv, monomial_zero, Subalgebra.coe_one, one_mul]
  have hb : (b : QuantumMonoidAlgebra q' β') = 1 := by
    simp only [b, coe_positiveShiftEquiv, PositiveDegreeMap.map_zero, monomial_zero,
      map_one, Subalgebra.coe_one, one_mul]
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (d.toShiftedDirectLimitOfChart_of_eq_one (grade q β) 0 0 hzero a ha)
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h 0 0 hzero 0 hzero'
    ((d.shiftedFiltration (grade q β) 0).of a)
  have h₃ := congrArg (e.toShiftedDirectLimitOfChart (grade q' β') (T 0) 0 hzero')
    (mapShiftedCompletion_of_coordinates d e T φ h 0 1)
  have h₄ := e.toShiftedDirectLimitOfChart_of_eq_one (grade q' β') (T 0) 0 hzero' b hb
  exact (h₁.symm).trans <|
    (h₂).trans <|
    (h₃).trans <|
    h₄

/-- The global quantum coefficient map, with its unital ring-homomorphism structure. -/
def mapShiftedDirectLimitRingHom :
    d.ShiftedDirectLimit (grade q β) →+* e.ShiftedDirectLimit (grade q' β') where
  __ := (mapShiftedDirectLimit d e T φ h).toAddMonoidHom
  map_one' := mapShiftedDirectLimit_one d e T φ h
  map_mul' := mapShiftedDirectLimit_mul d e T φ h

/-- The ring map has the same values as the original semilinear global map. -/
@[simp]
theorem mapShiftedDirectLimitRingHom_apply (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimitRingHom d e T φ h x = mapShiftedDirectLimit d e T φ h x := by
  -- This application only projects the defining map record and its unchanged underlying function.
  rfl

/-- Global coefficient transport acts on central scalars by the prescribed ring homomorphism. -/
theorem mapShiftedDirectLimitRingHom_algebraMap (r : R) :
    mapShiftedDirectLimitRingHom d e T φ h
        (algebraMap R (d.ShiftedDirectLimit (grade q β)) r) =
      algebraMap S (e.ShiftedDirectLimit (grade q' β')) (φ r) := by
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (Algebra.algebraMap_eq_smul_one (A := d.ShiftedDirectLimit (grade q β)) r)
  have h₂ := (mapShiftedDirectLimit d e T φ h).map_smulₛₗ r 1
  have h₃ := congrArg (fun x : e.ShiftedDirectLimit (grade q' β') => φ r • x)
    (mapShiftedDirectLimit_one d e T φ h)
  exact h₁.trans (h₂.trans (h₃.trans (Algebra.algebraMap_eq_smul_one (φ r)).symm))

end Mei.QuantumMonoidAlgebra
