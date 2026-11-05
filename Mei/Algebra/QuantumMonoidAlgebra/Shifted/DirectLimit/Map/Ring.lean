/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map.Product
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit

/-!
# Ring maps between global quantum coefficient algebras

The global scalar and degree coefficient map is a unital ring homomorphism
compatible with the algebra maps of scalars. The bilinear forms need not be
alternating, and no injectivity or spanning assumption is required.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ'] [DecidableEq Γ] [DecidableEq Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

private local instance : Ring (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Algebra R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q β) := inferInstance
private local instance : Module R (QuantumMonoidAlgebra q β) := inferInstance
private local instance : GradedAlgebra (grade q β) := inferInstance
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : Algebra S (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : Module S (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : GradedAlgebra (grade q' β') := inferInstance
private local instance : DirectSum.Decomposition (grade q' β') := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ') : AddCommGroup (e.ShiftedCoefficients (grade q' β') p) :=
  inferInstance
private local instance (p : Γ') : Module S (e.ShiftedCoefficients (grade q' β') p) :=
  inferInstance
private local instance : AddCommGroup (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Ring (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Algebra R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : AddCommGroup (e.ShiftedDirectLimit (grade q' β')) := inferInstance
private local instance : Ring (e.ShiftedDirectLimit (grade q' β')) := inferInstance
private local instance : Algebra S (e.ShiftedDirectLimit (grade q' β')) := inferInstance
private local instance : Module S (e.ShiftedDirectLimit (grade q' β')) := inferInstance

private theorem map_global_mul_charts (p r : Γ) (s t : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hr : r - d.coefficientOrigin t ∈ d.monoid) (u v : Multiset e.monoid)
    (hu : T p - e.coefficientOrigin u ∈ e.monoid)
    (hv : T r - e.coefficientOrigin v ∈ e.monoid)
    (x : d.ShiftedCoefficients (grade q β) p)
    (y : d.ShiftedCoefficients (grade q β) r) :
    mapShiftedDirectLimit d e T φ h
        (d.toShiftedDirectLimitOfChart (grade q β) p s hp x *
          d.toShiftedDirectLimitOfChart (grade q β) r t hr y) =
      mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimitOfChart (grade q β) p s hp x) *
        mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimitOfChart (grade q β) r t hr y) := by
  have hst : p + r - d.coefficientOrigin (s + t) ∈ d.monoid := by
    simpa only [PositiveDegrees.coefficientOrigin_add, add_sub_add_comm] using
      d.monoid.add_mem hp hr
  have huv : T p + T r - e.coefficientOrigin (u + v) ∈ e.monoid := by
    simpa only [PositiveDegrees.coefficientOrigin_add, add_sub_add_comm] using
      e.monoid.add_mem hu hv
  have huv' : T (p + r) - e.coefficientOrigin (u + v) ∈ e.monoid := by
    simpa only [map_add] using huv
  let z := d.shiftedCompletionMul (grade q β) p r x y
  let E := e.toShiftedDirectLimitOfChart (grade q' β') (T p + T r) (u + v) huv
  have hs := (d.shiftedDirectLimitMul_eq_mul (grade q β) _ _).symm.trans
    (d.shiftedDirectLimitMul_toShiftedDirectLimitOfChart (grade q β) p r s t hp hr x y)
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h) hs
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h
    (p + r) (s + t) hst (u + v) huv' z
  have h₃ := e.toShiftedDirectLimitOfChart_cast (grade q' β') (T (p + r)) (T p + T r)
    (map_add T.toAddMonoidHom p r) (u + v) (u + v) huv' huv
    (mapShiftedCompletion d e T φ h (p + r) z)
  have h₄ := congrArg E (mapShiftedCompletion_mul d e T φ h p r x y)
  have ht := (e.shiftedDirectLimitMul_eq_mul (grade q' β') _ _).symm.trans
    (e.shiftedDirectLimitMul_toShiftedDirectLimitOfChart (grade q' β')
      (T p) (T r) u v hu hv
      (mapShiftedCompletion d e T φ h p x) (mapShiftedCompletion d e T φ h r y))
  have hf := congrArg₂ (fun a b : e.ShiftedDirectLimit (grade q' β') => a * b)
    (mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h p s hp u hu x)
    (mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h r t hr v hv y)
  exact (h₁).trans <|
    (h₂).trans <|
    (h₃.symm).trans <|
    (h₄).trans <|
    (ht.symm).trans <|
    hf.symm

/-- Global quantum coefficient transport preserves products for arbitrary bilinear forms. -/
theorem mapShiftedDirectLimit_mul (x y : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit d e T φ h (x * y) =
      mapShiftedDirectLimit d e T φ h x * mapShiftedDirectLimit d e T φ h y := by
  refine (d.exists_toShiftedDirectLimit (grade q β) x).elim fun s hs => ?_
  refine hs.elim fun a ha => ?_
  refine (d.exists_toShiftedDirectLimit (grade q β) y).elim fun t ht => ?_
  refine ht.elim fun b hb => ?_
  let u : Multiset e.monoid := {⟨T (s.sum : Γ), T.map_mem s.sum.property⟩}
  let v : Multiset e.monoid := {⟨T (t.sum : Γ), T.map_mem t.sum.property⟩}
  have hu : T (d.coefficientOrigin s) - e.coefficientOrigin u ∈ e.monoid := by
    simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, u, Multiset.sum_singleton,
      map_neg, sub_self, zero_mem]
  have hv : T (d.coefficientOrigin t) - e.coefficientOrigin v ∈ e.monoid := by
    simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, v, Multiset.sum_singleton,
      map_neg, sub_self, zero_mem]
  have hs : d.toShiftedDirectLimitOfChart (grade q β) (d.coefficientOrigin s) s (by simp) a = x :=
    (d.toShiftedDirectLimitOfChart_apply (grade q β) (d.coefficientOrigin s) s (by simp) a).trans
      ((congrArg (d.toShiftedDirectLimit (grade q β) s)
        (d.shiftedCompletedInclusion_refl (grade q β) (d.coefficientOrigin s) a)).trans ha)
  have ht : d.toShiftedDirectLimitOfChart (grade q β) (d.coefficientOrigin t) t (by simp) b = y :=
    (d.toShiftedDirectLimitOfChart_apply (grade q β) (d.coefficientOrigin t) t (by simp) b).trans
      ((congrArg (d.toShiftedDirectLimit (grade q β) t)
        (d.shiftedCompletedInclusion_refl (grade q β) (d.coefficientOrigin t) b)).trans hb)
  have hmul := map_global_mul_charts d e T φ h (d.coefficientOrigin s) (d.coefficientOrigin t)
    s t (by simp) (by simp) u v hu hv a b
  have hl := congrArg₂ (fun a b => mapShiftedDirectLimit d e T φ h (a * b)) hs ht
  have hr := congrArg₂ (fun a b => mapShiftedDirectLimit d e T φ h a *
    mapShiftedDirectLimit d e T φ h b) hs ht
  exact hl.symm.trans (hmul.trans hr)

omit [DecidableEq Γ'] in
private theorem global_of_eq_one (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (a : shiftedSubmodule (grade q β) d.monoid p) (ha : (a : QuantumMonoidAlgebra q β) = 1) :
    d.toShiftedDirectLimitOfChart (grade q β) p s hp ((d.shiftedFiltration (grade q β) p).of a) =
      1 := by
  apply d.shiftedDirectLimitComponents_injective (grade q β)
  funext u
  rw [PositiveDegrees.shiftedDirectLimitComponents_toShiftedDirectLimitOfChart,
    PositiveDegrees.shiftedHomogeneousComponent_of,
    PositiveDegrees.shiftedDirectLimitComponents_one]
  exact congrArg (fun z => DirectSum.decompose (grade q β) z u) ha

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
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h) (global_of_eq_one d 0 0 hzero a ha)
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h 0 0 hzero 0 hzero'
    ((d.shiftedFiltration (grade q β) 0).of a)
  have h₃ := congrArg (e.toShiftedDirectLimitOfChart (grade q' β') (T 0) 0 hzero')
    (mapShiftedCompletion_of_coordinates d e T φ h 0 1)
  have h₄ := global_of_eq_one e (T 0) 0 hzero' b hb
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
