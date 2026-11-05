/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Positive.Support

/-!
# Positive completion embeddings commute with global transport

Scalar and positive degree maps commute with the inclusion of the positive
completion in global coefficients. Consequently they preserve the positive
global coefficient subalgebra. Neither injectivity nor a spanning or alternating
hypothesis is needed; relative cutoff control is supplied by the positive degree map.
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
private local instance : DirectSum.Decomposition (grade q β) := inferInstance
private local instance : Ring (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : Algebra S (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : AddCommGroup (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : Module S (QuantumMonoidAlgebra q' β') := inferInstance
private local instance : DirectSum.Decomposition (grade q' β') := inferInstance
private local instance (p : Γ) : AddCommGroup (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ) : Module R (d.ShiftedCoefficients (grade q β) p) := inferInstance
private local instance (p : Γ') : AddCommGroup (e.ShiftedCoefficients (grade q' β') p) :=
  inferInstance
private local instance (p : Γ') : Module S (e.ShiftedCoefficients (grade q' β') p) := inferInstance
private local instance : AddCommMonoid (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : Module R (d.ShiftedDirectLimit (grade q β)) := inferInstance
private local instance : AddCommMonoid (e.ShiftedDirectLimit (grade q' β')) := inferInstance
private local instance : Module S (e.ShiftedDirectLimit (grade q' β')) := inferInstance

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => positiveFiltration q' β' e.monoid e.degree (fun _ h => e.degree_nonneg h)

private local instance : Ring (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Algebra R (positiveSubalgebra q β d.monoid) := inferInstance
private local instance : Ring (positiveSubalgebra q' β' e.monoid) := inferInstance
private local instance : Algebra S (positiveSubalgebra q' β' e.monoid) := inferInstance
private local instance : Ring (F).completion := inferInstance
private local instance : Algebra R (F).completion := inferInstance
private local instance : Module R (F).completion := inferInstance
private local instance : Ring (G).completion := inferInstance
private local instance : Algebra S (G).completion := inferInstance
private local instance : Module S (G).completion := inferInstance

/-- The global embedding of positive completions is natural for scalar and degree transport. -/
theorem mapShiftedDirectLimit_positiveCompletionToDirectLimit (a : (F).completion) :
    mapShiftedDirectLimit d e T φ h (positiveCompletionToDirectLimit q β d a) =
      positiveCompletionToDirectLimit q' β' e (mapPositiveCompletion d e T φ h a) := by
  have hd0 : (0 : Γ) - d.coefficientOrigin 0 ∈ d.monoid := d.zero_coefficientOrigin_mem
  have he0 : T 0 - e.coefficientOrigin 0 ∈ e.monoid := by
    simpa only [T.map_zero] using e.zero_coefficientOrigin_mem
  have he00 : (0 : Γ') - e.coefficientOrigin 0 ∈ e.monoid := e.zero_coefficientOrigin_mem
  let b := mapPositiveCompletion d e T φ h a
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (positiveCompletionToDirectLimit_apply q β d a)
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h 0 0 hd0 0 he0
    (positiveCompletionShiftEquiv q β d 0 a)
  have h₃ := congrArg (e.toShiftedDirectLimitOfChart (grade q' β') (T 0) 0 he0)
    (mapShiftedCompletion_coordinates d e T φ h 0 a)
  have hcast := toShiftedDirectLimitOfChart_positiveCompletionShiftEquiv_congr q' β' e
    T.map_zero 0 he0 he00 b
  exact (h₁).trans <|
    (h₂).trans <|
    (h₃).trans <|
    (hcast).trans <|
    (positiveCompletionToDirectLimit_apply q' β' e b).symm

/-- Compatible scalar and degree maps preserve positive global support. -/
theorem mapShiftedDirectLimit_mem_positiveCoefficientSubalgebra
    {x : d.ShiftedDirectLimit (grade q β)}
    (hx : x ∈ d.positiveCoefficientSubalgebra (grade q β)) :
    mapShiftedDirectLimit d e T φ h x ∈ e.positiveCoefficientSubalgebra (grade q' β') := by
  let a := (positiveCompletionEquivPositiveCoefficients q β d).symm ⟨x, hx⟩
  have ha := positiveCompletionToDirectLimit_equiv_symm q β d ⟨x, hx⟩
  have hm := mapShiftedDirectLimit_positiveCompletionToDirectLimit d e T φ h a
  have he := (congrArg (mapShiftedDirectLimit d e T φ h) ha).symm.trans hm
  rw [← range_positiveCompletionToDirectLimit q' β' e]
  exact ⟨mapPositiveCompletion d e T φ h a, he.symm⟩

end Mei.QuantumMonoidAlgebra
