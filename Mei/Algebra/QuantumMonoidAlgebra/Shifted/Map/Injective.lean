/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Completion.Injective
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map

/-!
# Faithful transport of shifted quantum completions

Positive monomial coordinates identify shifted transport with positive completion
transport. Consequently faithful scalar and positive exponent maps remain
injective at every ambient shift, including negative shifts.
-/

public section

open TauCeti (PositiveDegrees PositiveDegreeMap)
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R S Γ Γ' : Type*} [CommRing R] [CommRing S]
  [AddCommGroup Γ] [AddCommGroup Γ']
  {q : Rˣ} {q' : Sˣ} {β : LinearMap.BilinForm ℤ Γ} {β' : LinearMap.BilinForm ℤ Γ'}
  (d : PositiveDegrees Γ) (e : PositiveDegrees Γ') (T : PositiveDegreeMap d e)
  (φ : R →+* S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' (T p) (T r))

/-- Faithful scalar and positive exponent transport is injective on every shifted completion. -/
theorem mapShiftedCompletion_injective (hφ : Function.Injective φ)
    (hT : Set.InjOn T d.monoid) (p : Γ) :
    Function.Injective (mapShiftedCompletion d e T φ h p) := by
  intro x y hxy
  apply (positiveCompletionShiftEquiv q β d p).symm.injective
  apply mapPositiveCompletion_injective d e T φ h hφ hT
  apply (positiveCompletionShiftEquiv q' β' e (T p)).injective
  simpa only [mapShiftedCompletion_apply] using hxy

end Mei.QuantumMonoidAlgebra
