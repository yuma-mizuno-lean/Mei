/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Map.Injective

/-!
# Faithful transport of global quantum coefficients

An injective coefficient map and an exponent map injective on the source positive
monoid induce an injective map on the global shifted coefficient algebra.
Two global elements can be represented in a common shifted chart. Faithful
shifted transport and injectivity of the target chart then reflect equality.
No spanning condition on the positive monoid is needed.
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

/-- Faithful scalar and positive exponent transport reflects equality of all global
coefficients, including infinite series and negative shifts. -/
theorem mapShiftedDirectLimit_injective (hφ : Function.Injective φ)
    (hT : Set.InjOn T d.monoid) :
    Function.Injective (mapShiftedDirectLimit d e T φ h) := by
  intro x y hxy
  obtain ⟨s, a, b, ha, hb⟩ := Module.DirectLimit.exists_of₂ x y
  have ha' : d.toShiftedDirectLimit (grade q β) s a = x :=
    (d.toShiftedDirectLimit_apply (grade q β) s a).trans ha
  have hb' : d.toShiftedDirectLimit (grade q β) s b = y :=
    (d.toShiftedDirectLimit_apply (grade q β) s b).trans hb
  let t : Multiset e.monoid := {⟨T (s.sum : Γ), T.map_mem s.sum.property⟩}
  have ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid := by
    simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, t, Multiset.sum_singleton,
      map_neg, sub_self, zero_mem]
  have he : mapShiftedDirectLimit d e T φ h
      (d.toShiftedDirectLimit (grade q β) s a) =
      mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimit (grade q β) s b) := by
    rw [ha', hb']
    exact hxy
  rw [mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s t ht a,
    mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s t ht b] at he
  have hab := mapShiftedCompletion_injective d e T φ h hφ hT (d.coefficientOrigin s)
    (e.toShiftedDirectLimitOfChart_injective (grade q' β') (T (d.coefficientOrigin s)) t ht he)
  exact ha'.symm.trans ((congrArg (d.toShiftedDirectLimit (grade q β) s) hab).trans hb')

end Mei.QuantumMonoidAlgebra
