/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map.Basic
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit
public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Map

/-!
# Naturality of global quantum ray actions

Compatible scalar and positive degree maps intertwine the global ray actions.
Exponent maps may merge distinct positive rays, the coefficient homomorphism need
not be injective, and neither bilinear form needs to be alternating.
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

/-- Global scalar and exponent transport intertwines quantum ray actions. -/
theorem mapShiftedDirectLimit_directLimitRayAction
    (n : d.monoid) (hn : 0 < d.degree n) (H : (PowerSeries R)ˣ)
    (x : d.ShiftedDirectLimit (grade q β)) :
    mapShiftedDirectLimit d e T φ h (directLimitRayAction q β d n hn H x) =
      directLimitRayAction q' β' e ⟨T n, T.map_mem n.property⟩
        (mappedRay_degree_pos d e T n hn) (Units.map (PowerSeries.map φ).toMonoidHom H)
        (mapShiftedDirectLimit d e T φ h x) := by
  refine (d.exists_toShiftedDirectLimit (grade q β) x).elim fun s hs => ?_
  refine hs.elim fun z hz => ?_
  let t : Multiset e.monoid := {⟨T (s.sum : Γ), T.map_mem s.sum.property⟩}
  have ht : T (d.coefficientOrigin s) - e.coefficientOrigin t ∈ e.monoid := by
    simp only [PositiveDegrees.coefficientOrigin_eq_neg_sum, t, Multiset.sum_singleton,
      map_neg, sub_self, zero_mem]
  let E := e.toShiftedDirectLimitOfChart (grade q' β') (T (d.coefficientOrigin s)) t ht
  let K := Units.map (PowerSeries.map φ).toMonoidHom H
  let N : e.monoid := ⟨T n, T.map_mem n.property⟩
  let hn' := mappedRay_degree_pos d e T n hn
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (directLimitRayAction_toShiftedDirectLimit q β d n hn H s z)
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s t ht
    (shiftedRayAction q β d n hn (d.coefficientOrigin s) H z)
  have h₃ := congrArg E
    (mapShiftedCompletion_shiftedRayAction d e T φ h n hn (d.coefficientOrigin s) H z)
  have h₄ := directLimitRayAction_toShiftedDirectLimitOfChart q' β' e N hn' K
    (T (d.coefficientOrigin s)) t ht
    (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)
  have h₅ := congrArg (directLimitRayAction q' β' e N hn' K)
    (mapShiftedDirectLimit_toShiftedDirectLimit d e T φ h s t ht z)
  -- Compute both global actions in a common chart using local naturality.
  calc
    _ = _ := (congrArg (fun y => mapShiftedDirectLimit d e T φ h
      (directLimitRayAction q β d n hn H y)) hz).symm
    _ = _ := h₁
    _ = E (mapShiftedCompletion d e T φ h (d.coefficientOrigin s)
        (shiftedRayAction q β d n hn (d.coefficientOrigin s) H z)) := h₂
    _ = E (shiftedRayAction q' β' e N hn' (T (d.coefficientOrigin s)) K
        (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)) := h₃
    _ = directLimitRayAction q' β' e N hn' K
        (E (mapShiftedCompletion d e T φ h (d.coefficientOrigin s) z)) := h₄.symm
    _ = _ := h₅.symm
    _ = _ := congrArg (fun y => directLimitRayAction q' β' e N hn' K
      (mapShiftedDirectLimit d e T φ h y)) hz

end Mei.QuantumMonoidAlgebra
