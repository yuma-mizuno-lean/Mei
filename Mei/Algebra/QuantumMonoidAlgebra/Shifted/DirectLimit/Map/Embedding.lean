/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Map.Basic
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Embedding

/-!
# Naturality of the finite quantum coefficient embedding

The global map induced by compatible scalar and positive degree maps agrees on
finite quantum coefficients with the original quantum algebra map. Both exponent
and coefficient maps may identify distinct inputs. Spanning assumptions are used
only to define the finite algebra embeddings, not for global coefficient transport.
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
  (hd : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)
  (he : ∀ p : Γ', ∃ a b : e.monoid, p = (a : Γ') - b)

private theorem mapShiftedDirectLimit_finiteCoordinates (p : Γ)
    (b : positiveSubalgebra q β d.monoid) :
    mapShiftedDirectLimit d e T φ h
        (d.toShiftedDirectLimitAlgHom (grade q β) hd (positiveShiftEquiv q β d p b)) =
      e.toShiftedDirectLimitAlgHom (grade q' β') he
        (map φ T.toAddMonoidHom h (positiveShiftEquiv q β d p b)) := by
  let s := Classical.choose (d.exists_coefficientOrigin_of_spanning hd p)
  have hs := Classical.choose_spec (d.exists_coefficientOrigin_of_spanning hd p)
  let t := Classical.choose (e.exists_coefficientOrigin_of_spanning he (T p))
  have ht := Classical.choose_spec (e.exists_coefficientOrigin_of_spanning he (T p))
  let b' := positiveMap φ T.toAddMonoidHom h d.monoid e.monoid
    (fun _ hn => T.map_mem hn) b
  have h₁ := congrArg (mapShiftedDirectLimit d e T φ h)
    (d.toShiftedDirectLimitAlgHom_of_supported (grade q β) hd p s hs
      (positiveShiftEquiv q β d p b))
  have h₂ := mapShiftedDirectLimit_toShiftedDirectLimitOfChart d e T φ h p s hs t ht
    ((d.shiftedFiltration (grade q β) p).of (positiveShiftEquiv q β d p b))
  have h₃ := congrArg (e.toShiftedDirectLimitOfChart (grade q' β') (T p) t ht)
    (mapShiftedCompletion_of_coordinates d e T φ h p b)
  have h₄ := e.toShiftedDirectLimitAlgHom_of_supported (grade q' β') he (T p) t ht
    (positiveShiftEquiv q' β' e (T p) b')
  have h₅ := congrArg (e.toShiftedDirectLimitAlgHom (grade q' β') he)
    (map_positiveShiftEquiv d e T φ h p b)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.symm.trans h₅.symm)))

/-- Finite coefficient embeddings commute with global scalar and exponent transport. -/
theorem mapShiftedDirectLimit_toShiftedDirectLimitAlgHom (x : QuantumMonoidAlgebra q β) :
    mapShiftedDirectLimit d e T φ h (d.toShiftedDirectLimitAlgHom (grade q β) hd x) =
      e.toShiftedDirectLimitAlgHom (grade q' β') he (map φ T.toAddMonoidHom h x) := by
  let f : QuantumMonoidAlgebra q β →ₛₗ[φ] QuantumMonoidAlgebra q' β' :=
    { toFun := map φ T.toAddMonoidHom h
      map_add' := (map φ T.toAddMonoidHom h).map_add
      map_smul' := map_smul φ T.toAddMonoidHom h }
  have hf (z : QuantumMonoidAlgebra q β) : f z = map φ T.toAddMonoidHom h z := by
    -- Only the local semilinear-map record is unfolded: its toFun is the quantum map.
    rfl
  have hmap : (mapShiftedDirectLimit d e T φ h).comp
        (d.toShiftedDirectLimitAlgHom (grade q β) hd).toLinearMap =
      (e.toShiftedDirectLimitAlgHom (grade q' β') he).toLinearMap.comp f := by
    apply (basis q β).ext
    intro p
    have hp := mapShiftedDirectLimit_finiteCoordinates d e T φ h hd he p 1
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, basis_apply,
      coe_positiveShiftEquiv, Subalgebra.coe_one, mul_one, hf] using hp
  exact congrArg (fun F : QuantumMonoidAlgebra q β →ₛₗ[φ]
    e.ShiftedDirectLimit (grade q' β') => F x) hmap

end Mei.QuantumMonoidAlgebra
