/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Hom
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Map

/-!
# Coefficient change in global quantum algebras over a common base

A coefficient algebra map preserving the quantum factor sets induces an algebra
map on the chosen-ambient global coefficients, keeping every exponent fixed.
The homogeneous pieces are restricted to the common scalar ring, so this also
allows noninjective changes of coefficient rings, including reduction modulo a
prime and specialization of the quantum parameter. The construction uses the
chosen ambient homogeneous pieces, with no comparison with other ambient completions.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {k R S Γ : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [AddCommGroup Γ] [DecidableEq Γ]
  (d : PositiveDegrees Γ) {q : Rˣ} {q' : Sˣ}
  {β β' : LinearMap.BilinForm ℤ Γ}
  (φ : R →ₐ[k] S)
  (h : ∀ p r, Units.map φ.toMonoidHom (q ^ β p r) = q' ^ β' p r)

/-- Change quantum coefficients in the global algebra, restricting grading scalars to the
common base. Compatibility of factor sets permits specializations as well as embeddings. -/
def globalCoefficientMap :
    d.ShiftedDirectLimit (fun u => (grade q β u).restrictScalars k) →ₐ[k]
      d.ShiftedDirectLimit (fun u => (grade q' β' u).restrictScalars k) :=
  d.shiftedDirectLimitAlgHom _ _ (mapAlgHom φ (AddMonoidHom.id Γ) h)
    (coefficientMap_mem_grade φ h)

/-- The global quantum coefficient change is the generic degree-preserving algebra extension. -/
theorem globalCoefficientMap_def :
    globalCoefficientMap d φ h =
      d.shiftedDirectLimitAlgHom _ _ (mapAlgHom φ (AddMonoidHom.id Γ) h)
        (coefficientMap_mem_grade φ h) := by
  -- This is the defining generic extension, with scalars restricted to the common base.
  rfl

/-- Every ambient coefficient is changed by the original quantum algebra map. -/
@[simp]
theorem coe_shiftedDirectLimitComponents_globalCoefficientMap
    (x : d.ShiftedDirectLimit (fun u => (grade q β u).restrictScalars k)) (u : Γ) :
    (d.shiftedDirectLimitComponents (fun v => (grade q' β' v).restrictScalars k)
        (globalCoefficientMap d φ h x) u : QuantumMonoidAlgebra q' β') =
      map φ.toRingHom (AddMonoidHom.id Γ) h
        (d.shiftedDirectLimitComponents (fun v => (grade q β v).restrictScalars k) x u) := by
  rw [globalCoefficientMap_def]
  have hc := d.coe_shiftedDirectLimitComponents_algHom
    (R := k) (A := QuantumMonoidAlgebra q β) (B := QuantumMonoidAlgebra q' β')
    (fun v => (grade q β v).restrictScalars k)
    (fun v => (grade q' β' v).restrictScalars k)
    (mapAlgHom φ (AddMonoidHom.id Γ) h) (coefficientMap_mem_grade φ h) x u
  exact hc.trans (mapAlgHom_apply φ (AddMonoidHom.id Γ) h _)

/-- An original finite quantum coefficient can be changed before or after global embedding. -/
@[simp]
theorem globalCoefficientMap_toShiftedDirectLimitAlgHom
    (hspan : ∀ p : Γ, ∃ a b : d.monoid, p = (a : Γ) - b)
    (a : QuantumMonoidAlgebra q β) :
    globalCoefficientMap d φ h (d.toShiftedDirectLimitAlgHom _ hspan a) =
      d.toShiftedDirectLimitAlgHom _ hspan (map φ.toRingHom (AddMonoidHom.id Γ) h a) := by
  rw [globalCoefficientMap_def,
    PositiveDegrees.shiftedDirectLimitAlgHom_toShiftedDirectLimitAlgHom, mapAlgHom_apply]

end Mei.QuantumMonoidAlgebra
