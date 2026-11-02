/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mei.Algebra.Lie.Logarithmic.TangentRestriction
public import Mei.Algebra.Lie.Logarithmic.Pairing.Completion

/-!
# Transport of tangent wall labels along tropical pairings

A tropical pairing sends a tangent field `u ∂_m`, all of whose characters are
multiples of the chosen character `m`, to the tangent field with the paired
coefficient and the paired character. The construction first transports finite
tangent coefficients. Taking completed exponentials then transports the
corresponding function-wall labels, which is enough for polynomial wall inputs:
at every coefficient order their logarithm is a finite tangent coefficient.
Arbitrary completed tangent coefficients are not treated here.

This is the label-level comparison used when a finite-index change of lattice
transports a rank-two polynomial input. In that application the paired
character is the primitive normal of the image ray.

The tangent-field convention follows Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5, and the finite-index specialization is the one used in
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
Theorem 9.5 (arXiv:2503.03719v1).
-/

public noncomputable section

open _root_.AddMonoidAlgebra

namespace Mei.TropicalPairing

open LogarithmicVectorField

universe u v w

variable {R : Type u} [CommRing R] [Algebra ℚ R]
  {Γ Γ' : Type v} {Λ Λ' : Type w}
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  [DecidableEq Γ] [DecidableEq Γ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'}
  {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {U : Submodule R (Λ →+ R)}

variable (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U) (m : U)

/-- The additive map of tangent monoids induced by a tropical pairing. A degree
tangent to `m` is sent to a degree tangent to the paired character. -/
def tangentDegreeMap :
    tropicalTangentMonoid d ρ m.val →+ tropicalTangentMonoid e ρ' (p.characterMap m) where
  toFun q :=
    ⟨p.degreeMap q.val, by
      have hq := (mem_tropicalTangentMonoid (d := d) (ρ := ρ) (m := m.val) q.val).mp
        q.property
      rw [mem_tropicalTangentMonoid]
      exact ⟨p.degreeMap.map_mem hq.1, by
        rw [p.eval_eq m hq.1]
        exact hq.2⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

omit [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ'] in
@[simp]
theorem tangentDegreeMap_apply (q : tropicalTangentMonoid d ρ m.val) :
    ((p.tangentDegreeMap m q : tropicalTangentMonoid e ρ' (p.characterMap m)) :
      Γ') = p.degreeMap q.val := (rfl)

/-- The coefficient map on tangent monoid algebras induced by a tropical pairing. -/
def tangentCoefficientMap :
    R[tropicalTangentMonoid d ρ m.val] →ₐ[R]
      R[tropicalTangentMonoid e ρ' (p.characterMap m)] :=
  mapDomainAlgHom R R (p.tangentDegreeMap m)

omit [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ'] in
@[simp]
theorem tangentCoefficientMap_single
    (q : tropicalTangentMonoid d ρ m.val) (c : R) :
    p.tangentCoefficientMap m (single q c) =
      single (p.tangentDegreeMap m q) c := by
  simp [tangentCoefficientMap]

omit [Algebra ℚ R] in
/-- A tropical pairing transports a finite tangent field to the tangent field
of the transported coefficient and the paired character. -/
@[simp]
theorem gradedLieHom_tropicalTangentFieldToSubalgebra
    (u : R[tropicalTangentMonoid d ρ m.val]) :
    ((p.gradedLieHom (tropicalTangentFieldToSubalgebra d ρ U m u)).val :
      LogarithmicVectorField R Γ' Λ' ρ') =
      (tropicalTangentField e ρ' (p.characterMap m) (p.tangentCoefficientMap m u) :
        LogarithmicVectorField R Γ' Λ' ρ') := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add u v hu hv =>
      simpa only [map_add, AddMemClass.coe_add] using congrArg₂ (· + ·) hu hv
  | single q c =>
    by_cases hq : (q : Γ) = 0
    · have hq' : q = 0 := Subtype.ext hq
      subst hq'
      have hz : tropicalTangentFieldToSubalgebra d ρ U m (single 0 c) = 0 := by
        apply Subtype.ext
        rw [coe_tropicalTangentFieldToSubalgebra, tropicalTangentField_single_zero]
        rfl
      rw [hz, map_zero]
      simp only [tangentCoefficientMap, mapDomainAlgHom_apply, mapDomain_single,
        AddSubmonoid.coe_zero, map_zero, tropicalTangentField_single_zero]
    · have hq' : q.val ≠ 0 := hq
      have hqT := (mem_tropicalTangentMonoid (d := d) (ρ := ρ) (m := m.val) q.val).mp
        q.property
      have hq0 : p.degreeMap q.val ≠ 0 := p.degreeMap.map_ne_zero hqT.1 hq'
      have hsrc : tropicalTangentFieldToSubalgebra d ρ U m (single q c) =
          c • tropicalSingle (d := d) (ρ := ρ) (U := U) hqT.1 hq'
            m hqT.2 := by
        apply Subtype.ext
        apply Subtype.ext
        rw [coe_tropicalTangentFieldToSubalgebra]
        rw [coe_tropicalTangentField_single d ρ m.val hq']
        simp only [SetLike.val_smul, coe_tropicalSingle, map_smul]
      rw [hsrc, map_smul]
      have hg : p.gradedLieHom (tropicalSingle (d := d) (ρ := ρ) (U := U) hqT.1 hq'
          m hqT.2) =
          ⟨single ρ' (p.degreeMap q.val) (p.characterMap m),
            single_mem_tropicalVertexLieAlgebra e ρ' (p.degreeMap.map_mem hqT.1) hq0
              (p.characterMap m) (by rw [p.eval_eq m hqT.1]; exact hqT.2)⟩ := by
        apply Subtype.ext
        exact coe_gradedLieHom_tropicalSingle p hqT.1 hq' m hqT.2
      rw [hg]
      change (c • single ρ' (p.degreeMap q.val) (p.characterMap m) :
        LogarithmicVectorField R Γ' Λ' ρ') = _
      change c • single ρ' (p.degreeMap q.val) (p.characterMap m) =
        (tropicalTangentField e ρ' (p.characterMap m)
          (mapDomainAlgHom R R (p.tangentDegreeMap m) (single q c)) :
            LogarithmicVectorField R Γ' Λ' ρ')
      rw [mapDomainAlgHom_apply, mapDomain_single,
        coe_tropicalTangentField_single e ρ' (p.characterMap m) hq0,
        tangentDegreeMap_apply]
      exact (map_smul (LogarithmicVectorField.single ρ' (p.degreeMap q.val)) c
        (p.characterMap m)).symm

/-- A tropical pairing transports the completed exponential of a finite tangent
field. This is the label-level form used by polynomial wall inputs: at each
coefficient order the logarithm is a finite tangent coefficient, and the paired
completed label is the exponential of the paired finite field. -/
theorem completedMap_expToCompletion_tropicalTangentFieldToSubalgebra
    (u : R[tropicalTangentMonoid d ρ m.val]) :
    p.gradedLieHom.completedMap
        (d.expToCompletion (tropicalSubalgebraGrading ρ U d)
          (tropicalTangentFieldToSubalgebra d ρ U m u)) =
      (e.expToCompletion (tropicalVertexGrading (R := R) e ρ')
        (tropicalTangentField e ρ' (p.characterMap m)
          (p.tangentCoefficientMap m u) : tropicalVertexLieAlgebra (R := R) e ρ') :
        e.completedBCHGroup (tropicalVertexGrading (R := R) e ρ')) := by
  rw [GradedLieHom.completedMap_expToCompletion]
  apply congrArg
  apply Subtype.ext
  exact p.gradedLieHom_tropicalTangentFieldToSubalgebra m u

end Mei.TropicalPairing
