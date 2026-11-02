/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeepSeek
-/
module

public import Mei.Algebra.Lie.Logarithmic.TangentRestriction

/-!
# Transport of tangent wall labels along tropical pairings

A tropical pairing sends a tangent field `u ∂_m`, all of whose characters are
multiples of the chosen character `m`, to the tangent field with the paired
coefficient and the paired character. The construction first transports finite
tangent coefficients, and then passes to completed coefficients: the transported
coefficient map respects the positive-increment filtration with the modulus of the
paired degree map, so it extends to the completions of the coefficient algebras.

Taking completed BCH exponentials then transports completed tangent fields, which
is the label-level form of the comparison: a completed label `exp(u ∂_m)`, with `u`
in the completion of the coefficient algebra, is sent to the label
`exp((ψ u) ∂_{p.characterMap m})` of the completed coefficient map `ψ`. For a finite
coefficient the completed transport restricts to the exponential of the transported
finite tangent field, which is
`completedMap_expToCompletion_tropicalTangentFieldToSubalgebra` below. Reducing a
polynomial wall function to these completed labels is done order by order and is
not carried out in this file.

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
theorem coe_tangentDegreeMap_apply (q : tropicalTangentMonoid d ρ m.val) :
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

omit [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ'] in
/-- The paired degree map carries the tangent monoid of `m` into the tangent monoid
of the paired character. -/
theorem map_tropicalTangentMonoid_le :
    (tropicalTangentMonoid d ρ m.val).map p.degreeMap.toAddMonoidHom ≤
      tropicalTangentMonoid e ρ' (p.characterMap m) := by
  rintro _ ⟨q, hq, rfl⟩
  exact (p.tangentDegreeMap m ⟨q, hq⟩).property

omit [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ'] in
/-- The transported coefficient map respects the tangent filtrations, with the
modulus of the paired degree map. -/
theorem tangentCoefficientMap_filtration (k : ℕ) :
    (TropicalVertexCoefficientAction.filtration (R := R) d
        (tropicalTangentMonoid d ρ m.val)).ideal (p.degreeMap.modulus k + 1) ≤
      ((TropicalVertexCoefficientAction.filtration (R := R) e
          (tropicalTangentMonoid e ρ' (p.characterMap m))).ideal (k + 1)).comap
        (p.tangentCoefficientMap m) := by
  have hT := p.map_tropicalTangentMonoid_le m
  have h := TropicalVertexCoefficientAction.filtration_ideal_le_comap_mapDomainAlgHom
    (R := R) (d := d)
    (Q := tropicalTangentMonoid d ρ m.val) (e := e)
    (Q' := tropicalTangentMonoid e ρ' (p.characterMap m)) p.degreeMap hT k
  have hmap : p.tangentDegreeMap m = (AddSubmonoid.inclusion hT).comp
      (p.degreeMap.toAddMonoidHom.addSubmonoidMap
        (tropicalTangentMonoid d ρ m.val)) :=
    AddMonoidHom.ext fun _ => Subtype.ext rfl
  simpa only [tangentCoefficientMap, hmap] using h

omit [DecidableEq Γ] [DecidableEq Γ'] in
/-- The coefficient map of a tropical pairing extended to the completions of the
tangent coefficient algebras, along the modulus of the paired degree map. -/
def completedTangentCoefficientMap :
    (TropicalVertexCoefficientAction.filtration (R := R) d
        (tropicalTangentMonoid d ρ m.val)).completion →ₐ[R]
      (TropicalVertexCoefficientAction.filtration (R := R) e
        (tropicalTangentMonoid e ρ' (p.characterMap m))).completion :=
  (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ m.val)).mapCompletionₐ
    (TropicalVertexCoefficientAction.filtration (R := R) e
      (tropicalTangentMonoid e ρ' (p.characterMap m)))
    (p.tangentCoefficientMap m) p.degreeMap.modulus p.degreeMap.monotone_modulus
    (p.tangentCoefficientMap_filtration m)

omit [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ'] in
/-- The completed coefficient map extends the transported finite coefficient map. -/
@[simp]
theorem completedTangentCoefficientMap_toCompletion
    (u : R[tropicalTangentMonoid d ρ m.val]) :
    p.completedTangentCoefficientMap m
        ((TropicalVertexCoefficientAction.filtration (R := R) d
          (tropicalTangentMonoid d ρ m.val)).toCompletion u) =
      (TropicalVertexCoefficientAction.filtration (R := R) e
        (tropicalTangentMonoid e ρ' (p.characterMap m))).toCompletion
        (p.tangentCoefficientMap m u) :=
  AlgFiltration.mapCompletionₐ_toCompletion _ _ _ _ _ _ _

omit [Algebra ℚ R] [DecidableEq Γ] [DecidableEq Γ'] in
/-- A finite representative computes every projection of the completed coefficient map. -/
theorem projection_completedTangentCoefficientMap (k : ℕ)
    (u : (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ m.val)).completion)
    (v : R[tropicalTangentMonoid d ρ m.val])
    (hv : (TropicalVertexCoefficientAction.filtration (R := R) d
        (tropicalTangentMonoid d ρ m.val)).projection (p.degreeMap.modulus k) u =
      Ideal.Quotient.mk _ v) :
    (TropicalVertexCoefficientAction.filtration (R := R) e
        (tropicalTangentMonoid e ρ' (p.characterMap m))).projection k
        (p.completedTangentCoefficientMap m u) =
      Ideal.Quotient.mk _ (p.tangentCoefficientMap m v) := by
  rw [completedTangentCoefficientMap, AlgFiltration.projection_mapCompletionₐ, hv,
    Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]

omit [Algebra ℚ R] in
/-- A tropical pairing transports a finite tangent field to the tangent field
of the transported coefficient and the paired character. -/
@[simp]
theorem coe_gradedLieHom_tropicalTangentFieldToSubalgebra
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
        rw [coe_tropicalTangentFieldToSubalgebra, tropicalTangentField_single_zero,
          ZeroMemClass.coe_zero]
      rw [hz, map_zero]
      simp [tangentCoefficientMap_single]
    · have hq' : q.val ≠ 0 := hq
      have hq0 : p.degreeMap q.val ≠ 0 :=
        p.degreeMap.map_ne_zero ((mem_tropicalTangentMonoid (d := d) (ρ := ρ)
          (m := m.val) q.val).mp q.property).1 hq'
      -- The restricted field of a single coefficient is a single positive generator.
      have hm : single ρ q.val (c • m.val) =
          (tropicalTangentFieldToSubalgebra d ρ U m (single q c)).val.val := by
        rw [coe_tropicalTangentFieldToSubalgebra,
          coe_tropicalTangentField_single d ρ m.val hq']
      rw [p.coe_gradedLieHom_of_homogeneous _ (c • m) hm, map_smul,
        tangentCoefficientMap_single,
        coe_tropicalTangentField_single e ρ' (p.characterMap m) hq0]
      rfl

omit [Algebra ℚ R] in
/-- A tropical pairing transports a completed tangent field, in the character
restriction, to the completed tangent field of the transported completed
coefficient and the paired character. -/
theorem completionMap_completedTropicalTangentFieldToSubalgebra
    (u : (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ m.val)).completion) :
    (LieIdeal.completionFiltration (d.degreeIdeal (tropicalSubalgebraGrading ρ U d))
        (d.degreeIdeal_antitone (tropicalSubalgebraGrading ρ U d))).completionMap
      (LieIdeal.completionFiltration (e.degreeIdeal (tropicalVertexGrading (R := R) e ρ'))
        (e.degreeIdeal_antitone (tropicalVertexGrading (R := R) e ρ')))
      p.gradedLieHom.toLieHom.toLinearMap p.degreeMap.modulus p.degreeMap.monotone_modulus
      (fun k _ hx => p.gradedLieHom.map_mem_degreeIdeal k hx)
      (completedTropicalTangentFieldToSubalgebra d ρ U m u) =
      completedTropicalTangentField e ρ' (p.characterMap m)
        (p.completedTangentCoefficientMap m u) := by
  let H := TropicalVertexCoefficientAction.filtration (R := R) d
    (tropicalTangentMonoid d ρ m.val)
  let F := LieIdeal.completionFiltration (d.degreeIdeal (tropicalSubalgebraGrading ρ U d))
    (d.degreeIdeal_antitone (tropicalSubalgebraGrading ρ U d))
  let G := LieIdeal.completionFiltration (e.degreeIdeal (tropicalVertexGrading (R := R) e ρ'))
    (e.degreeIdeal_antitone (tropicalVertexGrading (R := R) e ρ'))
  apply G.completion_ext
  intro k
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (H.projection (p.degreeMap.modulus k) u)
  rw [ModuleFiltration.projection_completionMap]
  simp only [projection_completedTropicalTangentFieldToSubalgebra d ρ U m
    (p.degreeMap.modulus k) u v hv.symm]
  simp only [LieIdeal.mkQ_apply, Submodule.mapQ_apply, LieHom.coe_toLinearMap,
    GradedLieHom.coe_toLieHom]
  rw [← LieIdeal.completionProjection_apply,
    completionProjection_completedTropicalTangentField e ρ' (p.characterMap m) k _
      (p.tangentCoefficientMap m v)
      (p.projection_completedTangentCoefficientMap m k u v hv.symm)]
  congr 1
  exact Subtype.ext (p.coe_gradedLieHom_tropicalTangentFieldToSubalgebra m v)

/-- A tropical pairing transports the completed exponential, in the character
restriction, of a completed tangent field to the completed exponential of the
transported completed coefficient and the paired character. -/
theorem completedMap_completedBCHExp_completedTropicalTangentFieldToSubalgebra
    (u : (TropicalVertexCoefficientAction.filtration (R := R) d
      (tropicalTangentMonoid d ρ m.val)).completion) :
    p.gradedLieHom.completedMap
        (d.completedBCHExp (tropicalSubalgebraGrading ρ U d)
          (completedTropicalTangentFieldToSubalgebra d ρ U m u)) =
      e.completedBCHExp (tropicalVertexGrading (R := R) e ρ')
        (completedTropicalTangentField e ρ' (p.characterMap m)
          (p.completedTangentCoefficientMap m u)) := by
  apply (e.completedBCHExp (tropicalVertexGrading (R := R) e ρ')).symm.injective
  rw [GradedLieHom.completedBCHExp_symm_completedMap, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  exact p.completionMap_completedTropicalTangentFieldToSubalgebra m u

/-- A tropical pairing transports the completed exponential of a finite tangent
field: the image is the exponential of the transported finite field. -/
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
  exact p.coe_gradedLieHom_tropicalTangentFieldToSubalgebra m u

end Mei.TropicalPairing
