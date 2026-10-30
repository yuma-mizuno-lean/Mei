/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.WallFunction
public import Mei.Algebra.Lie.Logarithmic.Pairing.Composition

/-!
# Tangent fields with restricted characters

If a character belongs to a submodule `U`, its tangent fields take values in
the corresponding positive character Lie subalgebra. This remains true after
degree completion. Exponentiating there gives a label whose image under the
graded inclusion is the original function-wall label. Thus pairings defined
only on selected characters can be applied to actual function-wall labels.

The constructions use `tropicalTangentField`, `ModuleFiltration.completionMap`
and the inherited grading on `tropicalSubalgebra`. The function-wall convention
is that of Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*,
§1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.LogarithmicVectorField

open _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ρ : Γ →+ Λ)
  (U : Submodule R (Λ →+ R))

local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "ℳ" => tropicalSubalgebraGrading ρ U d
local notation "F" => LieIdeal.completionFiltration (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)
local notation "G" => LieIdeal.completionFiltration (d.degreeIdeal ℳ) (d.degreeIdeal_antitone ℳ)

/-- A tangent field uses only scalar multiples of its specified character. -/
theorem tropicalTangentField_mem_tropicalSubalgebra (m : U)
    (u : R[tropicalTangentMonoid d ρ m.val]) :
    tropicalTangentField d ρ m.val u ∈ tropicalSubalgebra ρ U d := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero] using (tropicalSubalgebra ρ U d).zero_mem
  | add a b ha hb => simpa only [map_add] using add_mem ha hb
  | single q c =>
    by_cases hq : (q : Γ) = 0
    · have hq' : q = 0 := Subtype.ext hq
      simp only [hq', tropicalTangentField_single_zero]
      exact zero_mem _
    · rw [mem_tropicalSubalgebra_iff, coe_tropicalTangentField_single d ρ m.val hq,
        ← mem_characterSubalgebra_iff, single_mem_characterSubalgebra_iff]
      exact U.smul_mem c m.property

/-- The tangent-field map with codomain restricted to the selected characters. -/
def tropicalTangentFieldToSubalgebra (m : U) :
    R[tropicalTangentMonoid d ρ m.val] →ₗ[R] tropicalSubalgebra ρ U d :=
  (tropicalTangentField d ρ m.val).codRestrict _
    (tropicalTangentField_mem_tropicalSubalgebra d ρ U m)

/-- Forgetting the character restriction recovers the original tangent field. -/
@[simp]
theorem coe_tropicalTangentFieldToSubalgebra (m : U)
    (u : R[tropicalTangentMonoid d ρ m.val]) :
    (tropicalTangentFieldToSubalgebra d ρ U m u).val =
      tropicalTangentField d ρ m.val u := (rfl)

/-- Restricting characters does not alter the order of a tangent field. -/
theorem tropicalTangentFieldToSubalgebra_mem_degreeIdeal (m : U) {k : ℕ}
    {u : R[tropicalTangentMonoid d ρ m.val]}
    (hu : u ∈ (TropicalVertexCoefficientAction.filtration
      (R := R) d (tropicalTangentMonoid d ρ m.val)).ideal (k + 1)) :
    tropicalTangentFieldToSubalgebra d ρ U m u ∈ d.degreeIdeal ℳ k := by
  -- Compare submodules to rewrite the grading without transporting its Lie algebra instance.
  have he := congrArg LieSubmodule.toSubmodule
    ((tropicalSubalgebra ρ U d).degreeIdeal_eq_comap ℒ d
      (tropicalSubalgebra_isHomogeneous ρ U d) k)
  simp only [PositiveDegrees.degreeIdeal_toSubmodule, LieIdeal.comap_toSubmodule] at he
  rw [← LieSubmodule.mem_toSubmodule, PositiveDegrees.degreeIdeal_toSubmodule,
    tropicalSubalgebraGrading_def, he]
  simpa only [Submodule.mem_comap, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
    coe_tropicalTangentFieldToSubalgebra, ← PositiveDegrees.degreeIdeal_toSubmodule,
    LieSubmodule.mem_toSubmodule] using
      tropicalTangentField_mem_degreeIdeal d ρ m.val hu

variable (m : U)

local notation "H" => TropicalVertexCoefficientAction.filtration
  (R := R) d (tropicalTangentMonoid d ρ m.val)

/-- Completed tangent fields can be formed inside the selected-character algebra. -/
def completedTropicalTangentFieldToSubalgebra :
    (H).completion →ₗ[R] d.completedLie ℳ :=
  ((H).toModuleFiltration R).completionMap G
    (tropicalTangentFieldToSubalgebra d ρ U m) id monotone_id
    (fun _ _ hu => tropicalTangentFieldToSubalgebra_mem_degreeIdeal d ρ U m
      (by simpa only [id_eq, AlgFiltration.toModuleFiltration_submodule,
        Submodule.restrictScalars_mem] using hu)) ∘ₗ
      (H).moduleCompletionEquiv.symm.toLinearMap

/-- A finite representative computes every projection of the restricted completed field. -/
theorem projection_completedTropicalTangentFieldToSubalgebra (k : ℕ)
    (u : (H).completion) (v : R[tropicalTangentMonoid d ρ m.val])
    (hv : (H).projection k u = Ideal.Quotient.mk _ v) :
    (G).projection k (completedTropicalTangentFieldToSubalgebra d ρ U m u) =
      (d.degreeIdeal ℳ k).mkQ (tropicalTangentFieldToSubalgebra d ρ U m v) := by
  simp only [completedTropicalTangentFieldToSubalgebra, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ModuleFiltration.projection_completionMap, id_eq,
    AlgFiltration.projection_moduleCompletionEquiv_symm, hv]
  rw [← Ideal.Quotient.mk_eq_mk,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply]
  rfl

/-- Forming a restricted tangent field commutes with completing a finite coefficient. -/
@[simp]
theorem completedTropicalTangentFieldToSubalgebra_toCompletion
    (u : R[tropicalTangentMonoid d ρ m.val]) :
    completedTropicalTangentFieldToSubalgebra d ρ U m ((H).toCompletion u) =
      LieIdeal.toCompletion (d.degreeIdeal ℳ) (d.degreeIdeal_antitone ℳ)
        (tropicalTangentFieldToSubalgebra d ρ U m u) := by
  simp only [completedTropicalTangentFieldToSubalgebra, LinearMap.comp_apply,
    LinearEquiv.coe_coe, AlgFiltration.moduleCompletionEquiv_symm_toCompletion,
    ModuleFiltration.completionMap_of]
  apply (G).completion_ext
  intro k
  simp only [ModuleFiltration.projection_of, ← LieIdeal.completionProjection_apply,
    LieIdeal.completionProjection_toCompletion, LieIdeal.mkQ_apply]

/-- Forgetting restricted characters after completion gives the original completed field. -/
theorem completionMap_completedTropicalTangentFieldToSubalgebra (u : (H).completion) :
    (G).completionMap F (TropicalPairing.id d ρ U).gradedLieHom.toLieHom.toLinearMap
        id monotone_id (fun k _ hx =>
          (TropicalPairing.id d ρ U).gradedLieHom.map_mem_degreeIdeal k
            (by simpa only [LieIdeal.completionFiltration_succ,
              LieSubmodule.mem_toSubmodule, TropicalPairing.id_degreeMap,
              PositiveDegreeMap.id_modulus, id_eq] using hx))
        (completedTropicalTangentFieldToSubalgebra d ρ U m u) =
      completedTropicalTangentField d ρ m.val u := by
  apply (F).completion_ext
  intro k
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((H).projection k u)
  simp only [ModuleFiltration.projection_completionMap, id_eq,
    projection_completedTropicalTangentFieldToSubalgebra d ρ U m k u v hv.symm]
  simp only [LieIdeal.mkQ_apply, Submodule.mapQ_apply, LieHom.coe_toLinearMap,
    GradedLieHom.coe_toLieHom,
    TropicalPairing.gradedLieHom_id_apply, coe_tropicalTangentFieldToSubalgebra]
  simpa only [LieIdeal.completionProjection_apply, LieIdeal.mkQ_apply] using
    (completionProjection_completedTropicalTangentField d ρ m.val k u v hv.symm).symm

variable [Algebra ℚ R]

/-- The completed label formed inside the character restriction maps to the original
function-wall label. This permits applying pairings whose character domain is `U`. -/
@[simp]
theorem completedMap_completedBCHExp_completedTropicalTangentFieldToSubalgebra
    (u : (H).completion) :
    (TropicalPairing.id d ρ U).gradedLieHom.completedMap
        (d.completedBCHExp ℳ (completedTropicalTangentFieldToSubalgebra d ρ U m u)) =
      d.completedBCHExp ℒ (completedTropicalTangentField d ρ m.val u) := by
  apply (d.completedBCHExp ℒ).symm.injective
  rw [GradedLieHom.completedBCHExp_symm_completedMap, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  have hmod : (PositiveDegreeMap.id d).modulus = id :=
    funext (fun k => PositiveDegreeMap.id_modulus (d := d) k)
  simpa only [TropicalPairing.id_degreeMap, hmod] using
      completionMap_completedTropicalTangentFieldToSubalgebra d ρ U m u

end Mei.LogarithmicVectorField
