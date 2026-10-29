/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Specialization.Coefficient
public import Mei.Algebra.Lie.Filtered.Map
public import Mei.Algebra.Lie.Filtered.RestrictScalars
public import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Twisted specialization of completed tropical coefficient actions

Weighted coefficient specialization extends to the allowed-increment completions
over any common commutative scalar ring and intertwines their completed BCH
actions over rational scalars. The Lie label map is the existing
`coefficientGradedLieHom`, compared over rational scalars; the source and target
retain their original coefficient rings and completed group carriers.

We use Mathlib's monoid-algebra lift through `AddMonoidAlgebra.weightedMap`,
`AlgFiltration.mapCompletionₐ_completedBCHAction_of_gradedLieHom`, and the scalar
restriction comparisons of completed BCH actions. The twisted tropical action
follows Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section
noncomputable section

namespace Mei.LogarithmicVectorField

open _root_.AddMonoidAlgebra

section CompletedCoefficients

variable {K R S Γ : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [AddCommMonoid Γ]
  (d : PositiveDegrees Γ) (Q : AddSubmonoid Γ)
  (φ : R →ₐ[K] S) (χ : Multiplicative Γ →* S)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := S) d Q
local notation "ψ" => weightedMap φ (χ.comp Q.subtype.toMultiplicative)
local notation "hψ" => fun k =>
  TropicalVertexCoefficientAction.filtration_ideal_le_comap_weightedMap d Q
    φ (χ.comp Q.subtype.toMultiplicative) (k + 1)

/-- The coefficient specialization on allowed-increment completions. -/
def completedWeightedMap : (F).completion →ₐ[K] (G).completion :=
  (F).mapCompletionₐ G ψ id monotone_id hψ

/-- Completed specialization agrees with the weighted map on original coefficients. -/
@[simp]
theorem completedWeightedMap_of (a : R[Q]) :
    completedWeightedMap d Q φ χ ((F).toCompletion a) =
      (G).toCompletion (ψ a) := by
  exact (F).mapCompletionₐ_toCompletion G ψ id monotone_id hψ a

/-- Every finite component is the quotient map induced by weighted specialization. -/
@[simp]
theorem projection_completedWeightedMap (k : ℕ) (a : (F).completion) :
    (G).projection k (completedWeightedMap d Q φ χ a) =
      Ideal.quotientMapₐ ((G).ideal (k + 1)) ψ (hψ k) ((F).projection k a) :=
  (F).projection_mapCompletionₐ G ψ id monotone_id hψ k a

/-- Identity coefficients and unit weights induce the identity on the completion. -/
@[simp]
theorem completedWeightedMap_id :
    completedWeightedMap d Q (AlgHom.id K R) (1 : Multiplicative Γ →* R) =
      AlgHom.id K (F).completion := by
  unfold completedWeightedMap
  have h : weightedMap (AlgHom.id K R)
      ((1 : Multiplicative Γ →* R).comp Q.subtype.toMultiplicative) =
        AlgHom.id K R[Q] := by
    simp only [MonoidHom.one_comp, weightedMap_id]
  simp only [h, AlgFiltration.mapCompletionₐ_id]

/-- Successive completed coefficient maps multiply the transported weights. -/
@[simp]
theorem completedWeightedMap_comp {T : Type*} [CommRing T] [Algebra K T]
    (τ : S →ₐ[K] T) (ω : Multiplicative Γ →* T) :
    (completedWeightedMap d Q τ ω).comp (completedWeightedMap d Q φ χ) =
      completedWeightedMap d Q (τ.comp φ) (ω * τ.toMonoidHom.comp χ) := by
  have hc : (weightedMap τ (ω.comp Q.subtype.toMultiplicative)).comp ψ =
      weightedMap (τ.comp φ)
        ((ω * τ.toMonoidHom.comp χ).comp Q.subtype.toMultiplicative) := by
    simp only [weightedMap_comp,
      MonoidHom.mul_comp, MonoidHom.comp_assoc]
  have h := (F).mapCompletionₐ_comp G ψ id monotone_id hψ
    (TropicalVertexCoefficientAction.filtration (R := T) d Q)
    (weightedMap τ (ω.comp Q.subtype.toMultiplicative)) id monotone_id
    (fun k => TropicalVertexCoefficientAction.filtration_ideal_le_comap_weightedMap d Q
      τ (ω.comp Q.subtype.toMultiplicative) (k + 1))
  simpa only [completedWeightedMap, hc, Function.id_comp] using h.symm

end CompletedCoefficients

section Completed

universe u v w

variable {R S : Type u} {Γ : Type v} {Λ : Type w}
  [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)
  (φ : R →+* S) (χ : Multiplicative Γ →* S)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d Q
local notation "G" => TropicalVertexCoefficientAction.filtration (R := S) d Q
local notation "ψ" => weightedMap φ.toRatAlgHom (χ.comp Q.subtype.toMultiplicative)
local notation "hψ" => fun k =>
  TropicalVertexCoefficientAction.filtration_ideal_le_comap_weightedMap d Q
    φ.toRatAlgHom (χ.comp Q.subtype.toMultiplicative) (k + 1)
local notation "ℒ" => tropicalVertexGrading (R := R) d ρ
local notation "ℳ" => tropicalVertexGrading (R := S) d ρ
local notation "E" => d.completedBCHRestrictScalarsEquiv (R := ℚ) ℒ
local notation "E'" => d.completedBCHRestrictScalarsEquiv (R := ℚ) ℳ

variable [DecidableEq Γ]

/-- Twisted specialization on the actual completed tropical label groups. -/
def completedCoefficientMap : d.completedBCHGroup ℒ →* d.completedBCHGroup ℳ :=
  (E').toMonoidHom.comp
    ((coefficientGradedLieHom ρ φ.toRatAlgHom χ d).completedMap.comp (E).symm.toMonoidHom)

/-- Each label projection is obtained by specializing the finite Lie logarithm. -/
@[simp]
theorem projection_completedCoefficientMap (k : ℕ) (g : d.completedBCHGroup ℒ) :
    CompletedGroup.projection k (completedCoefficientMap d ρ φ χ g) =
      BCHGroup.exp ((d.truncatedRestrictScalarsEquiv (R := ℚ) ℳ k)
        ((coefficientGradedLieHom ρ φ.toRatAlgHom χ d).truncatedMap (a := k) k (by simp)
          ((d.truncatedRestrictScalarsEquiv (R := ℚ) ℒ k).symm
            (BCHGroup.log (CompletedGroup.projection k g))))) := by
  simp only [completedCoefficientMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    PositiveDegrees.projection_completedBCHRestrictScalarsEquiv]
  rw [GradedLieHom.projection_completedMap_of_le _ k (a := k) (by simp)]
  simp only [PositiveDegrees.projection_completedBCHRestrictScalarsEquiv_symm,
    LieHom.bchGroupMap_exp, LieEquiv.coe_toLieHom]
  rfl

/-- Specialization carries the exponential of an original field to that of its image. -/
@[simp]
theorem completedCoefficientMap_expToCompletion (x : tropicalVertexLieAlgebra (R := R) d ρ) :
    completedCoefficientMap d ρ φ χ (d.expToCompletion ℒ x) =
      d.expToCompletion ℳ (coefficientGradedLieHom ρ φ.toRatAlgHom χ d x) := by
  apply CompletedGroup.ext
  intro k
  simp only [projection_completedCoefficientMap, PositiveDegrees.projection_expToCompletion,
    BCHGroup.log_exp, LieIdeal.mkQ_apply,
    PositiveDegrees.truncatedRestrictScalarsEquiv_symm_mk,
    GradedLieHom.truncatedMap_mk, PositiveDegrees.truncatedRestrictScalarsEquiv_mk]
  rfl

/-- The identity specialization fixes completed labels. -/
@[simp]
theorem completedCoefficientMap_id :
    completedCoefficientMap d ρ (RingHom.id R) (1 : Multiplicative Γ →* R) =
      MonoidHom.id (d.completedBCHGroup ℒ) := by
  have hφ : (RingHom.id R).toRatAlgHom = AlgHom.id ℚ R := by ext; rfl
  ext g
  simp [completedCoefficientMap, hφ, coefficientGradedLieHom_id,
    GradedLieHom.completedMap_id]

/-- Completed label specializations compose with the transported product of weights. -/
@[simp]
theorem completedCoefficientMap_comp {T : Type u} [CommRing T] [Algebra ℚ T]
    (τ : S →+* T) (ω : Multiplicative Γ →* T) :
    (completedCoefficientMap d ρ τ ω).comp (completedCoefficientMap d ρ φ χ) =
      completedCoefficientMap d ρ (τ.comp φ) (ω * τ.toMonoidHom.comp χ) := by
  have hτ : τ.toRatAlgHom.toMonoidHom = τ.toMonoidHom := by ext r; rfl
  have hφ : (τ.comp φ).toRatAlgHom = τ.toRatAlgHom.comp φ.toRatAlgHom := by
    ext r
    rfl
  have h := GradedLieHom.completedMap_eq_of_toLieHom_eq
    (coefficientGradedLieHom ρ (τ.comp φ).toRatAlgHom (ω * τ.toMonoidHom.comp χ) d)
    ((coefficientGradedLieHom ρ τ.toRatAlgHom ω d).comp
      (coefficientGradedLieHom ρ φ.toRatAlgHom χ d))
    (by simpa only [GradedLieHom.toLieHom_comp, hφ,
      hτ] using
      (coefficientGradedLieHom_comp ρ φ.toRatAlgHom χ d τ.toRatAlgHom ω).symm)
  have hc := h.trans (GradedLieHom.completedMap_comp _ _)
  apply MonoidHom.ext
  intro g
  simpa only [completedCoefficientMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using
    congrArg (d.completedBCHRestrictScalarsEquiv (R := ℚ)
      (tropicalVertexGrading (R := T) d ρ))
      (DFunLike.congr_fun hc ((E).symm g)).symm

open scoped TropicalVertexCoefficientAction

variable [Fact (d.monoid ≤ Q)]

/-- Twisted coefficient specialization intertwines arbitrary completed tropical
labels and arbitrary completed coefficient inputs. -/
theorem completedWeightedMap_completedBCHAction
    (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    completedWeightedMap d Q φ.toRatAlgHom χ ((F).completedBCHAction d ℒ g a) =
      (G).completedBCHAction d ℳ (completedCoefficientMap d ρ φ χ g)
        (completedWeightedMap d Q φ.toRatAlgHom χ a) := by
  let : LieModule ℚ (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] :=
    LieModule.restrictScalars (S := R)
  let : LieModule ℚ (tropicalVertexLieAlgebra (R := S) d ρ) S[Q] :=
    LieModule.restrictScalars (S := S)
  have h := (F).mapCompletionₐ_completedBCHAction_of_gradedLieHom G
    (coefficientGradedLieHom ρ φ.toRatAlgHom χ d) ψ
    (fun x a => weightedMap_tropicalVertexCoefficientAction d ρ Q φ.toRatAlgHom χ
      Fact.out x a) id monotone_id hψ ((E).symm g) a
  simpa only [AlgFiltration.completedBCHAction_restrictScalars,
    AlgEquiv.restrictScalars_apply, MulEquiv.apply_symm_apply,
    completedWeightedMap, completedCoefficientMap, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] using h

end Completed
end Mei.LogarithmicVectorField
