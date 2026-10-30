/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Coefficient
public import Mei.Algebra.MonoidAlgebra.Range
public import Mei.Algebra.Lie.Logarithmic.Positive

/-!
# Positivity of the principal substitution of polynomial inputs

For a BLM polynomial input, the substitution `p_{i,s} ↦ a_{i,s} t_i^s` of
`Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Coefficient` sends a monomial `r z^q`
of the native coefficient algebra to `r a^b z^{T q}`, where `b` is the multiplicity of the
independent variables in `q`. For a semiring map `σ : A →+* R` it therefore maps the
image `σ(A)[Q]` into the image `σ(A)[a][Q']` of the polynomials over `A`, and it is a
positive specialization (`Mei.PositiveSpecialization`) with identity cutoff modulus. For
`A = ℕ` and `R = ℚ`, coefficients with natural-number coefficients become coefficients whose
monomial coefficients are polynomials in the `a_{i,s}` with natural-number coefficients.

Combined with the intertwining of completed BCH actions, a label of the cylinder-normal
subalgebra that carries a coefficient to a positive element is transported to a principal
label that carries the substituted coefficient to a positive element.

The substitution follows Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput) [DecidableEq ι] [Fintype ι]

local notation "d" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "e" => I.principalDatum.principalPositiveDegrees
  I.principalBasis.unfrozenBasis.positiveDegrees
local notation "𝒬" => I.principalDatum.principalCoefficientMonoid
  I.principalBasis.unfrozenBasis.positiveDegrees

section CoefficientImage

variable {A R : Type*} [CommSemiring A] [CommSemiring R] (σ : A →+* R)

/-- The principal substitution sends `σ(A)[Q]` into the image of `A[a_{i,s}][Q']`. -/
theorem principalCoefficientMap_mem_rangeS {x : R[I.coefficientMonoid]}
    (hx : x ∈ (mapRingHom I.coefficientMonoid σ).rangeS) :
    I.principalCoefficientMap R x ∈ (mapRingHom 𝒬 (MvPolynomial.map (σ := I.Letter) σ)).rangeS :=
  AddMonoidAlgebra.map_mem_rangeS_mapRingHom σ (MvPolynomial.map σ)
    (I.principalCoefficientMap R).toAddMonoidHom (fun q a =>
      ⟨single (I.principalCoefficientExponent q)
        (MvPolynomial.C a * MvPolynomial.monomial (I.coefficientMultiplicity q) 1),
        by simp⟩) hx

end CoefficientImage

section Specialization

variable {A R : Type*} [CommSemiring A] [CommRing R] (σ : A →+* R)

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d I.coefficientMonoid
local notation "G" => TropicalVertexCoefficientAction.filtration (R := MvPolynomial I.Letter R) e 𝒬

/-- The principal substitution as a positive specialization from `σ(A)[Q]` to the image of
`A[a_{i,s}][Q']`, with identity cutoff modulus. -/
def principalCoefficientPositiveSpecialization :
    PositiveSpecialization F G (mapRingHom I.coefficientMonoid σ).rangeS
      (mapRingHom 𝒬 (MvPolynomial.map (σ := I.Letter) σ)).rangeS where
  toRingHom := I.principalCoefficientMap R
  exists_modulus := ⟨id, monotone_id, I.filtration_ideal_le_comap_principalCoefficientMap R⟩
  map_mem _ hx := I.principalCoefficientMap_mem_rangeS σ hx

@[simp]
theorem principalCoefficientPositiveSpecialization_toRingHom :
    (I.principalCoefficientPositiveSpecialization σ).toRingHom = I.principalCoefficientMap R :=
  (rfl)

/-- The completion map of the specialization is the completed principal substitution. -/
@[simp]
theorem completionMap_principalCoefficientPositiveSpecialization (a : (F).completion) :
    (I.principalCoefficientPositiveSpecialization σ).completionMap a =
      I.principalCoefficientCompletionMap a := by
  have hf : ∀ k, (F).ideal (id k + 1) ≤
      ((G).ideal (k + 1)).comap (I.principalCoefficientPositiveSpecialization σ).toRingHom :=
    fun k => I.filtration_ideal_le_comap_principalCoefficientMap R k
  have hm := (I.principalCoefficientPositiveSpecialization σ).completionMap_eq_mapCompletion id
    monotone_id hf
  refine (DFunLike.congr_fun hm a).trans (AlgFiltration.completion_ext _ fun k => ?_)
  -- Both sides are computed at order `k` by the quotient substitution.
  rw [projection_principalCoefficientCompletionMap (R := R),
    AlgFiltration.projection_mapCompletion]
  dsimp only [id]
  generalize (F).projection k a = y
  induction y using Submodule.Quotient.induction_on with | _ x => ?_
  exact (Ideal.quotientMap_mk ..).trans (Ideal.quotient_map_mkₐ ..).symm

/-- The completed principal substitution sends coefficients positive for `σ(A)[Q]` to
coefficients positive for the image of `A[a_{i,s}][Q']`. -/
theorem isPositive_principalCoefficientCompletionMap {a : (F).completion}
    (h : (F).IsPositive (mapRingHom I.coefficientMonoid σ).rangeS a) :
    (G).IsPositive (mapRingHom 𝒬 (MvPolynomial.map (σ := I.Letter) σ)).rangeS
      (I.principalCoefficientCompletionMap a) := by
  simpa only [completionMap_principalCoefficientPositiveSpecialization] using
    (I.principalCoefficientPositiveSpecialization σ).map_isPositive h

end Specialization

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

universe u

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

variable {N ι : Type u} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput) [DecidableEq ι] [Fintype ι]

local notation "d" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "e" => I.principalDatum.principalPositiveDegrees
  I.principalBasis.unfrozenBasis.positiveDegrees
local notation "𝒬" => I.principalDatum.principalCoefficientMonoid
  I.principalBasis.unfrozenBasis.positiveDegrees

section CompletedAction

open LogarithmicVectorField _root_.AddMonoidAlgebra
open scoped TropicalVertexCoefficientAction

variable {A R : Type*} [CommSemiring A] [CommRing R] [Algebra ℚ R] (σ : A →+* R)
  [DecidableEq (Module.Dual ℤ N)]
  [DecidableEq (Module.Dual ℤ I.principalDatum.sublattice)]

local notation "𝒮" => MvPolynomial I.Letter R
local notation "ρ" => AddMonoidHom.id (Module.Dual ℤ N × (I.Letter → ℤ))
local notation "ρ'" => AddMonoidHom.id
  (Module.Dual ℤ I.principalDatum.sublattice × I.principalDatum.unfrozen)
local notation "𝓛" => tropicalSubalgebraGrading ρ (I.alphabetNormalSpan R) d
local notation "𝓛'" => (fun n =>
  Submodule.restrictScalars R (tropicalVertexGrading (R := 𝒮) e ρ' n))
local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d I.coefficientMonoid
local notation "G" => TropicalVertexCoefficientAction.filtration (R := 𝒮) e 𝒬

local instance : Fact ((d).monoid ≤ I.coefficientMonoid) :=
  ⟨I.positiveDegrees_le_coefficientMonoid⟩

local instance : Fact ((e).monoid ≤ 𝒬) :=
  ⟨I.principalDatum.principalPositiveDegrees_le_coefficientMonoid
    I.principalBasis.unfrozenBasis.positiveDegrees⟩

local instance : LieModule R (tropicalVertexLieAlgebra (R := 𝒮) e ρ') 𝒮[𝒬] :=
  LieModule.restrictScalars R 𝒮 _ _

local instance : IsFiltrationRaising e 𝓛' ((G).toModuleFiltration R) :=
  IsFiltrationRaising.restrictScalars_algebra (R := R) (S := 𝒮) (G) e
    (tropicalVertexGrading (R := 𝒮) e ρ')

/-- If a label of the cylinder-normal subalgebra carries a coefficient to an element positive
for `σ(A)[Q]`, then the principal label carries the substituted coefficient to an element
positive for the image of `A[a_{i,s}][Q']`. -/
theorem isPositive_completedBCHAction_principalCoefficientGradedLieHom
    {g : (d).completedBCHGroup 𝓛} {a : (F).completion}
    (h : (F).IsPositive (mapRingHom I.coefficientMonoid σ).rangeS
      ((F).completedBCHAction d 𝓛 g a)) :
    (G).IsPositive (mapRingHom 𝒬 (MvPolynomial.map (σ := I.Letter) σ)).rangeS
      ((G).completedBCHAction (R := R) e 𝓛'
        ((I.principalCoefficientGradedLieHom R).completedMap g)
        (I.principalCoefficientCompletionMap a)) := by
  rw [← I.principalCoefficientCompletionMap_completedBCHAction R g a]
  exact isPositive_principalCoefficientCompletionMap I σ h

end CompletedAction

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
