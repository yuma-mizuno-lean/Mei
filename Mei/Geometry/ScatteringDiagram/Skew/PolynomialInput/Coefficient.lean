/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Principal
public import Mei.Geometry.ScatteringDiagram.Skew.Coefficient.Completion
public import Mei.Algebra.Lie.Logarithmic.MonoidSpecialization
public import Mei.RingTheory.FilteredAlgebra.AlgHom

/-!
# Principal coefficient specialization of polynomial inputs

For a BLM polynomial input, specialize the independent coefficient variables by
`p_{i,s} ↦ a_{i,s} t_i^s`, while transporting the spatial character to the
normalized principal datum. The source coefficient monoid allows every Laurent
character and nonnegative multiplicities of all the independent variables.
The polynomial weights `a^b` need not be units. The substitution preserves the
positive-increment filtration with identity cutoff modulus, and therefore extends
to the coefficient completions. Its initial functions become the principal
polynomials with coefficients `a_{i,s}`.

We use `BLMPolynomialInput.principalLift`, Mathlib's
`AddMonoidAlgebra.lift`, `MvPolynomial.monomialOneHom`, and the filtered
coefficient-monoid specialization and completion APIs. The substitution follows
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*,
§8.1 and §9.2 (arXiv:2503.03719v1).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open Module _root_.AddMonoidAlgebra

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput) [DecidableEq ι] [Fintype ι]

local notation "d" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "e" => I.principalDatum.principalPositiveDegrees
  I.principalBasis.unfrozenBasis.positiveDegrees
local notation "Q'" => I.principalDatum.principalCoefficientMonoid
  I.principalBasis.unfrozenBasis.positiveDegrees

/-- Restrict the principal lattice lift to the two coefficient monoids. -/
def principalCoefficientExponent : I.coefficientMonoid →+ Q' :=
  (I.principalLift.toAddMonoidHom.comp I.coefficientMonoid.subtype).codRestrict Q' (fun q => by
    rw [I.principalDatum.mem_principalCoefficientMonoid]
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      AddSubmonoid.subtype_apply, I.principalLift_apply]
    apply AddSubmonoid.sum_mem
    intro α _
    rw [← Int.toNat_of_nonneg ((I.mem_coefficientMonoid _).mp q.property α)]
    exact nsmul_mem (nsmul_mem
      (by
        rw [← I.unfrozenBasis_principalBasis, Module.Basis.mem_positiveDegrees_monoid,
          Basis.repr_self]
        exact fun j => by simp [Finsupp.single_apply, ite_nonneg]) _) _)

@[simp]
theorem coe_principalCoefficientExponent (q : I.coefficientMonoid) :
    (I.principalCoefficientExponent q).val = I.principalLift q.val := (rfl)

/-- The lift carries every coefficient exponent into the principal coefficient monoid. -/
theorem map_coefficientMonoid_le :
    I.coefficientMonoid.map I.principalFiniteAlphabetLift.toAddMonoidHom ≤ Q' := by
  rintro _ ⟨q, hq, rfl⟩
  simpa only [coe_principalCoefficientExponent, I.principalFiniteAlphabetLift_apply] using
    (I.principalCoefficientExponent ⟨q, hq⟩).property

/-- A variable in slot `s` acquires the principal exponent `s r(ε_i)`. -/
theorem coe_principalCoefficientExponent_coefficientLetter (α : I.Letter) :
    (I.principalCoefficientExponent (I.coefficientLetter α)).val =
      ((α.2 : ℕ) + 1) • I.principalDatum.principalEmbedding
        ⟨Finsupp.single (α.1 : ι) 1, I.single_mem_principalDatum_unfrozen α.1⟩ := by
  rw [coe_principalCoefficientExponent, coe_coefficientLetter, I.principalLift_letter]

section Semiring

variable (R : Type*) [CommSemiring R]

/-- The polynomial weight `a^b` of an independent-variable multiplicity `b`. -/
def coefficientWeight : Multiplicative I.coefficientMonoid →* MvPolynomial I.Letter R :=
  (MvPolynomial.monomialOneHom R I.Letter).comp I.coefficientMultiplicity.toMultiplicative

omit [DecidableEq ι] in
@[simp]
theorem coefficientWeight_apply (q : I.coefficientMonoid) :
    I.coefficientWeight R (.ofAdd q) =
      MvPolynomial.monomial (I.coefficientMultiplicity q) (1 : R) := (rfl)

private def coefficientTwist : R[I.coefficientMonoid] →ₐ[R]
    (MvPolynomial I.Letter R)[I.coefficientMonoid] :=
  lift R _ _ (singleHom.comp
    ((I.coefficientWeight R).prod (MonoidHom.id _)))

omit [DecidableEq ι] in
private theorem coefficientTwist_single (q : I.coefficientMonoid) (r : R) :
    I.coefficientTwist R (single q r) =
      single q (MvPolynomial.C r * I.coefficientWeight R (.ofAdd q)) := by
  simp [coefficientTwist, lift_single, Algebra.smul_def, singleHom, single_mul_single]

/-- Substitute `p_{i,s} ↦ a_{i,s} t_i^s` in the native coefficient monoid algebras.
The spatial character is transported by the normalized principal lattice map. -/
def principalCoefficientMap : R[I.coefficientMonoid] →ₐ[R] (MvPolynomial I.Letter R)[Q'] :=
  (AlgHom.restrictScalars R (mapDomainAlgHom (MvPolynomial I.Letter R) (MvPolynomial I.Letter R)
    ((AddSubmonoid.inclusion I.map_coefficientMonoid_le).comp
      (I.principalFiniteAlphabetLift.toAddMonoidHom.addSubmonoidMap I.coefficientMonoid)))).comp
    (I.coefficientTwist R)

/-- The substitution retains the entire scalar and independent-variable weight
before distinct source exponents can merge under the principal lift. -/
@[simp]
theorem principalCoefficientMap_single (q : I.coefficientMonoid) (r : R) :
    I.principalCoefficientMap R (single q r) =
      single (I.principalCoefficientExponent q)
        (MvPolynomial.C r * MvPolynomial.monomial (I.coefficientMultiplicity q) 1) := by
  simp only [principalCoefficientMap, AlgHom.comp_apply, coefficientTwist_single,
    AlgHom.restrictScalars_apply, mapDomainAlgHom_apply, mapDomain_single, coefficientWeight_apply]
  congr 1
  apply Subtype.ext
  simp [coe_principalCoefficientExponent, I.principalFiniteAlphabetLift_apply]

/-- In principal polynomial coordinates, the variable in slot `s` is exactly
`a_{i,s} z^{s w_i} t_i^s`, with `w_i` transported to the principal character lattice. -/
theorem principalCoefficientPolynomialEquiv_principalCoefficientMap_letter (α : I.Letter) :
    I.principalDatum.principalCoefficientPolynomialEquiv
        I.principalBasis.unfrozenBasis.positiveDegrees
        I.principalBasis.unfrozenBasis.positiveDegreesMonoidEquiv
        (I.principalCoefficientMap R (single (I.coefficientLetter α) 1)) =
      MvPolynomial.monomial (Finsupp.single ⟨α.1, by simp⟩ ((α.2 : ℕ) + 1))
        (single (((α.2 : ℕ) + 1) • I.principalDatum.principalCharacter
          ⟨Finsupp.single (α.1 : ι) 1, I.single_mem_principalDatum_unfrozen α.1⟩)
          (MvPolynomial.X α)) := by
  rw [principalCoefficientMap_single,
    I.principalDatum.principalCoefficientPolynomialEquiv_single]
  simp only [coefficientMultiplicity_coefficientLetter, map_one, one_mul, MvPolynomial.X]
  have hp := I.coe_principalCoefficientExponent_coefficientLetter α
  rw [I.principalDatum.principalEmbedding_apply] at hp
  apply congrArg₂ (fun n c => MvPolynomial.monomial n c)
  · ext j
    rw [Module.Basis.positiveDegreesMonoidEquiv_apply]
    have h := congrArg Prod.snd hp
    simp only [Prod.smul_mk] at h
    dsimp only
    rw [h, ← I.unfrozenBasis_principalBasis, map_nsmul, Basis.repr_self]
    simp only [Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp
  · exact congrArg (fun p => single p (MvPolynomial.X α)) (congrArg Prod.fst hp)

/-- The principal substitution sends the initial function to the polynomial
with independent coefficients `a_{i,s}` at exponents `s r(ε_i)`. -/
@[simp]
theorem principalCoefficientMap_initialCoefficientFunction (i : B.unfrozenIndex) :
    I.principalCoefficientMap R (I.initialCoefficientFunction R i) =
      1 + ∑ s : Fin (I.multiplicity i),
        single (I.principalCoefficientExponent (I.coefficientLetter ⟨i, s⟩))
          (MvPolynomial.X ⟨i, s⟩) := by
  simp [initialCoefficientFunction_def, MvPolynomial.X]

/-- The coefficient substitution preserves the native positive-increment filtration.
The modulus is the identity, although a letter of multiplicity `s` acquires
principal order `s`. -/
theorem filtration_ideal_le_comap_principalCoefficientMap (k : ℕ) :
    (TropicalVertexCoefficientAction.filtration (R := R) d I.coefficientMonoid).ideal (k + 1) ≤
      ((TropicalVertexCoefficientAction.filtration (R := MvPolynomial I.Letter R) e Q').ideal
        (k + 1)).comap (I.principalCoefficientMap R) := by
  simpa only [I.principalFiniteAlphabetLift_modulus, principalCoefficientMap] using
    LogarithmicVectorField.filtration_ideal_le_comap_coefficientDegreeMap
      d I.coefficientMonoid (Algebra.ofId R (MvPolynomial I.Letter R))
      (I.coefficientWeight R) (I.coefficientTwist R) (I.coefficientTwist_single R)
      I.principalFiniteAlphabetLift I.map_coefficientMonoid_le k

end Semiring

section Completion

variable {R : Type*} [CommRing R]

local notation "F" => TropicalVertexCoefficientAction.filtration (R := R) d I.coefficientMonoid
local notation "G" => TropicalVertexCoefficientAction.filtration (R := MvPolynomial I.Letter R) e Q'

/-- The completed principal substitution, with identity cutoff modulus. -/
def principalCoefficientCompletionMap : (F).completion →ₐ[R] (G).completion :=
  (F).mapCompletionₐ G (I.principalCoefficientMap R) id monotone_id
    (I.filtration_ideal_le_comap_principalCoefficientMap R)

/-- Every finite projection is computed by the same-order quotient substitution. -/
@[simp]
theorem projection_principalCoefficientCompletionMap (k : ℕ) (a : (F).completion) :
    (G).projection k (I.principalCoefficientCompletionMap a) =
      Ideal.quotientMapₐ ((G).ideal (k + 1)) (I.principalCoefficientMap R)
        (I.filtration_ideal_le_comap_principalCoefficientMap R k) ((F).projection k a) :=
  (F).projection_mapCompletionₐ G _ id monotone_id _ k a

/-- The completed substitution extends the polynomial substitution. -/
@[simp]
theorem principalCoefficientCompletionMap_toCompletion (a : R[I.coefficientMonoid]) :
    I.principalCoefficientCompletionMap ((F).toCompletion a) =
      (G).toCompletion (I.principalCoefficientMap R a) :=
  (F).mapCompletionₐ_toCompletion G _ id monotone_id _ a

end Completion

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
