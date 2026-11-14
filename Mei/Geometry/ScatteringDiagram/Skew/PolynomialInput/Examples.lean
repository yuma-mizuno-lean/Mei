/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Examples
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Pentagon
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Commuting
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.HyperplaneTerm
public import Mei.Geometry.ScatteringDiagram.Skew.Principal.Examples

/-!
# Checks on polynomial inputs of generalized cluster scattering diagrams

Three checks on `BLMPolynomialInput`, and instances of the positive representatives of
`Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Commuting` and
`Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon`.

* *Terms of one initial polynomial on different rays.* Let `1 + ∑ₛ pₛ z^(s w)` be the initial
  function of a polynomial input, with variables `p_s`, `p_t` for `s ≠ t`. The terms
  `p_s z^(s w)` and `p_t z^(t w)` have proportional exponents, but lie on different supported
  rays of the finite alphabet, those of the letters `v_s` and `v_t`
  (`TauCeti.PositiveDegrees.letterRay_injective`). The product `p_s p_t z^((s+t) w)` lies on a third
  ray, that of `v_s + v_t` (`TauCeti.PositiveDegrees.letterPairRay_ne_letterRay`). The logarithm of
  the initial function is `g - g²/2` modulo cubic terms, where `g = ∑ pₛ z^(s w)`. The
  coefficient of `p_s p_t` in `g²` is `2`, so the coefficient on this ray is `-2/2 = -1`. So the
  ray factor of the initial label on this ray has wall function `f_u` with `[u] f_u = -1`
  (`logComponent_initialLabel_letter_add_letter`,
  `logComponent_rayFactor_initialLabel_letterPairRay`). For the polynomial `1 + p₁ x + p₂ x²`
  of the rank-two datum, at the second index of
  `Mei.SkewLatticeDatum.Examples.rankTwoBLMPolynomialInput`, this is
  `Mei.SkewLatticeDatum.Examples.rankTwo_logComponent_rayFactor_letterPairRay`.

* *Specializing the variables.* On the rank-two datum, the alphabet input of
  `Mei.SkewLatticeDatum.Examples.rankTwoBLMPolynomialInput` on the lines `e₁⊥` and `e₂⊥` of `M`
  is lifted along the specialization `p_{i,s} ↦ 1`, written in the coordinates
  `m ↦ (m(e₂), -m(e₁))` of `M` in which `w₁ = e₂*` and `w₂ = -e₁*` are the standard basis of
  `ℤ²` (`rankTwoSpecialization`). The lift has the walls `1 + x` and `1 + y + y²` in the
  positive quadrant `ℕ²`, for `x = z^{(1, 0)}` and `y = z^{(0, 1)}` (`rankTwoSpecializedInput`).
  The letters of `p_{2,1}` and `p_{2,2}` lie on different rays of the alphabet, but their images
  `y` and `y²` lie on one ray (`rankTwoSpecializedInput_exponent_rankTwoLetter_one`). The
  pushforward of the scattering class of the alphabet walls is the scattering class of the
  lifted walls (`rankTwo_pushforward_scat_alphabetInput`), and over `ℚ` the lifted ray
  presentation is a positive wall representative
  (`rankTwoSpecializedInput_isPositiveWallRepresentative`).

* *The zero form.* On the rank-one lattice `ℤ` with the zero skew form and `N_uf = N° = ℤ`, the
  map `N_uf ∩ N° → M`, `n ↦ ω(-, n)` is not injective, so there is no polynomial input
  (`Mei.SkewLatticeDatum.Examples.isEmpty_zeroFormAdaptedBasis_blmPolynomialInput`), whereas the
  principal extension of the same adapted basis carries one, with a nonzero form
  (`Mei.SkewLatticeDatum.Examples.nonempty_blmPolynomialInput_principalBLMBasis`,
  `Mei.SkewLatticeDatum.Examples.principalBLMDatum_form_ne_zero`).

* *Positive representatives for the zero form of rank two.* On `ℤ²` with the zero form and both
  basis vectors unfrozen (`zeroFormPlaneBasis`), the principal BLM extension with any
  multiplicities `ℓ₀, ℓ₁` is a polynomial input whose form vanishes on its unfrozen sublattice
  (`zeroFormPlane_principalBLMDatum_form_eq_zero`). Its two incoming cylinder hyperplanes have
  non-proportional normals (`zeroFormPlane_alphabetNormal_not_proportional`), so they cross;
  nevertheless the incoming diagram is consistent, and over `ℚ` it represents its own outgoing
  scattering class with grouped wall functions `1 + ∑_{s=1}^{ℓᵢ} pᵢₛ z^{s wᵢ}` whose monomial
  coefficients are natural numbers (`zeroFormPlane_exists_isPositiveWallRepresentative`).

* *Positive representatives of type `A₂`.* On the unimodular plane `ℤ²` with `{e₀, e₁} = 1`, both
  indices unfrozen and multipliers and multiplicities one, the polynomial input with initial
  functions `1 + p₀ z^{e₁*}` and `1 + p₁ z^{-e₀*}` (`unimodularBLMPolynomialInput`) is of type
  `A₂` (`isTypeA₂_unimodularBLMPolynomialInput`). Its outgoing scattering class is the class of
  the pentagon diagram, with one outgoing wall labelled by `1 + p₀ p₁ z^{e₁* - e₀*}`
  (`scat_unimodularBLMPolynomialInput`), and over `ℚ` this representative has grouped wall
  functions with natural-number monomial coefficients
  (`unimodular_exists_isPositiveWallRepresentative`).

* *Positive representatives of type `A₂` with an isolated index.* On `ℤ³` with the form
  `{x, y} = x₀ y₁ - x₁ y₀`, all three basis vectors unfrozen (`isolatedBasis`), the principal BLM
  extension with multiplicities `ℓ = (1, 1, 2)` is a polynomial input whose form is degenerate
  on its unfrozen sublattice but does not vanish there. It is of type `A₂` at the indices of `e₀`
  and `e₁` with the isolated index of `e₂`, where the initial function has two variables
  (`isTypeA₂WithIsolated_isolatedExtension`, `isolatedExtension_multiplicity_thd`). Its outgoing
  scattering class is the class of the pentagon diagram of the type `A₂` part together with the
  isolated incoming walls (`scat_isolatedExtension`), and over `ℚ` this representative has
  grouped wall functions with natural-number monomial coefficients, among them
  `1 + p₂,₁ z^{w₂} + p₂,₂ z^{2 w₂}` at the isolated index
  (`isolatedExtension_exists_isPositiveWallRepresentative`).

The splitting of the initial function into rays follows Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1).
-/

public section

open TauCeti (PositiveDegrees)

noncomputable section

namespace Mei.SkewLatticeDatum.Examples

open AdaptedBasis

/-- The second unfrozen index of the rank-two adapted basis, whose initial function is
`1 + p_{2,1} z^{-e₁*} + p_{2,2} z^{-2e₁*}`, that is `1 + p₁ x + p₂ x²` for `x = z^{-e₁*}`. -/
def rankTwoSecondIndex : rankTwoAdaptedBasis.unfrozenIndex :=
  ⟨1, by simp⟩

/-- The variable `p_{2,s+1}` of the second initial function of the rank-two example. -/
def rankTwoLetter (s : Fin 2) : rankTwoBLMPolynomialInput.Letter :=
  ⟨rankTwoSecondIndex, ⟨s, by simpa [rankTwoSecondIndex, Nat.lt_succ_iff] using Fin.is_le s⟩⟩

/-- The exponent of the variable `p₁` of the initial function `1 + p₁ x + p₂ x²` is `-e₁*`, that
of `x = z^{-e₁*}`. -/
theorem rankTwoLetterExponent_zero :
    rankTwoBLMPolynomialInput.letterExponent (rankTwoLetter 0) = -LinearMap.fst ℤ ℤ ℤ := by
  simp [rankTwoLetter, rankTwoSecondIndex]

/-- The exponent of the variable `p₂` is `-2e₁*`, that of `x²`. -/
theorem rankTwoLetterExponent_one :
    rankTwoBLMPolynomialInput.letterExponent (rankTwoLetter 1) = -(2 • LinearMap.fst ℤ ℤ ℤ) := by
  simp [rankTwoLetter, rankTwoSecondIndex]

/-- The terms `p₁ x` and `p₂ x²`, whose exponents `-e₁*` and `-2e₁*` are proportional, lie on
different supported rays of the finite alphabet. -/
theorem rankTwoLetterRay_zero_ne_one :
    PositiveDegrees.letterRay rankTwoBLMPolynomialInput.letterExponent (rankTwoLetter 0) ≠
      PositiveDegrees.letterRay rankTwoBLMPolynomialInput.letterExponent (rankTwoLetter 1) :=
  fun h => by simpa [rankTwoLetter] using PositiveDegrees.letterRay_injective _ h

section RayFactor

variable {R : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq (Module.Dual ℤ (ℤ × ℤ))]

local notation "𝒥" => rankTwoBLMPolynomialInput
local notation "𝒅" => PositiveDegrees.finiteAlphabet rankTwoBLMPolynomialInput.letterExponent
local notation "ρ" =>
  AddMonoidHom.id (Module.Dual ℤ (ℤ × ℤ) × (rankTwoBLMPolynomialInput.Letter → ℤ))

/-- The logarithm of `1 + p₁ x + p₂ x²` has the coefficient `-1` on the ray of `u = p₁ p₂ x³`,
which differs from the rays of `p₁ x` and `p₂ x²`: the wall function `f_u` of the ray factor
satisfies `[u] f_u = -1`. -/
theorem rankTwo_logComponent_rayFactor_letterPairRay :
    (((𝒅).logComponent (tropicalVertexGrading (R := R) 𝒅 ρ)
      ((𝒅).rayFactor _ ((𝒥).initialLabel (R := R) rankTwoSecondIndex)
        (PositiveDegrees.letterPairRay (𝒥).letterExponent
          (α := rankTwoLetter 0) (β := rankTwoLetter 1) (by simp [rankTwoLetter])))
      (PositiveDegrees.letter (𝒥).letterExponent (rankTwoLetter 0) +
        PositiveDegrees.letter (𝒥).letterExponent (rankTwoLetter 1)) :
        tropicalVertexLieAlgebra (R := R) 𝒅 ρ) : LogarithmicVectorField R _ _ ρ) =
      LogarithmicVectorField.single ρ (PositiveDegrees.letter (𝒥).letterExponent (rankTwoLetter 0) +
        PositiveDegrees.letter (𝒥).letterExponent (rankTwoLetter 1))
        ((-1 : R) • AddMonoidHom.comp (Int.castAddHom R) ((𝒥).alphabetNormal rankTwoSecondIndex)) :=
  (𝒥).logComponent_rayFactor_initialLabel_letterPairRay rankTwoSecondIndex
    (s := ⟨0, by simp [rankTwoSecondIndex]⟩) (t := ⟨1, by simp [rankTwoSecondIndex]⟩) (by simp)

end RayFactor

section Specialization

open HyperplaneTermInput DirectedDiagram

local notation "𝒥" => rankTwoBLMPolynomialInput
local notation "ℕ²" => Module.Basis.positiveDegrees (Module.Basis.finTwoProd ℤ)

/-- The specialization `p_{i,s} ↦ 1` of the rank-two input, in the coordinates
`m ↦ (m(e₂), -m(e₁))` of `M = Hom(ℤ², ℤ)`, in which the exponents `w₁ = e₂*` and `w₂ = -e₁*` are
the standard basis vectors of `ℤ²`. -/
def rankTwoSpecialization : Module.Dual ℤ (ℤ × ℤ) × ((𝒥).Letter → ℤ) →+ ℤ × ℤ where
  toFun x := (x.1 (0, 1), -x.1 (1, 0))
  map_zero' := by simp
  map_add' x y := by ext <;> simp [add_comm]

@[simp]
theorem rankTwoSpecialization_apply (x : Module.Dual ℤ (ℤ × ℤ) × ((𝒥).Letter → ℤ)) :
    rankTwoSpecialization x = (x.1 (0, 1), -x.1 (1, 0)) :=
  (rfl)

/-- The character `a e₂* + b (-e₁*)` of a point `(a, b)` of `ℤ²`. -/
def rankTwoCharacter : ℤ × ℤ →+ Module.Dual ℤ (ℤ × ℤ) :=
  (zmultiplesHom _ (LinearMap.snd ℤ ℤ ℤ)).coprod (zmultiplesHom _ (-LinearMap.fst ℤ ℤ ℤ))

@[simp]
theorem rankTwoCharacter_apply (p : ℤ × ℤ) :
    rankTwoCharacter p = p.1 • LinearMap.snd ℤ ℤ ℤ + p.2 • -LinearMap.fst ℤ ℤ ℤ := by
  simp [rankTwoCharacter]

/-- The variable `p_{i,s}` specializes to `s` times the `i`-th basis vector of `ℤ²`, the
exponent `s w_i` in the coordinates of `rankTwoSpecialization`. -/
theorem rankTwoSpecialization_letter (α : (𝒥).Letter) :
    rankTwoSpecialization (PositiveDegrees.letter (𝒥).letterExponent α) =
      ((α.2 : ℕ) + 1) • Module.Basis.finTwoProd ℤ α.1.1 := by
  obtain ⟨⟨i, hi⟩, s⟩ := α
  fin_cases i <;> ext <;> simp [PositiveDegrees.letter_fst]

/-- The specialized variables are allowed degrees of the positive quadrant `ℕ²`. -/
theorem rankTwoSpecialization_letter_mem (α : (𝒥).Letter) :
    rankTwoSpecialization (PositiveDegrees.letter (𝒥).letterExponent α) ∈ (ℕ²).monoid := by
  rw [rankTwoSpecialization_letter]
  exact nsmul_mem (Module.Basis.mem_positiveDegrees_monoid_self _ _) _

/-- The specialized variables are nonzero. -/
theorem rankTwoSpecialization_letter_ne_zero (α : (𝒥).Letter) :
    rankTwoSpecialization (PositiveDegrees.letter (𝒥).letterExponent α) ≠ 0 := by
  rw [rankTwoSpecialization_letter]
  exact smul_ne_zero (Nat.succ_ne_zero _) ((Module.Basis.finTwoProd ℤ).ne_zero _)

/-- The character of the specialization of the variable `p_{i,s}` is its exponent `s w_i`. -/
theorem rankTwoCharacter_rankTwoSpecialization_letter (α : (𝒥).Letter) :
    rankTwoCharacter (rankTwoSpecialization (PositiveDegrees.letter (𝒥).letterExponent α)) =
      (𝒥).letterExponent α := by
  ext <;> simp [PositiveDegrees.letter_fst]

/-- The specialization `p_{i,s} ↦ 1` of the rank-two input: the lift of its alphabet input along
`rankTwoSpecialization`, with the walls `1 + x` on `e₁⊥` and `1 + y + y²` on `e₂⊥`, where
`x = z^{(1, 0)}` and `y = z^{(0, 1)}` in `ℕ²`. -/
def rankTwoSpecializedInput :
    HyperplaneTermInput ℕ² rankTwoCharacter rankTwoAdaptedBasis.unfrozenIndex (𝒥).Letter :=
  (𝒥).alphabetInput.liftFiniteAlphabet rankTwoSpecialization_letter_mem
    rankTwoSpecialization_letter_ne_zero rankTwoCharacter_rankTwoSpecialization_letter

/-- The variable `p_{i,s}` becomes the monomial of `s` times the `i`-th basis vector of `ℤ²`. -/
@[simp]
theorem rankTwoSpecializedInput_exponent (α : (𝒥).Letter) :
    rankTwoSpecializedInput.exponent α = ((α.2 : ℕ) + 1) • Module.Basis.finTwoProd ℤ α.1.1 := by
  simp only [rankTwoSpecializedInput, liftFiniteAlphabet_exponent,
    BLMPolynomialInput.alphabetInput_exponent]
  exact rankTwoSpecialization_letter α

/-- The terms `p₁ x` and `p₂ x²` of `1 + p₁ x + p₂ x²` lie on different supported rays of the
alphabet (`rankTwoLetterRay_zero_ne_one`), but their specializations `y` and `y²` lie on one
ray of `ℕ²`. -/
theorem rankTwoSpecializedInput_exponent_rankTwoLetter_one :
    rankTwoSpecializedInput.exponent (rankTwoLetter 1) =
      2 • rankTwoSpecializedInput.exponent (rankTwoLetter 0) := by
  simp [rankTwoLetter, rankTwoSecondIndex]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {j : Module.Dual ℤ (ℤ × ℤ) →+ V}
  (g : TauCeti.Toric.IsIntegralLattice j)

/-- The pushforward of the scattering class of the alphabet walls `1 + p_{1,1} z^{v_{1,1}}` and
`1 + p_{2,1} z^{v_{2,1}} + p_{2,2} z^{v_{2,2}}` along the specialization is the scattering class of
the walls `1 + x` and `1 + y + y²` in `ℕ²`. -/
theorem rankTwo_pushforward_scat_alphabetInput [DecidableEq (Module.Dual ℤ (ℤ × ℤ))] :
    Class.pushforward (DirectedWall.Pushforward.ofFiniteAlphabetLift (R := ℚ) (g := g)
        rankTwoSpecialization_letter_mem rankTwoSpecialization_letter_ne_zero
        rankTwoCharacter_rankTwoSpecialization_letter)
        (((𝒥).alphabetInput.diagram g fun _ => (1 : ℚ)).Scat
          (fun _ => ofHyperplaneRayFactors_full ..)) =
      (rankTwoSpecializedInput.diagram g fun _ => (1 : ℚ)).Scat
        (fun _ => ofHyperplaneRayFactors_full ..) :=
  (𝒥).alphabetInput.pushforward_scat_liftFiniteAlphabet _ _ _ g _

open scoped Mei.TropicalVertexCoefficientAction

/-- Every degree of `ℤ²` is a coefficient exponent. -/
local instance factPositiveDegreesLeTop : Fact ((ℕ²).monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) :=
  ⟨le_top⟩

/-- Over `ℚ` and for the full coefficient lattice `ℤ²`, the ray presentation of the walls `1 + x`
and `1 + y + y²` is a positive wall representative for the character map `rankTwoCharacter`: its
grouped wall functions have natural-number coefficients. -/
theorem rankTwoSpecializedInput_isPositiveWallRepresentative :
    (rankTwoSpecializedInput.diagram g fun _ => (1 : ℚ)).IsPositiveWallRepresentative
      ((TropicalVertexCoefficientAction.filtration (R := ℚ) ℕ²
        (⊤ : AddSubmonoid (ℤ × ℤ))).completedBCHAction ℕ²
        (tropicalVertexGrading (R := ℚ) ℕ² rankTwoCharacter))
      (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ)) (Nat.castRingHom ℚ)).rangeS
      rankTwoCharacter :=
  (𝒥).isPositiveWallRepresentative_liftFiniteAlphabet_alphabetInput _ _ _ g
    (⊤ : AddSubmonoid (ℤ × ℤ))
    (fun i => ⟨![(0, -1), (1, 0)] i.1, trivial, trivial, by
      obtain ⟨i, -⟩ := i
      fin_cases i <;> simp⟩) _

end Specialization

section ZeroForm

/-- The rank-one skew lattice datum on `ℤ` with the zero form, `N_uf = N° = ℤ`. -/
def zeroForm : SkewLatticeDatum ℤ where
  unfrozen := ⊤
  unfrozen_saturated _ _ _ := Or.inr Submodule.mem_top
  sublattice := ⊤
  finiteIndex_sublattice := by
    simpa only [Submodule.top_toAddSubgroup] using
      (inferInstance : (⊤ : AddSubgroup ℤ).FiniteIndex)
  form := 0
  isAlt_form _ := rfl
  integral_unfrozen_sublattice _ _ _ _ := ⟨0, rfl⟩
  integral_unfrozen_inf_sublattice _ _ _ := ⟨0, rfl⟩

@[simp]
theorem zeroForm_form : zeroForm.form = 0 :=
  (rfl)

/-- The basis `1` of `ℤ`, with its only index unfrozen and multiplier one, is an adapted basis
of the zero-form datum. -/
noncomputable def zeroFormAdaptedBasis : zeroForm.AdaptedBasis Unit where
  basis := Module.Basis.singleton Unit ℤ
  unfrozenIndex := Finset.univ
  multiplier _ := 1
  multiplier_pos _ := one_pos
  unfrozen_eq_span := by
    rw [Finset.coe_univ, Set.image_univ, Module.Basis.span_eq]
    -- the goal is `zeroForm.unfrozen = ⊤`, which is the definition of `zeroForm`
    rfl
  sublattice_eq_span := by
    simp only [one_smul, Module.Basis.span_eq]
    -- the goal is `zeroForm.sublattice = ⊤`, which is the definition of `zeroForm`
    rfl

@[simp]
theorem zeroFormAdaptedBasis_unfrozenIndex : zeroFormAdaptedBasis.unfrozenIndex = Finset.univ :=
  (rfl)

/-- With the zero form and an unfrozen index, the map `N_uf ∩ N° → M`, `n ↦ ω(-, n)` is not
injective, so the zero-form datum admits no polynomial input. -/
theorem isEmpty_zeroFormAdaptedBasis_blmPolynomialInput :
    IsEmpty zeroFormAdaptedBasis.BLMPolynomialInput :=
  BLMPolynomialInput.isEmpty_of_form_eq_zero zeroForm_form ⟨(), by simp⟩

/-- The principal extension of the zero-form adapted basis is nevertheless a polynomial input,
for any multiplicity. -/
theorem nonempty_blmPolynomialInput_principalBLMBasis
    (ℓ : zeroFormAdaptedBasis.unfrozenIndex → ℕ+) :
    Nonempty ((zeroFormAdaptedBasis.principalBLMBasis ℓ).BLMPolynomialInput) :=
  ⟨zeroFormAdaptedBasis.principalBLMExtension ℓ⟩

/-- Unlike the zero form, the form of the principal extension pairs the unfrozen basis vector
with its frozen companion by a positive number. -/
theorem principalBLMDatum_form_ne_zero (ℓ : zeroFormAdaptedBasis.unfrozenIndex → ℕ+) :
    (zeroFormAdaptedBasis.principalBLMDatum ℓ).form ≠ 0 := by
  intro h
  have := congrArg (fun f => f (Finsupp.single (.inl ()) 1)
    (Finsupp.single (.inr ⟨(), by simp⟩) 1)) h
  have hc := (zeroFormAdaptedBasis.principalBLMScale_pos ℓ).ne'
  have hd : zeroFormAdaptedBasis.multiplier () ≠ 0 := (zeroFormAdaptedBasis.multiplier_pos ()).ne'
  simp only [principalBLMDatum_form, LinearMap.zero_apply] at this
  rw [principalBLMForm_single_inl_single_inr] at this
  simp [hc, hd] at this

end ZeroForm

section ZeroFormPlane

/-- The rank-two skew lattice datum on `ℤ²` with the zero form and `N_uf = N° = ℤ²`. -/
def zeroFormPlane : SkewLatticeDatum (ℤ × ℤ) :=
  ofBasis (Module.Basis.finTwoProd ℤ) Finset.univ (fun _ => 1) 0 (fun _ => one_pos)
    (fun _ => by simp) (fun _ _ _ => ⟨0, by simp⟩) (fun _ _ _ => ⟨0, by simp⟩)

@[simp]
theorem zeroFormPlane_form : zeroFormPlane.form = 0 :=
  ofBasis_form

/-- The standard basis of `ℤ²`, with both indices unfrozen and multipliers one, as an adapted
basis of the zero-form plane. -/
def zeroFormPlaneBasis : zeroFormPlane.AdaptedBasis (Fin 2) :=
  AdaptedBasis.ofBasis _ _ _ _ _ _ _ _

@[simp]
theorem zeroFormPlaneBasis_unfrozenIndex : zeroFormPlaneBasis.unfrozenIndex = Finset.univ :=
  AdaptedBasis.ofBasis_unfrozenIndex

variable (ℓ : zeroFormPlaneBasis.unfrozenIndex → ℕ+)

/-- The principal BLM extension of the zero-form plane with multiplicities `ℓ`. -/
abbrev zeroFormPlaneInput : (zeroFormPlaneBasis.principalBLMBasis ℓ).BLMPolynomialInput :=
  zeroFormPlaneBasis.principalBLMExtension ℓ

/-- The unfrozen index of the extension coming from the basis vector `e_k` of `ℤ²`. -/
def zeroFormPlaneIndex (k : Fin 2) : (zeroFormPlaneBasis.principalBLMBasis ℓ).unfrozenIndex :=
  zeroFormPlaneBasis.principalBLMUnfrozenEquiv ℓ ⟨k, by simp⟩

/-- The incoming cylinder hyperplanes of the extension at the two unfrozen indices have
non-proportional normals: the normal at `e₀` takes the value `1` on the character `(a₀*, 0)`,
and the normal at `e₁` takes the value `0` there. -/
theorem zeroFormPlane_alphabetNormal_not_proportional {c e : ℤ} (hc : c ≠ 0) :
    c • (zeroFormPlaneInput ℓ).alphabetNormal (zeroFormPlaneIndex ℓ 0) ≠
      e • (zeroFormPlaneInput ℓ).alphabetNormal (zeroFormPlaneIndex ℓ 1) := by
  intro hce
  have h := DFunLike.congr_fun hce
    (((zeroFormPlaneBasis.principalBLMBasis ℓ).basis.coord (zeroFormPlaneIndex ℓ 0)), 0)
  simp [zeroFormPlaneIndex, hc] at h

/-- The form of the principal extension of the zero-form plane vanishes on its unfrozen
sublattice. -/
theorem zeroFormPlane_principalBLMDatum_form_eq_zero
    (n m : (zeroFormPlaneBasis.principalBLMDatum ℓ).unfrozen) :
    (zeroFormPlaneBasis.principalBLMDatum ℓ).form n m = 0 :=
  zeroFormPlaneBasis.principalBLMDatum_form_eq_zero_of_forall_form_eq_zero ℓ (by simp) n m

/-- The alphabet degrees of the extension are allowed exponents of its coefficient monoid. -/
instance zeroFormPlaneInput_coefficientMonoid_fact :
    Fact ((PositiveDegrees.finiteAlphabet (zeroFormPlaneInput ℓ).letterExponent).monoid ≤
      (zeroFormPlaneInput ℓ).coefficientMonoid) :=
  ⟨(zeroFormPlaneInput ℓ).positiveDegrees_le_coefficientMonoid⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DecidableEq (Module.Dual ℤ ((Fin 2 ⊕ zeroFormPlaneBasis.unfrozenIndex) →₀ ℤ))]
  {latticeMap : (Module.Dual ℤ ((Fin 2 ⊕ zeroFormPlaneBasis.unfrozenIndex) →₀ ℤ) ×
    ((zeroFormPlaneInput ℓ).Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming diagram of the principal extension of the zero-form plane is consistent,
although its two cylinder hyperplanes cross. -/
theorem zeroFormPlane_incomingDiagram_consistent :
    ((zeroFormPlaneInput ℓ).incomingDiagram (R := ℚ) h).Consistent :=
  (zeroFormPlaneInput ℓ).incomingDiagram_consistent_of_forall_form_eq_zero h
    (zeroFormPlane_principalBLMDatum_form_eq_zero ℓ)

open scoped Mei.TropicalVertexCoefficientAction in
/-- Over `ℚ`, the outgoing scattering class of the principal extension of the zero-form plane
has a representative whose grouped wall functions have natural-number monomial coefficients, for
the coefficient monoid with Laurent characters and nonnegative multiplicities of the variables:
the incoming diagram, with wall functions `1 + ∑_{s=1}^{ℓᵢ} pᵢₛ z^{s wᵢ}`. -/
theorem zeroFormPlane_exists_isPositiveWallRepresentative :
    ∃ (κ : Type) (E : DirectedDiagram
        (d := PositiveDegrees.finiteAlphabet (zeroFormPlaneInput ℓ).letterExponent) h
        (tropicalVertexWallSpaces (R := ℚ) _ (AddMonoidHom.id _)) κ),
      E.toClass = ((zeroFormPlaneInput ℓ).incomingDiagram (R := ℚ) h).Scat
          ((zeroFormPlaneInput ℓ).incomingDiagram_full h) ∧
        E.IsPositiveWallRepresentative
          ((TropicalVertexCoefficientAction.filtration (R := ℚ)
            (PositiveDegrees.finiteAlphabet (zeroFormPlaneInput ℓ).letterExponent)
            (zeroFormPlaneInput ℓ).coefficientMonoid).completedBCHAction _
              (tropicalVertexGrading (R := ℚ) _ (AddMonoidHom.id _)))
          (AddMonoidAlgebra.mapRingHom (zeroFormPlaneInput ℓ).coefficientMonoid
            (Nat.castRingHom ℚ)).rangeS
          (AddMonoidHom.fst _ _) :=
  (zeroFormPlaneInput ℓ).exists_isPositiveWallRepresentative_of_forall_form_eq_zero h
    (zeroFormPlaneInput ℓ).coefficientMonoid (zeroFormPlane_principalBLMDatum_form_eq_zero ℓ)
    (fun _ => by simp) _

end ZeroFormPlane

section TypeA₂

/-- The polynomial input of type `A₂` on the unimodular plane `ℤ²` with `{e₀, e₁} = 1`, both indices
unfrozen, multipliers and multiplicities one. Its exponents are `w₀ = {e₀, -} = e₁*` and
`w₁ = {e₁, -} = -e₀*`, so its initial functions are `1 + p₀ z^{e₁*}` and `1 + p₁ z^{-e₀*}`. -/
noncomputable def unimodularBLMPolynomialInput :
    unimodularRankTwoAdaptedBasis.BLMPolynomialInput where
  multiplicity _ := 1
  multiplicity_pos _ := one_pos
  exponent i := ![LinearMap.snd ℤ ℤ ℤ, -LinearMap.fst ℤ ℤ ℤ] i.1
  multiplicity_mul_exponent i a := by
    obtain ⟨i, -⟩ := i
    fin_cases i <;> simp
  isPrimitive_exponent i := by
    obtain ⟨i, -⟩ := i
    fin_cases i
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.applyₗ (0, 1), by simp⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.applyₗ (-1, 0), by simp⟩
  eq_one_of_dvd_multiplier k hk := by
    simpa using hk 0
  eq_zero_of_form_eq_zero v _ hv := by
    have h₁ := hv (1, 0)
    have h₂ := hv (0, 1)
    simp only [unimodularRankTwo_form, rankTwoForm_apply, Int.cast_eq_zero] at h₁ h₂
    ext <;> simp_all

/-- Both initial functions have a single variable. -/
@[simp]
theorem unimodularBLMPolynomialInput_multiplicity
    (i : unimodularRankTwoAdaptedBasis.unfrozenIndex) :
    unimodularBLMPolynomialInput.multiplicity i = 1 :=
  (rfl)

/-- The polynomial input on the unimodular plane is of type `A₂` at `e₀, e₁`:
`d₀ {e₀, e₁} = d₁ {e₀, e₁} = 1`. -/
theorem isTypeA₂_unimodularBLMPolynomialInput :
    unimodularBLMPolynomialInput.IsTypeA₂WithIsolated unimodularRankTwoFst
      unimodularRankTwoSnd where
  form_eq_zero i hi₁ hi₂ := by
    obtain ⟨i, hi⟩ := i
    fin_cases i
    exacts [absurd rfl hi₁, absurd rfl hi₂]
  multiplicity_fst := unimodularBLMPolynomialInput_multiplicity _
  multiplicity_snd := unimodularBLMPolynomialInput_multiplicity _
  multiplier_mul_form_fst := by simp
  multiplier_mul_form_snd := by simp

/-- The alphabet degrees of the input are allowed exponents of its coefficient monoid. -/
instance unimodularBLMPolynomialInput_coefficientMonoid_fact :
    Fact ((PositiveDegrees.finiteAlphabet unimodularBLMPolynomialInput.letterExponent).monoid ≤
      unimodularBLMPolynomialInput.coefficientMonoid) :=
  ⟨unimodularBLMPolynomialInput.positiveDegrees_le_coefficientMonoid⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DecidableEq (Module.Dual ℤ (ℤ × ℤ))]
  {latticeMap : (Module.Dual ℤ (ℤ × ℤ) × (unimodularBLMPolynomialInput.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The outgoing scattering class of the polynomial input of type `A₂` on the unimodular plane is
the class of its pentagon diagram: the incoming cylinders over `e₀⊥` and `e₁⊥` and the outgoing
half-hyperplane `{e₀ + e₁ = 0, e₀ ≥ 0}` labelled by the binomial label of `1 + z^{v₀ + v₁}`, that
is of `1 + p₀ p₁ z^{e₁* - e₀*}`. -/
theorem scat_unimodularBLMPolynomialInput :
    (unimodularBLMPolynomialInput.incomingDiagram (R := ℚ) h).Scat
        (unimodularBLMPolynomialInput.incomingDiagram_full h) =
      (isTypeA₂_unimodularBLMPolynomialInput.isTypeA₂Presentation h).pentagonDiagram.toClass :=
  (isTypeA₂_unimodularBLMPolynomialInput.isTypeA₂Presentation h).scat_eq_toClass_pentagonDiagram

open scoped Mei.TropicalVertexCoefficientAction in
/-- Over `ℚ`, the outgoing scattering class of the polynomial input of type `A₂` on the unimodular
plane has a consistent outgoing representative whose grouped wall functions `1 + p₀ z^{e₁*}`,
`1 + p₁ z^{-e₀*}` and `1 + p₀ p₁ z^{e₁* - e₀*}` have natural-number monomial coefficients, for the
coefficient monoid with Laurent characters and nonnegative multiplicities of the variables. -/
theorem unimodular_exists_isPositiveWallRepresentative :
    ∃ (κ : Type) (E : DirectedDiagram
        (d := PositiveDegrees.finiteAlphabet unimodularBLMPolynomialInput.letterExponent) h
        (tropicalVertexWallSpaces (R := ℚ) _ (AddMonoidHom.id _))
        (unimodularBLMPolynomialInput.IncomingIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion
          (unimodularBLMPolynomialInput.incomingDiagram (R := ℚ) h).wall E ∧
        E.toClass = (unimodularBLMPolynomialInput.incomingDiagram (R := ℚ) h).Scat
          (unimodularBLMPolynomialInput.incomingDiagram_full h) ∧
        E.IsPositiveWallRepresentative
          ((TropicalVertexCoefficientAction.filtration (R := ℚ)
            (PositiveDegrees.finiteAlphabet unimodularBLMPolynomialInput.letterExponent)
            unimodularBLMPolynomialInput.coefficientMonoid).completedBCHAction _
              (tropicalVertexGrading (R := ℚ) _ (AddMonoidHom.id _)))
          (AddMonoidAlgebra.mapRingHom unimodularBLMPolynomialInput.coefficientMonoid
            (Nat.castRingHom ℚ)).rangeS
          (AddMonoidHom.fst _ _) :=
  isTypeA₂_unimodularBLMPolynomialInput.exists_isPositiveWallRepresentative_scat h _
    (fun _ => by simp) _

end TypeA₂

section TypeA₂WithIsolated

/-- The multiplicities `ℓ = (1, 1, 2)` at the unfrozen indices of `isolatedBasis`. -/
def isolatedMultiplicity : isolatedBasis.unfrozenIndex → ℕ+ := fun i => ![1, 1, 2] i.1

/-- The principal BLM extension of `isolatedBasis` with multiplicities `ℓ = (1, 1, 2)`. -/
abbrev isolatedExtension :
    (isolatedBasis.principalBLMBasis isolatedMultiplicity).BLMPolynomialInput :=
  isolatedBasis.principalBLMExtension isolatedMultiplicity

/-- The initial function at the isolated index of the extension has two variables. -/
theorem isolatedExtension_multiplicity_thd :
    isolatedExtension.multiplicity
        (isolatedBasis.principalBLMUnfrozenEquiv isolatedMultiplicity isolatedThd) = 2 := by
  simp [isolatedMultiplicity]

/-- The principal BLM extension of `isolatedBasis` with multiplicities `ℓ = (1, 1, 2)` is of type
`A₂` at the indices of `e₀` and `e₁`, with the isolated index of `e₂`. -/
theorem isTypeA₂WithIsolated_isolatedExtension :
    isolatedExtension.IsTypeA₂WithIsolated
      (isolatedBasis.principalBLMUnfrozenEquiv isolatedMultiplicity isolatedFst)
      (isolatedBasis.principalBLMUnfrozenEquiv isolatedMultiplicity isolatedSnd) :=
  isolatedBasis.principalBLMExtension_isTypeA₂WithIsolated _ (by simp [isolatedMultiplicity])
    (by simp [isolatedMultiplicity])
    (by simp [isolatedBasis_multiplier])
    (by simp [isolatedBasis_multiplier])
    isTypeA₂WithIsolated_isolatedBasis.form_eq_zero

/-- The alphabet degrees of the extension are allowed exponents of its coefficient monoid. -/
instance isolatedExtension_coefficientMonoid_fact :
    Fact ((PositiveDegrees.finiteAlphabet isolatedExtension.letterExponent).monoid ≤
      isolatedExtension.coefficientMonoid) :=
  ⟨isolatedExtension.positiveDegrees_le_coefficientMonoid⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [DecidableEq (Module.Dual ℤ ((Fin 3 ⊕ isolatedBasis.unfrozenIndex) →₀ ℤ))]
  {latticeMap : (Module.Dual ℤ ((Fin 3 ⊕ isolatedBasis.unfrozenIndex) →₀ ℤ) ×
    (isolatedExtension.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The outgoing scattering class of the extension of `isolatedBasis` is the class of its
pentagon diagram: the incoming walls together with the outgoing half-hyperplane
`{a₀ + a₁ = 0, a₀ ≥ 0}` labelled by the binomial label of `1 + z^{v₀ + v₁}`. The wall at the
isolated index does not interact with it. -/
theorem scat_isolatedExtension :
    (isolatedExtension.incomingDiagram (R := ℚ) h).Scat (isolatedExtension.incomingDiagram_full h) =
      (isTypeA₂WithIsolated_isolatedExtension.isTypeA₂Presentation h).pentagonDiagram.toClass :=
  (isTypeA₂WithIsolated_isolatedExtension.isTypeA₂Presentation h).scat_eq_toClass_pentagonDiagram

open scoped Mei.TropicalVertexCoefficientAction in
/-- Over `ℚ`, the outgoing scattering class of the extension of `isolatedBasis` has a consistent
outgoing representative whose grouped wall functions have natural-number monomial coefficients,
for the coefficient monoid with Laurent characters and nonnegative multiplicities of the
variables: `1 + p₀ z^{w₀}`, `1 + p₁ z^{w₁}`, `1 + p₀ p₁ z^{w₀ + w₁}` and, at the isolated index,
`1 + p₂,₁ z^{w₂} + p₂,₂ z^{2 w₂}`. -/
theorem isolatedExtension_exists_isPositiveWallRepresentative :
    ∃ (κ : Type) (E : DirectedDiagram
        (d := PositiveDegrees.finiteAlphabet isolatedExtension.letterExponent) h
        (tropicalVertexWallSpaces (R := ℚ) _ (AddMonoidHom.id _))
        (isolatedExtension.IncomingIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion
          (isolatedExtension.incomingDiagram (R := ℚ) h).wall E ∧
        E.toClass = (isolatedExtension.incomingDiagram (R := ℚ) h).Scat
          (isolatedExtension.incomingDiagram_full h) ∧
        E.IsPositiveWallRepresentative
          ((TropicalVertexCoefficientAction.filtration (R := ℚ)
            (PositiveDegrees.finiteAlphabet isolatedExtension.letterExponent)
            isolatedExtension.coefficientMonoid).completedBCHAction _
              (tropicalVertexGrading (R := ℚ) _ (AddMonoidHom.id _)))
          (AddMonoidAlgebra.mapRingHom isolatedExtension.coefficientMonoid
            (Nat.castRingHom ℚ)).rangeS
          (AddMonoidHom.fst _ _) :=
  isTypeA₂WithIsolated_isolatedExtension.exists_isPositiveWallRepresentative_scat h _
    (fun _ => by simp) _

end TypeA₂WithIsolated

end Mei.SkewLatticeDatum.Examples
