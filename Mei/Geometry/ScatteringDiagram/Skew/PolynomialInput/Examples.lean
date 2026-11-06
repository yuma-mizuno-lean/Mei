/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Examples
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Commuting
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon

/-!
# Checks on polynomial inputs of generalized cluster scattering diagrams

Two checks on `BLMPolynomialInput`, and instances of the positive representatives of
`Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Commuting` and
`Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Pentagon`.

* *Terms of one initial polynomial on different rays.* Let `1 + ∑ₛ pₛ z^(s w)` be the initial
  function of a polynomial input, with variables `p_s`, `p_t` for `s ≠ t`. The terms
  `p_s z^(s w)` and `p_t z^(t w)` have proportional exponents, but lie on different supported
  rays of the finite alphabet, those of the letters `v_s` and `v_t`
  (`Mei.PositiveDegrees.letterRay_injective`). The product `p_s p_t z^((s+t) w)` lies on a third
  ray, that of `v_s + v_t` (`Mei.PositiveDegrees.letterPairRay_ne_letterRay`). The logarithm of
  the initial function is `g - g²/2` modulo cubic terms, where `g = ∑ pₛ z^(s w)`. The
  coefficient of `p_s p_t` in `g²` is `2`, so the coefficient on this ray is `-2/2 = -1`. So the
  ray factor of the initial label on this ray has wall function `f_u` with `[u] f_u = -1`
  (`logComponent_initialLabel_letter_add_letter`,
  `logComponent_rayFactor_initialLabel_letterPairRay`). For the polynomial `1 + p₁ x + p₂ x²`
  of the rank-two datum, at the second index of
  `Mei.SkewLatticeDatum.Examples.rankTwoBLMPolynomialInput`, this is
  `Mei.SkewLatticeDatum.Examples.rankTwo_logComponent_rayFactor_letterPairRay`.

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

The splitting of the initial function into rays follows Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1).
-/

public section

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
    unimodularBLMPolynomialInput.IsTypeA₂ unimodularRankTwoFst unimodularRankTwoSnd where
  eq_or_eq i := by
    obtain ⟨i, hi⟩ := i
    fin_cases i
    exacts [Or.inl rfl, Or.inr rfl]
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

end Mei.SkewLatticeDatum.Examples
