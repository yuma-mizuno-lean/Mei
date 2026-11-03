/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.Examples
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Extension.Basic
public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming

/-!
# Checks on polynomial inputs of generalized cluster scattering diagrams

Two checks on `BLMPolynomialInput`.

* *Terms of one initial polynomial on different rays.* Let `1 + ∑ₛ pₛ z^(s w)` be the initial
  function of a polynomial input, with variables `p_s`, `p_t` for `s ≠ t`. The terms
  `p_s z^(s w)` and `p_t z^(t w)` have proportional exponents, but lie on different supported
  rays of the finite alphabet, those of the letters `v_s` and `v_t`
  (`Mei.PositiveDegrees.letterRay_injective`). The product `p_s p_t z^((s+t) w)` lies on a third
  ray, that of `v_s + v_t` (`Mei.PositiveDegrees.letterPairRay_ne_letterRay`). The logarithm of
  the initial function has coefficient `-1` there, minus the coefficient of `p_s p_t` in the
  square of `∑ pₛ z^(s w)` divided by two. So the ray factor of the initial label on this ray
  has wall function `f_u` with `[u] f_u = -1`
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

The splitting of the initial function into rays follows Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra

variable {N ι R : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput) [DecidableEq ι] [CommRing R] [Algebra ℚ R]

local notation "Γ" => Module.Dual ℤ N × (I.Letter → ℤ)
local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id Γ
local notation "χ" i => AddMonoidHom.comp (Int.castAddHom R) (I.alphabetNormal i)
local notation "T" i => tropicalTangentMonoid 𝒅 ρ (χ i)
local notation "F" i => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 (T i)
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ

section Pair

variable (i : B.unfrozenIndex)

/-- The sum of the monomials of the variables of the initial polynomial at `i`, that is, the
initial polynomial minus one, in the tangent coefficient algebra. -/
private abbrev variableSum : R[T i] :=
  ∑ r : Fin (I.multiplicity i), single (I.tangentLetter i r) 1

/-- Modulo the third filtration ideal, the logarithm of the initial polynomial is `g - g² / 2`,
where `g` is the sum of its variable monomials. -/
private theorem projection_two_completedLog :
    (F i).projection 2 ((F i).completedLog
      ⟨(F i).toCompletion (I.tangentInitialFunction i),
        I.toCompletion_tangentInitialFunction_sub_one_mem i⟩) =
      Ideal.Quotient.mk _
        (variableSum (R := R) I i + (-1 / 2 : ℚ) • variableSum (R := R) I i ^ 2) := by
  have hn : ((F i).projection 2 ((F i).toCompletion (I.tangentInitialFunction i)) - 1) ^ 3 = 0 := by
    rw [AlgFiltration.projection_toCompletion, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    have := (F i).pow_mem (I.tangentInitialFunction_sub_one_mem (R := R) i) 3
    exact (F i).antitone (by norm_num) this
  rw [AlgFiltration.projection_completedLog, IsNilpotent.log_eq_sum hn]
  simp [Finset.sum_range_succ, AlgFiltration.projection_toCompletion,
    tangentInitialFunction_def, map_add, map_sum, map_rat_smul, map_pow]
  norm_num

omit [Algebra ℚ R] in
/-- Two sums of two tangent letters of one initial polynomial agree exactly when they consist of
the same letters. -/
private theorem tangentLetter_add_tangentLetter_eq_iff {r r' s t : Fin (I.multiplicity i)} :
    I.tangentLetter (R := R) i r + I.tangentLetter i r' =
        I.tangentLetter i s + I.tangentLetter i t ↔
      (r = s ∧ r' = t) ∨ (r = t ∧ r' = s) := by
  rw [Subtype.ext_iff]
  simp [PositiveDegrees.letter_add_letter_eq_iff]

omit [Algebra ℚ R] in
/-- The alphabet degree of a tangent letter is one. -/
private theorem degree_tangentLetter (r : Fin (I.multiplicity i)) :
    (𝒅).degree (I.tangentLetter (R := R) i r : Γ) = 1 := by
  rw [coe_tangentLetter, PositiveDegrees.finiteAlphabet_degree_letter]

omit [Algebra ℚ R] in
/-- The alphabet degree of a sum of two tangent letters is two. -/
private theorem degree_tangentLetter_add (s t : Fin (I.multiplicity i)) :
    (𝒅).degree ((I.tangentLetter (R := R) i s + I.tangentLetter i t : T i) : Γ) = 2 := by
  rw [AddSubmonoid.coe_add, coe_tangentLetter, coe_tangentLetter,
    PositiveDegrees.finiteAlphabet_degree_letter_add_letter]

omit [Algebra ℚ R] in
/-- A tangent letter is not a sum of two tangent letters, since their alphabet degrees are
one and two. -/
private theorem tangentLetter_ne_add (r s t : Fin (I.multiplicity i)) :
    I.tangentLetter (R := R) i r ≠ I.tangentLetter i s + I.tangentLetter i t := by
  intro h
  have := congrArg (fun q : T i => (𝒅).degree (q : Γ)) h
  simp only [degree_tangentLetter, degree_tangentLetter_add] at this
  omega

/-- The coefficient of the tangent degree `v_s + v_t` in the order-two logarithm of the initial
polynomial is `-1` for distinct letters `s ≠ t`: it is minus the coefficient of the monomial
`p_s p_t` in `g² / 2`. -/
private theorem coeff_logTwo_letter_add_letter {s t : Fin (I.multiplicity i)} (hst : s ≠ t) :
    (variableSum (R := R) I i + (-1 / 2 : ℚ) • variableSum (R := R) I i ^ 2).coeff
      (I.tangentLetter i s + I.tangentLetter i t) = (-1 : R) := by
  classical
  have hsq : variableSum (R := R) I i ^ 2 = ∑ r, ∑ r',
      single (I.tangentLetter (R := R) i r + I.tangentLetter i r') (1 : R) := by
    simp [sq, variableSum, Finset.sum_mul_sum, single_mul_single]
  have h1 : (variableSum (R := R) I i).coeff (I.tangentLetter i s + I.tangentLetter i t) = 0 := by
    rw [variableSum, coeff_sum, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun r _ => by
      rw [coeff_single, Finsupp.single_apply]
      simp [I.tangentLetter_ne_add i r s t]
  have h2 : (variableSum (R := R) I i ^ 2).coeff
      (I.tangentLetter i s + I.tangentLetter i t) = 2 := by
    rw [hsq]
    simp only [coeff_sum, coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply,
      tangentLetter_add_tangentLetter_eq_iff]
    rw [← Finset.sum_product' (f := fun r r' =>
      if r = s ∧ r' = t ∨ r = t ∧ r' = s then (1 : R) else 0), Finset.sum_boole]
    have : ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin (I.multiplicity i) × Fin _ =>
        p.1 = s ∧ p.2 = t ∨ p.1 = t ∧ p.2 = s) = {(s, t), (t, s)} := by
      ext ⟨a, b⟩
      simp
    rw [this, Finset.card_pair (by simp [hst])]
    norm_num
  rw [coeff_add, Finsupp.add_apply, coeff_smul, Finsupp.smul_apply, h1, h2, zero_add]
  rw [show (2 : R) = (2 : ℚ) • (1 : R) by rw [Algebra.smul_def, map_ofNat, mul_one], smul_smul]
  norm_num

variable [DecidableEq (Module.Dual ℤ N)]

/-- The logarithm of the initial label at `i` has the coefficient `-1` in the degree
`v_s + v_t` of the monomial `p_s p_t`, for distinct variables `p_s`, `p_t` of the initial
polynomial: the logarithmic vector field `-z^(v_s + v_t) ∂_n` with the cylinder normal `n`. -/
theorem logComponent_initialLabel_letter_add_letter {s t : Fin (I.multiplicity i)}
    (hst : s ≠ t) :
    (((𝒅).logComponent ℒ (I.initialLabel (R := R) i)
        (PositiveDegrees.letter I.letterExponent ⟨i, s⟩ +
          PositiveDegrees.letter I.letterExponent ⟨i, t⟩) :
        tropicalVertexLieAlgebra (R := R) 𝒅 ρ) : LogarithmicVectorField R Γ Γ ρ) =
      LogarithmicVectorField.single ρ (PositiveDegrees.letter I.letterExponent ⟨i, s⟩ +
        PositiveDegrees.letter I.letterExponent ⟨i, t⟩) ((-1 : R) • χ i) := by
  have hu : PositiveDegrees.letter I.letterExponent ⟨i, s⟩ +
      PositiveDegrees.letter I.letterExponent ⟨i, t⟩ =
        ((I.tangentLetter (R := R) i s + I.tangentLetter i t : T i) : Γ) := by simp
  rw [hu]
  have hdeg : (𝒅).degree ((I.tangentLetter (R := R) i s + I.tangentLetter i t : T i) : Γ) ≤
      ((2 : ℕ) : ℤ) := (I.degree_tangentLetter_add i s t).le
  have hne : ((I.tangentLetter (R := R) i s + I.tangentLetter i t : T i) : Γ) ≠ 0 :=
    fun h => by
      have := congrArg (𝒅).degree h
      rw [I.degree_tangentLetter_add i s t, map_zero] at this
      omega
  rw [initialLabel_def,
    logComponent_completedBCHExp_completedTropicalTangentField_eq_decompose 𝒅 ρ
      (I.alphabetNormal i) _ (I.projection_two_completedLog i) hdeg,
    decompose_tropicalTangentField_apply 𝒅 ρ (I.alphabetNormal i),
    I.coeff_logTwo_letter_add_letter i hst, coe_tropicalTangentField_single _ _ _ hne]

/-- The ray factor of the initial label on the ray of `v_s + v_t` has the same logarithmic
coefficient `-1` there: its wall function `f_u` has `[u] f_u = -1`, for the primitive generator
`u = v_s + v_t` of its ray. -/
theorem logComponent_rayFactor_initialLabel_letterPairRay {s t : Fin (I.multiplicity i)}
    (hst : s ≠ t) :
    (((𝒅).logComponent ℒ ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i)
        (PositiveDegrees.letterPairRay I.letterExponent
          (α := ⟨i, s⟩) (β := ⟨i, t⟩) (by simpa using hst)))
        (PositiveDegrees.letter I.letterExponent ⟨i, s⟩ +
          PositiveDegrees.letter I.letterExponent ⟨i, t⟩) :
        tropicalVertexLieAlgebra (R := R) 𝒅 ρ) : LogarithmicVectorField R Γ Γ ρ) =
      LogarithmicVectorField.single ρ (PositiveDegrees.letter I.letterExponent ⟨i, s⟩ +
        PositiveDegrees.letter I.letterExponent ⟨i, t⟩) ((-1 : R) • χ i) := by
  have hαβ : (⟨i, s⟩ : I.Letter) ≠ ⟨i, t⟩ := by simpa using hst
  have hmem : PositiveDegrees.letter I.letterExponent ⟨i, s⟩ +
      PositiveDegrees.letter I.letterExponent ⟨i, t⟩ ∈
        (PositiveDegrees.letterPairRay I.letterExponent hαβ).rayDegrees := by
    simpa using (SupportedRay.generator_mem_rayDegrees_iff
      (PositiveDegrees.letterPairRay I.letterExponent hαβ)).mpr (by
        simpa using add_mem (PositiveDegrees.letter_mem I.letterExponent ⟨i, s⟩)
          (PositiveDegrees.letter_mem I.letterExponent ⟨i, t⟩))
  rw [PositiveDegrees.logComponent_rayFactor_of_mem 𝒅 ℒ _ hmem]
  exact I.logComponent_initialLabel_letter_add_letter i hst

end Pair

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

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
    rfl
  sublattice_eq_span := by
    simp only [one_smul, Module.Basis.span_eq]
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
  simp at this
  exact this.elim hc hd

end ZeroForm

end Mei.SkewLatticeDatum.Examples
