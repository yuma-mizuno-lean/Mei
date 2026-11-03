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

end Mei.SkewLatticeDatum.Examples
