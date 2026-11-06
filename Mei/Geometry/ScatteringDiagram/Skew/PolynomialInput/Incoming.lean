/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.RayFactor
public import Mei.RingTheory.FilteredAlgebra.Positive.Basic
public import Mei.Algebra.Lie.Logarithmic.WallFunction.Binomial

/-!
# Incoming diagrams of BLM polynomial inputs

The polynomial `1 + ∑ₛ pᵢₛ z^(s wᵢ)` generally has logarithmic terms on
several supported rays of the finite alphabet lattice. We realize its logarithm
as a completed tangent field, split its exponential into ray labels, and place
the tangent ray labels on the full cylinder over `eᵢ⊥`. These infinitely indexed
walls have finite activity at every cutoff and are all incoming. Their products
recover the original label at each finite order, whose coefficient action is
the prescribed polynomial function raised to the normal pairing.

The constructions use `PositiveDegrees.rayFactor`, its wall-group and finite
support theorems, the ray-factor theorems for tangent polynomials of
`Mei.Geometry.ScatteringDiagram.WallSpace.Logarithmic.RayFactor`, shared with the
rank-two polynomial inputs, and the ray presentation
`DirectedDiagram.ofHyperplaneRayFactors` on hyperplanes. The polynomial inputs
and their ray presentations follow Burcroff–Lee–Mou, *Positivity of generalized
cluster scattering diagrams*, §8.1 and §9.2 (arXiv:2503.03719v1), and the
function-wall convention of Gross–Hacking–Keel–Kontsevich, *Canonical bases for
cluster algebras*, §1.1 (arXiv:1411.1394v2).
-/

public noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra

variable {N ι R V : Type*} [AddCommGroup N]
  {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι} (I : B.BLMPolynomialInput)

variable [DecidableEq ι]

local notation "Γ" => Module.Dual ℤ N × (I.Letter → ℤ)
local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id Γ

/-- The primitive cylinder normal: evaluate the spatial character on `eᵢ`,
ignoring the coefficient-variable coordinates. -/
def alphabetNormal (i : B.unfrozenIndex) : Γ →+ ℤ where
  toFun q := q.1 (B.basis i)
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq ι] in
@[simp]
theorem alphabetNormal_apply (i : B.unfrozenIndex) (q : Γ) :
    I.alphabetNormal i q = q.1 (B.basis i) := (rfl)

omit [DecidableEq ι] in
/-- Evaluation on a basis vector is a nonzero integral normal. -/
theorem alphabetNormal_ne_zero (i : B.unfrozenIndex) : I.alphabetNormal i ≠ 0 := by
  intro he
  have h := DFunLike.congr_fun he (B.basis.coord i, 0)
  simp at h

omit [DecidableEq ι] in
/-- The cylinder normal is primitive: it takes the value one on the character
`(eᵢ*, 0)`, and evaluation at that character is an integral functional on normals. -/
theorem isPrimitive_alphabetNormal (i : B.unfrozenIndex) :
    TauCeti.IsPrimitive (I.alphabetNormal i) :=
  TauCeti.isPrimitive_def.mpr ⟨AddMonoidHom.toIntLinearMap
    (AddMonoidHom.eval (B.basis.coord i, 0)), by simp⟩

/-- The letter `v_{i,s}` of a variable of the initial function at `i` is tangent to the cylinder
over `eᵢ⊥`. -/
theorem alphabetNormal_letter_self (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) :
    I.alphabetNormal i (PositiveDegrees.letter I.letterExponent ⟨i, s⟩) = 0 := by
  simp

variable [CommRing R]

local notation "χ" i => AddMonoidHom.comp (Int.castAddHom R) (I.alphabetNormal i)
local notation "T" i => tropicalTangentMonoid 𝒅 ρ (χ i)
local notation "F" i => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 (T i)
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ
local notation "H" => tropicalVertexWallSpaces (R := R) 𝒅 ρ

/-- A variable monomial, regarded as a tangent degree of its initial wall. -/
private def tangentLetter (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) : T i :=
  ⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
    (mem_tropicalTangentMonoid _ _ _ _).mpr
      ⟨PositiveDegrees.letter_mem _ _, by simp⟩⟩

@[simp]
private theorem coe_tangentLetter (i : B.unfrozenIndex) (s : Fin (I.multiplicity i)) :
    (I.tangentLetter (R := R) i s : Γ) =
      PositiveDegrees.letter I.letterExponent ⟨i, s⟩ := (rfl)

/-- The initial polynomial in its tangent coefficient algebra. Its inclusion
in the ambient alphabet algebra is `initialFunction`. -/
def tangentInitialFunction (i : B.unfrozenIndex) : R[T i] :=
  1 + ∑ s : Fin (I.multiplicity i), single (I.tangentLetter i s) 1

/-- Forgetting the tangent subtype recovers the original polynomial, including
all independent coefficient letters. -/
@[simp]
theorem mapDomain_tangentInitialFunction (i : B.unfrozenIndex) :
    mapDomain (fun q : T i => q.val) (I.tangentInitialFunction (R := R) i) =
      I.initialFunction R i := by
  have he : mapDomainRingHom R (T i).subtype (I.tangentInitialFunction (R := R) i) =
      I.initialFunction R i := by
    simp only [tangentInitialFunction, initialFunction_def, map_add, map_one, map_sum,
      mapDomainRingHom_apply, mapDomain_single, AddSubmonoid.subtype_apply, coe_tangentLetter]
  simpa only [mapDomainRingHom_apply, AddSubmonoid.coe_subtype] using he

/-- The initial polynomial is one modulo the first tangent filtration ideal. -/
theorem tangentInitialFunction_sub_one_mem (i : B.unfrozenIndex) :
    I.tangentInitialFunction (R := R) i - 1 ∈ (F i).ideal 1 := by
  rw [tangentInitialFunction, add_sub_cancel_left]
  exact sum_single_mem_filtration_ideal_one 𝒅 ρ (I.alphabetNormal i) _ _ fun s => by
    simpa only [coe_tangentLetter] using PositiveDegrees.letter_ne_zero _ _

/-- The completed initial polynomial is congruent to one. -/
theorem toCompletion_tangentInitialFunction_sub_one_mem (i : B.unfrozenIndex) :
    (F i).toCompletion (I.tangentInitialFunction (R := R) i) - 1 ∈
      (F i).completionIdeal 1 := by
  rw [← map_one (F i).toCompletion, ← map_sub,
    AlgFiltration.toCompletion_mem_completionIdeal_iff]
  exact I.tangentInitialFunction_sub_one_mem i

variable [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R]

/-- The unsplit function-wall label `exp(log(fᵢ) ∂_(eᵢ))` in the completed
tropical vertex group of the finite alphabet. -/
def initialLabel (i : B.unfrozenIndex) : (𝒅).completedBCHGroup ℒ :=
  (𝒅).completedBCHExp ℒ (completedTropicalTangentField 𝒅 ρ (χ i)
    ((F i).completedLog ⟨(F i).toCompletion (I.tangentInitialFunction i),
      I.toCompletion_tangentInitialFunction_sub_one_mem i⟩))

/-- The defining logarithmic tangent field of the combined initial label. -/
theorem initialLabel_def (i : B.unfrozenIndex) :
    I.initialLabel (R := R) i =
      (𝒅).completedBCHExp ℒ (completedTropicalTangentField 𝒅 ρ (χ i)
        ((F i).completedLog ⟨(F i).toCompletion (I.tangentInitialFunction i),
          I.toCompletion_tangentInitialFunction_sub_one_mem i⟩)) := (rfl)

/-- If the initial function at `i` has a single variable (`ℓᵢ = 1`), so that it is the binomial
`1 + p_{i,1} z^{wᵢ}`, its unsplit label is the binomial label `exp(log(1 + z^v) ∂_{eᵢ})` of the
letter `v = v_{i,1}`, with coefficient one. -/
theorem initialLabel_eq_binomialLabel {i : B.unfrozenIndex} (hi : I.multiplicity i = 1)
    (s : Fin (I.multiplicity i)) :
    I.initialLabel (R := R) i = binomialLabel 𝒅 ρ (I.alphabetNormal i)
      (PositiveDegrees.letter_mem I.letterExponent ⟨i, s⟩)
      (PositiveDegrees.letter_ne_zero I.letterExponent ⟨i, s⟩)
      (I.alphabetNormal_letter_self i s) 1 := by
  have hf : I.tangentInitialFunction (R := R) i = 1 + single (binomialExponent 𝒅 ρ
      (I.alphabetNormal i) (PositiveDegrees.letter_mem I.letterExponent ⟨i, s⟩)
      (I.alphabetNormal_letter_self i s)) 1 := by
    rw [tangentInitialFunction, Fintype.sum_eq_single s fun t ht =>
      absurd (Fin.ext (by have := t.isLt; have := s.isLt; omega)) ht]
    exact congrArg (fun q => 1 + single q 1)
      (Subtype.ext ((I.coe_tangentLetter i s).trans (coe_binomialExponent ..).symm))
  simp only [initialLabel_def, binomialLabel_def, hf]

section Pair

variable (i : B.unfrozenIndex)

/-- The sum of the monomials of the variables of the initial polynomial at `i`, that is, the
initial polynomial minus one, in the tangent coefficient algebra. -/
private abbrev variableSum : R[T i] :=
  ∑ r : Fin (I.multiplicity i), single (I.tangentLetter i r) 1

omit [DecidableEq (Module.Dual ℤ N)] in
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
    tangentInitialFunction, map_add, map_sum, map_rat_smul, map_pow]
  norm_num

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- Two sums of two tangent letters of one initial polynomial agree exactly when they consist of
the same letters. -/
private theorem tangentLetter_add_tangentLetter_eq_iff {r r' s t : Fin (I.multiplicity i)} :
    I.tangentLetter (R := R) i r + I.tangentLetter i r' =
        I.tangentLetter i s + I.tangentLetter i t ↔
      (r = s ∧ r' = t) ∨ (r = t ∧ r' = s) := by
  rw [Subtype.ext_iff]
  simp [PositiveDegrees.letter_add_letter_eq_iff]

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- The alphabet degree of a tangent letter is one. -/
private theorem degree_tangentLetter (r : Fin (I.multiplicity i)) :
    (𝒅).degree (I.tangentLetter (R := R) i r : Γ) = 1 := by
  rw [coe_tangentLetter, PositiveDegrees.finiteAlphabet_degree_letter]

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- The alphabet degree of a sum of two tangent letters is two. -/
private theorem degree_tangentLetter_add (s t : Fin (I.multiplicity i)) :
    (𝒅).degree ((I.tangentLetter (R := R) i s + I.tangentLetter i t : T i) : Γ) = 2 := by
  rw [AddSubmonoid.coe_add, coe_tangentLetter, coe_tangentLetter,
    PositiveDegrees.finiteAlphabet_degree_letter_add_letter]

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- A tangent letter is not a sum of two tangent letters, since their alphabet degrees are
one and two. -/
private theorem tangentLetter_ne_add (r s t : Fin (I.multiplicity i)) :
    I.tangentLetter (R := R) i r ≠ I.tangentLetter i s + I.tangentLetter i t := by
  intro h
  have := congrArg (fun q : T i => (𝒅).degree (q : Γ)) h
  simp only [degree_tangentLetter, degree_tangentLetter_add] at this
  omega

omit [DecidableEq (Module.Dual ℤ N)] in
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
  rw [PositiveDegrees.logComponent_rayFactor_of_mem 𝒅 ℒ _
    (PositiveDegrees.letter_add_letter_mem_rayDegrees_letterPairRay _ hαβ)]
  exact I.logComponent_initialLabel_letter_add_letter i hst

end Pair

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)))
  [Fact ((PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 Q

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- In any coefficient monoid containing the positive degrees, the tangent
polynomial becomes the same finite sum of its independent variable monomials. -/
theorem tropicalTangentInclusion_tangentInitialFunction (i : B.unfrozenIndex) :
    tropicalTangentInclusion 𝒅 ρ (χ i) Q Fact.out (I.tangentInitialFunction i) =
      1 + ∑ s : Fin (I.multiplicity i),
        single (⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
          (Fact.out : (PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)
            (PositiveDegrees.letter_mem _ _)⟩ : Q) 1 := by
  simp only [tangentInitialFunction, map_add, map_one, map_sum,
    tropicalTangentInclusion_single, coe_tangentLetter]

/-- The initial polynomial `1 + ∑ₛ z^(letter (i, s))` as a unit of the completed
coefficient algebra. -/
def completedInitialFunction (i : B.unfrozenIndex) : (G).completionˣ :=
  (isUnit_completedTropicalTangentInclusion 𝒅 ρ (χ i) Q
    (I.toCompletion_tangentInitialFunction_sub_one_mem i)).unit

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- The initial function is the image of the initial polynomial. -/
@[simp]
theorem coe_completedInitialFunction (i : B.unfrozenIndex) :
    (I.completedInitialFunction (R := R) Q i : (G).completion) = (G).toCompletion
      (1 + ∑ s : Fin (I.multiplicity i),
        single (⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
          (Fact.out : (PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)
            (PositiveDegrees.letter_mem _ _)⟩ : Q) 1) := by
  rw [completedInitialFunction, IsUnit.unit_spec, completedTropicalTangentInclusion_toCompletion,
    I.tropicalTangentInclusion_tangentInitialFunction Q i]

omit [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R] in
/-- The initial functions have natural-number coefficients, hence are positive for the
image of `S[Q]` under any coefficient map. -/
theorem isPositive_completedInitialFunction {S : Type*} [Semiring S] (φ : S →+* R)
    (i : B.unfrozenIndex) :
    (G).IsPositive (AddMonoidAlgebra.mapRingHom Q φ).rangeS
      (I.completedInitialFunction Q i).val := by
  rw [I.coe_completedInitialFunction Q i]
  refine AlgFiltration.isPositive_toCompletion ⟨1 + ∑ s : Fin (I.multiplicity i),
    single (⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
      (Fact.out : (PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)
        (PositiveDegrees.letter_mem _ _)⟩ : Q) 1, ?_⟩
  simp only [map_add, map_one, map_sum, mapRingHom_single]

/-- The combined initial label acts by the original polynomial raised to the
integral cylinder-normal pairing. Negative pairings use inverse unit powers. -/
theorem completedBCHAction_initialLabel (i : B.unfrozenIndex)
    (f : (G).completionˣ)
    (hf : (f : (G).completion) = (G).toCompletion
      (1 + ∑ s : Fin (I.multiplicity i),
        single (⟨PositiveDegrees.letter I.letterExponent ⟨i, s⟩,
          (Fact.out : (PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)
            (PositiveDegrees.letter_mem _ _)⟩ : Q) 1))
    (p : Q) (c : R) :
    (G).completedBCHAction 𝒅 ℒ (I.initialLabel i) ((G).toCompletion (single p c)) =
      (f ^ I.alphabetNormal i p.val : (G).completionˣ) *
        (G).toCompletion (single p c) := by
  have he := completedBCHAction_completedBCHExp_completedTropicalTangentField_completedLog
    𝒅 ρ Q (I.alphabetNormal i) (I.toCompletion_tangentInitialFunction_sub_one_mem i) p c
  rw [← initialLabel] at he
  have hf' : (isUnit_completedTropicalTangentInclusion 𝒅 ρ (χ i) Q
      (I.toCompletion_tangentInitialFunction_sub_one_mem i)).unit = f := by
    apply Units.ext
    rw [IsUnit.unit_spec, completedTropicalTangentInclusion_toCompletion,
      I.tropicalTangentInclusion_tangentInitialFunction Q i, hf]
  simpa only [AddMonoidHom.id_apply, hf'] using he

end Action

/-- Each ray factor is an actual wall-group label, even when the ray generator
does not belong to the positive monoid. -/
@[simp high]
theorem rayFactor_initialLabel_mem_wallGroup (i : B.unfrozenIndex) (w : SupportedRay 𝒅) :
    (𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w ∈ (H).wallGroup w (I.alphabetNormal i) :=
  rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ _

/-- Nontangent rays have identity labels and can be omitted from the diagram. -/
@[simp]
theorem rayFactor_initialLabel_eq_one (i : B.unfrozenIndex) {w : SupportedRay 𝒅}
    (hw : w.generator.1 (B.basis i) ≠ 0) :
    (𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w = 1 :=
  rayFactor_completedBCHExp_completedTropicalTangentField_eq_one _ _ _ _ hw

/-- A nontrivial incoming ray label projects to the positive ray of the initial exponent.
Identity labels on the other tangent rays carry no monomial direction constraint. -/
theorem rayFactor_initialLabel_projectedDirection (i : B.unfrozenIndex) (w : SupportedRay 𝒅)
    (hw : (𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w ≠ 1) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • w.generator.1 = b • I.exponent i :=
  exists_nsmul_eq_nsmul_of_rayFactor_completedLog_ne_one 𝒅 ρ (I.alphabetNormal i)
    (I.tangentLetter i) (fun _ => 1) (AddMonoidHom.fst _ _) (I.exponent i)
    (fun s => ⟨s.val + 1, Nat.succ_pos _, by simp only [AddMonoidHom.coe_fst, coe_tangentLetter,
      PositiveDegrees.letter_fst, letterExponent_mk]⟩)
    (I.toCompletion_tangentInitialFunction_sub_one_mem i) hw

/-- The ray labels belonging to a fixed initial polynomial commute. -/
theorem commute_rayFactor_initialLabel (i : B.unfrozenIndex) (v w : SupportedRay 𝒅) :
    Commute ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i) v)
      ((𝒅).rayFactor ℒ (I.initialLabel (R := R) i) w) :=
  (H).commute_of_mem_wallGroup (I.rayFactor_initialLabel_mem_wallGroup i v)
    (I.rayFactor_initialLabel_mem_wallGroup i w) one_ne_zero one_ne_zero rfl

/-- The walls are indexed by the original unfrozen index and a tangent supported
ray. Coincident supports from different original polynomials remain distinct. -/
abbrev IncomingIndex : Type _ := Σ i : B.unfrozenIndex,
  {w : SupportedRay (PositiveDegrees.finiteAlphabet I.letterExponent) //
    I.alphabetNormal i w.generator = 0}

variable [Module.Finite ℤ N]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming BLM diagram on the finite alphabet lattice. Each polynomial
is split into supported-ray labels on its full cylinder hyperplane. -/
def incomingDiagram : DirectedDiagram (d := 𝒅) h (H) I.IncomingIndex :=
  DirectedDiagram.ofHyperplaneRayFactors h I.alphabetNormal I.alphabetNormal_ne_zero (fun _ => 0)
    I.initialLabel I.rayFactor_initialLabel_mem_wallGroup (by
      let := Module.Free.of_basis B.basis
      let : HasUniqueDiv (Module.Dual ℤ N × (I.Letter → ℤ)) := .of_isTorsionFree ℤ _
      exact hasFiniteSupport_rayFactor_sigma 𝒅 ρ I.initialLabel fun _ => Set.toFinite _)

/-- The wall over the polynomial `i` is cooriented by its alphabet normal. -/
@[simp]
theorem incomingDiagram_normal (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).normal = I.alphabetNormal j.1 := by
  simp [incomingDiagram]

/-- The wall indexed by a tangent supported ray lies on that ray. -/
@[simp]
theorem incomingDiagram_ray (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).ray = j.2.val := by
  simp [incomingDiagram]

/-- The wall over the polynomial `i` is supported on the kernel of its real normal. -/
@[simp]
theorem incomingDiagram_support (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).support =
      (h.realCharacter (I.alphabetNormal j.1)).ker := by
  ext
  simp [incomingDiagram]

/-- The wall over the polynomial `i` on the ray `w` carries the ray factor of its label. -/
@[simp]
theorem incomingDiagram_label (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).label =
      (𝒅).rayFactor ℒ (I.initialLabel (R := R) j.1) j.2.val := by
  simp [incomingDiagram]

/-- The incoming diagram is the ray presentation of the unsplit initial labels on the
cylinders over the `eᵢ⊥`. -/
theorem isRayFactorPresentation_incomingDiagram :
    (I.incomingDiagram (R := R) h).IsRayFactorPresentation (μ := I.alphabetNormal)
      (fun i => (h.realCharacter (I.alphabetNormal i)).ker) I.initialLabel where
  support := I.incomingDiagram_support h
  normal := I.incomingDiagram_normal h
  ray := I.incomingDiagram_ray h
  label := I.incomingDiagram_label h

/-- At every cutoff, the labels on the tangent rays of the actual incoming
diagram reassemble the original polynomial label. The finite set may contain
additional rays, whose surviving factors are retained automatically. -/
theorem projection_initialLabel_eq_noncommProd_incomingDiagram
    (i : B.unfrozenIndex) (k : ℕ)
    (s : Finset {w : SupportedRay 𝒅 // I.alphabetNormal i w.generator = 0})
    (hs : ∀ w ∈ (𝒅).raysAtOrder k, ∀ hw : I.alphabetNormal i w.generator = 0,
      ⟨w, hw⟩ ∈ s) :
    CompletedGroup.projection k (I.initialLabel (R := R) i) =
      s.noncommProd (fun w => CompletedGroup.projection k
        ((I.incomingDiagram (R := R) h).wall ⟨i, w⟩).label)
        (fun v _ w _ _ => by
          simp only [incomingDiagram_label]
          exact (I.commute_rayFactor_initialLabel i v.val w.val).map _) := by
  let := Module.Free.of_basis B.basis
  rw [initialLabel_def,
    projection_completedBCHExp_completedTropicalTangentField_eq_noncommProd_tangentRayFactor 𝒅 ρ
      (I.alphabetNormal i) _ k s hs]
  exact Finset.noncommProd_congr rfl (fun w _ => by
    simp only [incomingDiagram_label, initialLabel_def]) _

/-- Every wall is incoming, with no constraint on the skew form's radical. -/
@[simp]
theorem incomingDiagram_incoming (j : I.IncomingIndex) :
    ((I.incomingDiagram (R := R) h).wall j).Incoming := by
  simp [incomingDiagram]

/-- The full-hyperplane condition required for outgoing completion. -/
theorem incomingDiagram_full (j : I.IncomingIndex) :
    ∃ c : ℝ, ((I.incomingDiagram (R := R) h).wall j).support =
      {x | h.realCharacter ((I.incomingDiagram (R := R) h).wall j).normal x = c} :=
  ⟨0, by
    simp only [incomingDiagram_support, incomingDiagram_normal]
    exact Set.ext fun _ => LinearMap.mem_ker⟩

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
