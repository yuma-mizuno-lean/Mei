/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Binomial

/-!
# Polynomial inputs of type `A₂`

Let `I` be a BLM polynomial input on a skew lattice datum `(N, N_uf, N°, {,})` with adapted basis
`(e_j)` and multipliers `d_j`. It is *of type `A₂`* at two unfrozen indices `i₁, i₂`
(`BLMPolynomialInput.IsTypeA₂`) when these are its only unfrozen indices, both multiplicities are
one, and `d_{i₁} {e_{i₁}, e_{i₂}} = d_{i₂} {e_{i₁}, e_{i₂}} = 1`. Frozen indices are unrestricted.
The initial functions are then the binomials `1 + p₁ z^{w₁}` and `1 + p₂ z^{w₂}` on the cylinders
over `e_{i₁}⊥` and `e_{i₂}⊥`, with `w₁(e_{i₂}) = 1` and `w₂(e_{i₁}) = -1`
(`IsTypeA₂.exponent_fst_snd`, `IsTypeA₂.exponent_snd_fst`). In the finite alphabet lattice
`M × ℤ^E`, the variable monomials `p_k z^{w_k}` are the letters `v_k = (w_k, e_{(i_k, 1)})`.

The incoming diagram is a ray presentation of type `A₂` of the binomial labels of
`1 + z^{v₁}` and `1 + z^{v₂}` (`IsTypeA₂.isTypeA₂Presentation`,
`Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Binomial`). Hence:

* adding the half-hyperplane `{e_{i₁} + e_{i₂} = 0, e_{i₁} ≥ 0}` of the alphabet space, cooriented
  by `e_{i₁} + e_{i₂}` and labelled by the binomial label of `1 + z^{v₁ + v₂}`, that is of
  `1 + p₁ p₂ z^{w₁ + w₂}`, gives a consistent outgoing completion of the input, which represents
  its outgoing scattering class
  (`DirectedDiagram.IsTypeA₂Presentation.isOutgoingCompletion_pentagonDiagram`,
  `DirectedDiagram.IsTypeA₂Presentation.scat_eq_toClass_pentagonDiagram`);
* if the coefficient monoid `Q` contains both signs of the spatial basis characters
  `(e_{i₁}*, 0)` and `(e_{i₂}*, 0)`, this representative is a positive wall representative for
  the image of `S[Q]` under any semiring map `φ : S →+* R`, with grouped wall functions
  `1 + p₁ z^{w₁}`, `1 + p₂ z^{w₂}` and `1 + p₁ p₂ z^{w₁ + w₂}`, and `1` on the remaining ray walls
  (`IsTypeA₂.exists_isPositiveWallRepresentative_scat`). For `φ = Nat.castRingHom ℚ` the monomial
  coefficients are natural numbers, so as functions of the variables `p₁, p₂` the grouped wall
  functions have coefficients in `ℕ[p₁, p₂]`.

This is the case of a nondegenerate rank-two unfrozen part of type `A₂` with `ℓ = (1, 1)` of
Burcroff–Lee–Mou, *Positivity of generalized cluster scattering diagrams*, Theorem 8.11
(arXiv:2503.03719v1); the consistent completion is the cluster scattering diagram of type `A₂` of
Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster algebras*, Example 1.15
(arXiv:1411.1394v2).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra

variable {N ι : Type*} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  (I : B.BLMPolynomialInput)

/-- A polynomial input is *of type `A₂`* at the unfrozen indices `i₁, i₂` when every unfrozen
index is `i₁` or `i₂`, both multiplicities are one, and the multipliers and the form satisfy
`d_{i₁} {e_{i₁}, e_{i₂}} = 1` and `d_{i₂} {e_{i₁}, e_{i₂}} = 1`. -/
structure IsTypeA₂ (i₁ i₂ : B.unfrozenIndex) : Prop where
  /-- Every unfrozen index is one of the two. -/
  eq_or_eq (i : B.unfrozenIndex) : i = i₁ ∨ i = i₂
  /-- The first initial function has a single variable. -/
  multiplicity_fst : I.multiplicity i₁ = 1
  /-- The second initial function has a single variable. -/
  multiplicity_snd : I.multiplicity i₂ = 1
  /-- `d_{i₁} {e_{i₁}, e_{i₂}} = 1`. -/
  multiplier_mul_form_fst : (B.multiplier i₁ : ℚ) * D.form (B.basis i₁) (B.basis i₂) = 1
  /-- `d_{i₂} {e_{i₁}, e_{i₂}} = 1`. -/
  multiplier_mul_form_snd : (B.multiplier i₂ : ℚ) * D.form (B.basis i₁) (B.basis i₂) = 1

namespace IsTypeA₂

variable {I} {i₁ i₂ : B.unfrozenIndex} (hA : I.IsTypeA₂ i₁ i₂)
include hA

/-- The first exponent takes the value `w₁(e_{i₂}) = d_{i₁} {e_{i₁}, e_{i₂}} = 1`. -/
theorem exponent_fst_snd : I.exponent i₁ (B.basis i₂) = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [I.cast_exponent_apply, hA.multiplicity_fst, hA.multiplier_mul_form_fst]
  simp

/-- The second exponent takes the value `w₂(e_{i₁}) = d_{i₂} {e_{i₂}, e_{i₁}} = -1`. -/
theorem exponent_snd_fst : I.exponent i₂ (B.basis i₁) = -1 := by
  apply Int.cast_injective (α := ℚ)
  rw [I.cast_exponent_apply, hA.multiplicity_snd, D.form_swap, mul_neg,
    hA.multiplier_mul_form_snd]
  simp

/-- The two indices are distinct. -/
theorem fst_ne_snd : i₁ ≠ i₂ := by
  intro he
  have h₁ := hA.exponent_fst_snd
  rw [← he, exponent_apply_basis_self] at h₁
  exact zero_ne_one h₁

/-- The variable `p₁` of the first initial function. -/
def fstLetter : I.Letter := ⟨i₁, ⟨0, by rw [hA.multiplicity_fst]; exact one_pos⟩⟩

/-- The variable `p₂` of the second initial function. -/
def sndLetter : I.Letter := ⟨i₂, ⟨0, by rw [hA.multiplicity_snd]; exact one_pos⟩⟩

/-- The first variable belongs to the first initial function. -/
theorem fstLetter_def :
    hA.fstLetter = ⟨i₁, ⟨0, by rw [hA.multiplicity_fst]; exact one_pos⟩⟩ := (rfl)

/-- The second variable belongs to the second initial function. -/
theorem sndLetter_def :
    hA.sndLetter = ⟨i₂, ⟨0, by rw [hA.multiplicity_snd]; exact one_pos⟩⟩ := (rfl)

variable [DecidableEq ι]

/-- The cylinder normal `e_{i₁}` pairs to `-1` with the letter `v₂ = (w₂, e_{(i₂, 1)})`. -/
theorem alphabetNormal_fst_sndLetter :
    I.alphabetNormal i₁ (PositiveDegrees.letter I.letterExponent hA.sndLetter) = -1 := by
  simp [sndLetter_def, hA.exponent_snd_fst]

/-- The cylinder normal `e_{i₂}` pairs to `1` with the letter `v₁ = (w₁, e_{(i₁, 1)})`. -/
theorem alphabetNormal_snd_fstLetter :
    I.alphabetNormal i₂ (PositiveDegrees.letter I.letterExponent hA.fstLetter) = 1 := by
  simp [fstLetter_def, hA.exponent_fst_snd]

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq (Module.Dual ℤ N)]
  [Module.Finite ℤ N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The incoming diagram of a polynomial input of type `A₂` is a ray presentation of type `A₂`:
the ray presentation of the binomial labels of `1 + z^{v₁}` and `1 + z^{v₂}` on the cylinders
over `e_{i₁}⊥` and `e_{i₂}⊥`, with coefficients one. -/
theorem isTypeA₂Presentation :
    (I.incomingDiagram (R := R) h).IsTypeA₂Presentation I.initialLabel i₁ i₂
      (PositiveDegrees.letter I.letterExponent hA.fstLetter)
      (PositiveDegrees.letter I.letterExponent hA.sndLetter) 1 1 where
  isRayFactorPresentation :=
    { (I.isRayFactorPresentation_incomingDiagram h) with
      support x := ((I.isRayFactorPresentation_incomingDiagram h).support x).trans
        (Set.ext fun _ => LinearMap.mem_ker) }
  eq_or_eq := hA.eq_or_eq
  mem_monoid_fst := PositiveDegrees.letter_mem _ _
  mem_monoid_snd := PositiveDegrees.letter_mem _ _
  apply_fst_fst := I.alphabetNormal_letter_self i₁ _
  apply_snd_snd := I.alphabetNormal_letter_self i₂ _
  apply_fst_snd := hA.alphabetNormal_fst_sndLetter
  apply_snd_fst := hA.alphabetNormal_snd_fstLetter
  label_fst := I.initialLabel_eq_binomialLabel hA.multiplicity_fst _
  label_snd := I.initialLabel_eq_binomialLabel hA.multiplicity_snd _

end IsTypeA₂

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

/-! ### Positivity, needing the lattice in `Type`

The pentagon identity `Mei.binomialLabel_pentagon` is transported through `ℤ × ℤ`, so the
theorem below takes `N ι : Type`, putting the alphabet lattice in `Type`. -/

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.IsTypeA₂

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

variable {N ι : Type} [AddCommGroup N] {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι}
  {I : B.BLMPolynomialInput} {i₁ i₂ : B.unfrozenIndex} (hA : I.IsTypeA₂ i₁ i₂)
  [DecidableEq ι] {R V : Type*} [CommRing R] [Algebra ℚ R] [DecidableEq (Module.Dual ℤ N)]
  [Module.Finite ℤ N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)
  (Q : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)))
  [Fact ((PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)]

local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id (Module.Dual ℤ N × (I.Letter → ℤ))
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ
local notation "H" => tropicalVertexWallSpaces (R := R) 𝒅 ρ
local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 Q

include hA in
/-- **Positive representatives of polynomial inputs of type `A₂`.** If the coefficient monoid `Q`
contains both signs of the spatial basis characters `(eᵢ*, 0)`, `i ∈ I_uf`, the outgoing scattering
class of a polynomial input of type `A₂` has a consistent outgoing representative, the pentagon
diagram of `IsTypeA₂.isTypeA₂Presentation`, whose grouped wall functions `1 + p₁ z^{w₁}`,
`1 + p₂ z^{w₂}`, `1 + p₁ p₂ z^{w₁ + w₂}` (and `1` on the remaining ray walls) are positive for the
image of `S[Q]` under any semiring map `φ : S →+* R`. -/
theorem exists_isPositiveWallRepresentative_scat
    (hQ : ∀ i : B.unfrozenIndex, (B.basis.coord i, 0) ∈ Q ∧ (-B.basis.coord i, 0) ∈ Q)
    {S : Type*} [Semiring S] (φ : S →+* R) :
    ∃ (κ : Type) (E : DirectedDiagram (d := 𝒅) h H (I.IncomingIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (I.incomingDiagram (R := R) h).wall E ∧
      E.toClass = (I.incomingDiagram (R := R) h).Scat (I.incomingDiagram_full h) ∧
      E.IsPositiveWallRepresentative ((G).completedBCHAction 𝒅 ℒ) (mapRingHom Q φ).rangeS
        (AddMonoidHom.fst _ _) :=
  let := Module.Free.of_basis B.basis
  -- The monomials `z^{(e_{i₁}*, 0)}` and `z^{(e_{i₂}*, 0)}` are invertible, and the cylinder
  -- normals `e_{i₁}`, `e_{i₂}` take the values `1, 0` and `0, 1` on their exponents.
  (hA.isTypeA₂Presentation h).exists_isPositiveWallRepresentative_scat Q (AddMonoidHom.fst _ _) φ
    ⟨1, map_one φ⟩ ⟨1, map_one φ⟩
    ⟨(B.basis.coord i₁, 0), (hQ i₁).1, by simpa using (hQ i₁).2, by simp,
      by simp [Module.Basis.coord_apply, Finsupp.single_eq_of_ne (Subtype.coe_injective.ne
        hA.fst_ne_snd)]⟩
    ⟨(B.basis.coord i₂, 0), (hQ i₂).1, by simpa using (hQ i₂).2, by simp⟩

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput.IsTypeA₂
