/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall.RayFactor

/-!
# Function walls of BLM polynomial inputs

The incoming diagram of a BLM polynomial input splits each initial polynomial
`fᵢ = 1 + ∑ₛ pᵢₛ z^(s wᵢ)` into ray walls on the full cylinder over `eᵢ⊥`, one for every
tangent supported ray of the finite alphabet lattice. Grouping these walls by the original
index `i` is a function-wall grouping: the walls of a group share the cylinder and its
primitive normal. Walls with nontrivial labels also share a projected monomial direction
in `M`; identity labels impose no direction constraint. The products of their labels
at each cutoff reassemble the unsplit label
`exp(log(fᵢ) ∂_(eᵢ))`, and this label acts on monomials by `z^p ↦ fᵢ^(⟨eᵢ, p⟩) z^p`.

The polynomial `fᵢ` is the image of the polynomial with natural-number coefficients
`1 + ∑ₛ z^(letter (i, s))` in the independent variables, so its wall function is positive
for the image of `S[Q]` under every coefficient map `S →+* R`. Hence the incoming diagram is
a positive wall representative when the coefficient monoid contains the positive and negative
basis characters, so the normal-weight-one monomials are invertible.

The grouping is the grouping of a ray presentation by label,
`DirectedDiagram.FunctionWallGrouping.ofRayFactors`, with its label and wall-function
theorems. The polynomial inputs and their positivity follow Burcroff–Lee–Mou, *Positivity of
generalized cluster scattering diagrams*, §8.1 (arXiv:2503.03719v1).
-/

public section

open TauCeti (PositiveDegrees)

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

variable {N ι R V : Type*} [AddCommGroup N]
  {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι} (I : B.BLMPolynomialInput)
  [DecidableEq ι] [CommRing R] [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R]
  [Module.Finite ℤ N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id (Module.Dual ℤ N × (I.Letter → ℤ))
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ

/-- The grouping of the incoming ray walls by their initial polynomial. -/
def incomingGrouping :
    (I.incomingDiagram (R := R) h).FunctionWallGrouping (AddMonoidHom.fst _ _) B.unfrozenIndex :=
  DirectedDiagram.FunctionWallGrouping.ofRayFactors (I.isRayFactorPresentation_incomingDiagram h)
    I.isPrimitive_alphabetNormal (AddMonoidHom.fst _ _) I.exponent fun i w hw =>
      I.rayFactor_initialLabel_projectedDirection i w hw

/-- A ray wall belongs to the group of its initial polynomial. -/
@[simp]
theorem incomingGrouping_group (j : I.IncomingIndex) :
    (I.incomingGrouping (R := R) h).group j = j.1 :=
  DirectedDiagram.FunctionWallGrouping.ofRayFactors_group ..

/-- The label of the group of ray walls over `fᵢ` is the unsplit initial label. -/
@[simp]
theorem label_incomingGrouping (i : B.unfrozenIndex) :
    (I.incomingGrouping (R := R) h).label i = I.initialLabel i :=
  let := Module.Free.of_basis B.basis
  DirectedDiagram.FunctionWallGrouping.label_ofRayFactors _ _ _ _ _ i _ (I.initialLabel_def i)

section Action

open scoped Mei.TropicalVertexCoefficientAction

variable (Q : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)))
  [Fact ((PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 Q

/-- The initial polynomial is the wall function of the grouped ray walls over it. -/
theorem isWallFunction_incomingGrouping (i : B.unfrozenIndex)
    (hQ : (B.basis.coord i, 0) ∈ Q ∧ (-B.basis.coord i, 0) ∈ Q) :
    (I.incomingGrouping (R := R) h).IsWallFunction ((G).completedBCHAction 𝒅 ℒ) i
      (I.completedInitialFunction Q i) := by
  let := Module.Free.of_basis B.basis
  have hp : I.alphabetNormal i (AddMonoidHom.id _ (B.basis.coord i, 0)) = 1 := by simp
  exact DirectedDiagram.FunctionWallGrouping.isWallFunction_ofRayFactors
    (I.isRayFactorPresentation_incomingDiagram h) I.isPrimitive_alphabetNormal
    (AddMonoidHom.fst _ _) I.exponent _ Q i _ (I.initialLabel_def (R := R) i) _
    (by rw [coe_completedInitialFunction, completedTropicalTangentInclusion_toCompletion,
      tropicalTangentInclusion_tangentInitialFunction]) hp hQ.1 (by simpa using hQ.2)

variable (hQ : ∀ i : B.unfrozenIndex,
  (B.basis.coord i, 0) ∈ Q ∧ (-B.basis.coord i, 0) ∈ Q)

include hQ

/-- The grouping of the incoming diagram by initial polynomial is positive when the
coefficient monoid contains both signs of the spatial basis characters. -/
theorem isPositive_incomingGrouping {S : Type*} [Semiring S] (φ : S →+* R) :
    (I.incomingGrouping (R := R) h).IsPositive ((G).completedBCHAction 𝒅 ℒ)
      (AddMonoidAlgebra.mapRingHom Q φ).rangeS :=
  ((I.incomingGrouping h).isPositive_iff _ _).mpr fun i =>
    ⟨I.completedInitialFunction Q i, I.isWallFunction_incomingGrouping h Q i (hQ i),
      I.isPositive_completedInitialFunction Q φ i⟩

/-- The incoming diagram of a BLM polynomial input is a positive wall representative when
the coefficient monoid contains both signs of the spatial basis characters. -/
theorem isPositiveWallRepresentative_incomingDiagram {S : Type*} [Semiring S]
    (φ : S →+* R) :
    (I.incomingDiagram (R := R) h).IsPositiveWallRepresentative
      ((G).completedBCHAction 𝒅 ℒ) (AddMonoidAlgebra.mapRingHom Q φ).rangeS
      (AddMonoidHom.fst _ _) :=
  (I.isPositive_incomingGrouping h Q hQ φ).isPositiveWallRepresentative

end Action

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
