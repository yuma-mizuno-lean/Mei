/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Incoming
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.FunctionWall

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

We use `BLMPolynomialInput.projection_initialLabel_eq_noncommProd_incomingDiagram` and
`BLMPolynomialInput.completedBCHAction_initialLabel`. The polynomial inputs and their
positivity follow Burcroff–Lee–Mou, *Positivity of generalized cluster scattering
diagrams*, §8.1 (arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra

variable {N ι R V : Type*} [AddCommGroup N]
  {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι} (I : B.BLMPolynomialInput)
  [DecidableEq ι] [CommRing R] [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R]
  [Module.Finite ℤ N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id (Module.Dual ℤ N × (I.Letter → ℤ))
local notation "χ" i => AddMonoidHom.comp (Int.castAddHom R) (I.alphabetNormal i)
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ

/-- The grouping of the incoming ray walls by their initial polynomial. -/
def incomingGrouping :
    (I.incomingDiagram (R := R) h).FunctionWallGrouping (AddMonoidHom.fst _ _) B.unfrozenIndex where
  group := Sigma.fst
  support_eq hj := by simp only [incomingDiagram_support, hj]
  normal_eq hj := by simp only [incomingDiagram_normal, hj]
  projectedDirection_eq {j j'} hj hj0 hj'0 := by
    simp only [incomingDiagram_label] at hj0 hj'0
    obtain ⟨a, b, ha, hb, he⟩ := I.rayFactor_initialLabel_projectedDirection j.1 j.2.val hj0
    obtain ⟨a', b', ha', hb', he'⟩ := I.rayFactor_initialLabel_projectedDirection j'.1 j'.2.val hj'0
    refine ⟨b' * a, b * a', Nat.mul_pos hb' ha, Nat.mul_pos hb ha', ?_⟩
    simp only [incomingDiagram_ray, AddMonoidHom.coe_fst]
    rw [mul_smul, he, mul_smul, he', ← hj, smul_comm b' b]
  isPrimitive_normal j := by
    simpa only [incomingDiagram_normal] using I.isPrimitive_alphabetNormal j.1

@[simp]
theorem incomingGrouping_group (j : I.IncomingIndex) :
    (I.incomingGrouping (R := R) h).group j = j.1 := (rfl)

/-- The label of the group of ray walls over `fᵢ` is the unsplit initial label. -/
@[simp]
theorem label_incomingGrouping (i : B.unfrozenIndex) :
    (I.incomingGrouping (R := R) h).label i = I.initialLabel i := by
  classical
  refine (((I.incomingGrouping h).eq_label_iff i _).mpr fun k => ?_).symm
  let := Module.Free.of_basis B.basis
  let : HasUniqueDiv (Module.Dual ℤ N × (I.Letter → ℤ)) := .of_isTorsionFree ℤ _
  let T : Finset {w : SupportedRay 𝒅 // I.alphabetNormal i w.generator = 0} :=
    ((𝒅).finite_raysAtOrder k).toFinset.subtype _
  let e : {w : SupportedRay 𝒅 // I.alphabetNormal i w.generator = 0} ↪ I.IncomingIndex :=
    ⟨fun w => ⟨i, w⟩, fun _ _ hw => by simpa using hw⟩
  refine (I.projection_initialLabel_eq_noncommProd_incomingDiagram h i k T
    fun w hw hw0 => by simpa [T] using hw).trans ((Finset.noncommProd_map T e _ _).symm.trans
      ((I.incomingGrouping h).groupLabel_eq_noncommProd i k (T.map e) ?_ ?_).symm)
  · intro j hj
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hj
    exact I.incomingGrouping_group h _
  · intro j hact hj
    rw [incomingGrouping_group] at hj
    obtain ⟨i', w⟩ := j
    obtain rfl : i' = i := hj
    refine Finset.mem_map.mpr ⟨w, ?_, rfl⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset]
    by_contra hw
    apply ((I.incomingDiagram h).mem_active k _).mp hact
    simpa only [incomingDiagram_label] using
      (𝒅).projection_eq_one_of_notMem_raysAtOrder ℒ
        ((𝒅).rayFactor_mem_completedRaySubgroup ℒ (I.initialLabel i') w.val) k hw

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
  refine ((I.incomingGrouping h).isWallFunction_iff _ i _).mpr fun j hj => ?_
  rw [incomingGrouping_group] at hj
  subst hj
  constructor
  · let p : Q := ⟨(B.basis.coord j.1, 0), hQ.1⟩
    let p' : Q := ⟨(-B.basis.coord j.1, 0), hQ.2⟩
    have hpp' : p + p' = 0 := Subtype.ext (by simp [p, p'])
    have hmul : (single p 1 * single p' 1 : R[Q]) = 1 := by
      rw [single_mul_single, hpp', mul_one, one_def]
    refine ⟨p, by simp [p], ?_⟩
    exact (isUnit_iff_exists_inv.mpr ⟨single p' 1, hmul⟩).map (G).toCompletion
  · intro p c
    rw [label_incomingGrouping]
    simpa only [incomingDiagram_normal, AddMonoidHom.id_apply] using
      I.completedBCHAction_initialLabel Q j.1 _ (I.coe_completedInitialFunction Q j.1) p c

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
