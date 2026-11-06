/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.PolynomialInput.Grouping
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hyperplane
public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Scat

/-!
# Polynomial inputs whose form vanishes on the unfrozen sublattice

Let `I` be a BLM polynomial input on a skew lattice datum `(N, N_uf, N°, {,})` with adapted basis
`(e_j)`, and suppose that the form vanishes on `N_uf`, that is `{e_i, e_j} = 0` for all unfrozen
`i, j`. Pairings with frozen vectors are unrestricted, and they must be nonzero for the
injectivity assumption of a polynomial input: the zero form admits no polynomial input with
`N_uf ≠ 0`, whereas the principal BLM extension of an adapted datum whose form vanishes on
`N_uf`, for instance of the zero form, is a polynomial input whose form vanishes on its own
unfrozen sublattice (`AdaptedBasis.principalBLMDatum_form_eq_zero_of_forall_form_eq_zero`).

Then the exponents satisfy `w_i(e_j) = d_i {e_i, e_j} / ℓ_i = 0`, so every nontrivial ray label of
the incoming diagram lies on a ray whose generator is annihilated by all the cylinder normals
`e_j`. The labels of the incoming diagram therefore commute pairwise
(`commute_incomingDiagram_label_of_forall_form_eq_zero`), although the tropical vertex algebra
of the finite alphabet is not abelian. This holds pointwise: the labels of the walls over the
initial polynomials at two unfrozen indices `i, j` commute as soon as `{e_i, e_j} = 0`
(`commute_incomingDiagram_label_of_form_eq_zero`). We prove:

* the incoming diagram is consistent (`incomingDiagram_consistent_of_forall_form_eq_zero`), so
  its outgoing scattering class is its own class
  (`scat_incomingDiagram_of_forall_form_eq_zero`): the input is its own outgoing completion;
* if the coefficient monoid `Q` contains both signs of the spatial basis characters, the
  outgoing scattering class has a representative whose grouped wall functions are positive for
  the image of `S[Q]` under any semiring map `φ : S →+* R`: the incoming diagram, grouped by
  initial polynomial, with the wall functions `fᵢ = 1 + ∑_{s=1}^{ℓᵢ} pᵢₛ z^{s wᵢ}`
  (`exists_isPositiveWallRepresentative_of_forall_form_eq_zero`). For `φ = Nat.castRingHom ℚ`
  the monomial coefficients of the grouped wall functions are natural numbers, so as functions of
  the independent variables `pᵢₛ` they have coefficients in `ℕ[pᵢₛ]`.

If the form does not vanish on `N_uf`, the outgoing completion has further walls, whose
positivity is not formalized here.

The polynomial inputs and their positive outgoing representatives are those of Burcroff–Lee–Mou,
*Positivity of generalized cluster scattering diagrams*, §8.1 and Theorem 8.11
(arXiv:2503.03719v1).
-/

public section

noncomputable section

namespace Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput

open _root_.AddMonoidAlgebra
open scoped Mei.TropicalVertexCoefficientAction

variable {N ι R V : Type*} [AddCommGroup N]
  {D : SkewLatticeDatum N} {B : D.AdaptedBasis ι} (I : B.BLMPolynomialInput)
  [DecidableEq ι] [CommRing R] [DecidableEq (Module.Dual ℤ N)] [Algebra ℚ R]

local notation "𝒅" => PositiveDegrees.finiteAlphabet I.letterExponent
local notation "ρ" => AddMonoidHom.id (Module.Dual ℤ N × (I.Letter → ℤ))
local notation "ℒ" => tropicalVertexGrading (R := R) 𝒅 ρ
local notation "H" => tropicalVertexWallSpaces (R := R) 𝒅 ρ

variable [Module.Finite ℤ N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {latticeMap : (Module.Dual ℤ N × (I.Letter → ℤ)) →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- If `{e_i, e_j} = 0`, the labels of the incoming walls over the initial polynomials at `i`
and `j` commute: each cylinder normal annihilates the supported ray of every nontrivial label of
the other. -/
theorem commute_incomingDiagram_label_of_form_eq_zero (j j' : I.IncomingIndex)
    (hjj' : D.form (B.basis j.1) (B.basis j'.1) = 0) :
    Commute ((I.incomingDiagram (R := R) h).wall j).label
      ((I.incomingDiagram (R := R) h).wall j').label := by
  simp only [incomingDiagram_label]
  by_cases hj : (𝒅).rayFactor ℒ (I.initialLabel (R := R) j.1) j.2.val = 1
  · rw [hj]
    exact Commute.one_left _
  by_cases hj' : (𝒅).rayFactor ℒ (I.initialLabel (R := R) j'.1) j'.2.val = 1
  · rw [hj']
    exact Commute.one_right _
  refine (H).commute_of_mem_wallGroup_of_apply_eq_zero ?_ ?_
    (I.rayFactor_initialLabel_mem_wallGroup j.1 j.2.val)
    (I.rayFactor_initialLabel_mem_wallGroup j'.1 j'.2.val)
  · simpa using I.generator_apply_eq_zero_of_form_eq_zero
      (by rw [D.form_swap, hjj', neg_zero]) hj'
  · simpa using I.generator_apply_eq_zero_of_form_eq_zero hjj' hj

/-- If the form vanishes on `N_uf`, the labels of the incoming diagram commute pairwise. -/
theorem commute_incomingDiagram_label_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) (j j' : I.IncomingIndex) :
    Commute ((I.incomingDiagram (R := R) h).wall j).label
      ((I.incomingDiagram (R := R) h).wall j').label :=
  I.commute_incomingDiagram_label_of_form_eq_zero h j j' (B.forall_form_eq_zero_iff.mp hform _ _)

/-- If the form vanishes on `N_uf`, the incoming diagram of the polynomial input is consistent:
its walls are full hyperplanes with pairwise commuting labels. -/
theorem incomingDiagram_consistent_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) :
    (I.incomingDiagram (R := R) h).Consistent :=
  DirectedDiagram.consistent_of_commute_of_full _ (I.incomingDiagram_full h)
    (I.commute_incomingDiagram_label_of_forall_form_eq_zero h hform)

/-- If the form vanishes on `N_uf`, the outgoing scattering class of the polynomial input is the
class of its incoming diagram: the input is its own outgoing completion. -/
theorem scat_incomingDiagram_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0) :
    (I.incomingDiagram (R := R) h).Scat (I.incomingDiagram_full h) =
      (I.incomingDiagram (R := R) h).toClass :=
  DirectedDiagram.scat_eq_toClass_of_consistent _ _
    (I.incomingDiagram_consistent_of_forall_form_eq_zero h hform)

variable (Q : AddSubmonoid (Module.Dual ℤ N × (I.Letter → ℤ)))
  [Fact ((PositiveDegrees.finiteAlphabet I.letterExponent).monoid ≤ Q)]

local notation "G" => TropicalVertexCoefficientAction.filtration (R := R) 𝒅 Q

/-- **Positive representatives when the form vanishes on `N_uf`.** If the form vanishes on the
unfrozen sublattice and the coefficient monoid `Q` contains both signs of the spatial basis
characters `(eᵢ*, 0)`, `i ∈ I_uf`, then the outgoing scattering class of the polynomial input has
a representative whose grouped wall functions are positive for the image of `S[Q]` under
`φ : S →+* R`: the incoming diagram itself, with wall functions
`fᵢ = 1 + ∑_{s=1}^{ℓᵢ} pᵢₛ z^{s wᵢ}`. -/
theorem exists_isPositiveWallRepresentative_of_forall_form_eq_zero
    (hform : ∀ n m : D.unfrozen, D.form n m = 0)
    (hQ : ∀ i : B.unfrozenIndex, (B.basis.coord i, 0) ∈ Q ∧ (-B.basis.coord i, 0) ∈ Q)
    {S : Type*} [Semiring S] (φ : S →+* R) :
    ∃ (κ : Type _) (E : DirectedDiagram (d := 𝒅) h (H) κ),
      E.toClass = (I.incomingDiagram (R := R) h).Scat (I.incomingDiagram_full h) ∧
        E.IsPositiveWallRepresentative ((G).completedBCHAction 𝒅 ℒ) (mapRingHom Q φ).rangeS
          (AddMonoidHom.fst _ _) :=
  ⟨_, _, (I.scat_incomingDiagram_of_forall_form_eq_zero h hform).symm,
    I.isPositiveWallRepresentative_incomingDiagram h Q hQ φ⟩

end Mei.SkewLatticeDatum.AdaptedBasis.BLMPolynomialInput
