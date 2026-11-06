/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.RankTwoPolynomialInput.Pentagon.Basic

/-!
# The coordinate axes as a rank-two polynomial input of type `A₂`

Take `L = M = ℤ²`, `π = id` and the quadrant `ℕ²` with the coordinate-sum degree. The
horizontal line `{y = 0}`, cooriented by `-e₂*`, with wall function `1 + c₀ z^{e₁}`, and the
vertical line `{x = 0}`, cooriented by `e₁*`, with wall function `1 + c₁ z^{e₂}`
(`RankTwoPolynomialInput.Examples.axesInput`), form an input of type `A₂`
(`RankTwoPolynomialInput.Examples.isTypeA₂_axesInput`): `-e₂*(e₂) = -1` and `e₁*(e₁) = 1`.
Hence, for arbitrary coefficients, its scattering class is represented by the pentagon diagram,
whose outgoing wall `{x = y, y ≤ 0}` carries the binomial label of `1 + c₀ c₁ z^{e₁ + e₂}`
(`RankTwoPolynomialInput.Examples.scat_axesInput`). For the independent variables `c₀, c₁` over
`ℚ` and the full coefficient lattice `ℤ²`, this representative is a positive wall representative
whose grouped wall functions have coefficients in `ℕ[c₀, c₁]`
(`RankTwoPolynomialInput.Examples.exists_isPositiveWallRepresentative_axesInput`). This is the
scattering diagram of Gross–Pandharipande–Siebert, *Quivers, curves, and the tropical vertex*,
Example 1.6 (arXiv:0902.0779v3), with coefficients.
-/

public section

noncomputable section

namespace Mei.RankTwoPolynomialInput.Examples

open Module

local notation "ℕ²" => Basis.positiveDegrees (Basis.finTwoProd ℤ)

/-- The coordinate axes of `ℤ²` with the wall functions `1 + c₀ z^{e₁}` on the horizontal line,
cooriented by `-e₂*`, and `1 + c₁ z^{e₂}` on the vertical line, cooriented by `e₁*`, on the
quadrant `ℕ²`. -/
def axesInput : RankTwoPolynomialInput ℕ² (ℤ × ℤ) (Fin 2) where
  projection := AddMonoidHom.id _
  projection_surjective := Function.surjective_id
  finrank_eq_two := by simp
  tangent := ![(1, 0), (0, 1)]
  isPrimitive_tangent j := by
    fin_cases j
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.fst ℤ ℤ ℤ, rfl⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨LinearMap.snd ℤ ℤ ℤ, rfl⟩
  normal := ![-LinearMap.snd ℤ ℤ ℤ, LinearMap.fst ℤ ℤ ℤ]
  isPrimitive_normal j := by
    fin_cases j
    · exact TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (0, -1), by simp⟩
    · exact TauCeti.isPrimitive_def.mpr ⟨Module.Dual.eval ℤ _ (1, 0), by simp⟩
  normal_tangent j := by fin_cases j <;> simp
  offset _ := 0
  exponents := ![{(1, 0)}, {(0, 1)}]
  mem_monoid_of_mem_exponents {j n} hn := by
    fin_cases j <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finset.mem_singleton] at hn
      subst hn
      simp
  ne_zero_of_mem_exponents {j n} hn := by
    fin_cases j <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finset.mem_singleton] at hn
      subst hn
      simp
  exists_projection_eq_of_mem_exponents {j n} hn := by
    fin_cases j <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finset.mem_singleton] at hn
      subst hn
      exact ⟨1, one_pos, by simp⟩
  finite_nontrivial _ := Set.toFinite _

/-- The projection of the axes input is the identity of `ℤ²`. -/
@[simp]
theorem axesInput_projection : axesInput.projection = AddMonoidHom.id (ℤ × ℤ) := (rfl)

/-- The coorientations of the axes are `-e₂*` and `e₁*`. -/
@[simp]
theorem axesInput_normal (j : Fin 2) :
    axesInput.normal j = ![-LinearMap.snd ℤ ℤ ℤ, LinearMap.fst ℤ ℤ ℤ] j := (rfl)

/-- The exponents of the axes are `e₁` and `e₂`. -/
@[simp]
theorem axesInput_exponents (j : Fin 2) :
    axesInput.exponents j = ![{(1, 0)}, {(0, 1)}] j := (rfl)

/-- Both axes pass through the origin. -/
@[simp]
theorem axesInput_offset (j : Fin 2) : axesInput.offset j = 0 := (rfl)

/-- The cylinder normal of the horizontal line is `-e₂*`. -/
@[simp]
theorem wallNormal_axesInput_zero (q : ℤ × ℤ) : axesInput.wallNormal 0 q = -q.2 := by
  simp [wallNormal_apply]

/-- The cylinder normal of the vertical line is `e₁*`. -/
@[simp]
theorem wallNormal_axesInput_one (q : ℤ × ℤ) : axesInput.wallNormal 1 q = q.1 := by
  simp [wallNormal_apply]

/-- The coordinate axes with the wall functions `1 + c₀ z^{e₁}` and `1 + c₁ z^{e₂}` form a
rank-two polynomial input of type `A₂`. -/
theorem isTypeA₂_axesInput : axesInput.IsTypeA₂ 0 1 (1, 0) (0, 1) where
  eq_or_eq j := by fin_cases j <;> simp
  exponents_fst := by simp
  exponents_snd := by simp
  offset_fst := axesInput_offset 0
  offset_snd := axesInput_offset 1
  wallNormal_fst_snd := by simp
  wallNormal_snd_fst := by simp

variable {R : Type*} [CommRing R] [Algebra ℚ R] {latticeMap : ℤ × ℤ →+ ℝ × ℝ}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- For arbitrary coefficients `c₀, c₁`, the scattering class of the coordinate axes with the wall
functions `1 + c₀ z^{e₁}` and `1 + c₁ z^{e₂}` is represented by the pentagon diagram, whose
outgoing wall `{x = y, y ≤ 0}` carries the binomial label of `1 + c₀ c₁ z^{e₁ + e₂}`. -/
theorem scat_axesInput (c : axesInput.Variable → R) :
    (axesInput.incomingDiagram h c).Scat (axesInput.incomingDiagram_full h c) =
      (isTypeA₂_axesInput.isTypeA₂Presentation h c).pentagonDiagram.toClass :=
  (isTypeA₂_axesInput.isTypeA₂Presentation h c).scat_eq_toClass_pentagonDiagram

open scoped Mei.TropicalVertexCoefficientAction

-- Named explicitly: an anonymous instance of the same type in `RankTwoPolynomialInput/Examples`
-- would get the same automatic name.
/-- The quadrant monoid lies in the full coefficient lattice `ℤ²`. -/
local instance factQuadrantMonoidLeTop : Fact ((ℕ²).monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) :=
  ⟨le_top⟩

/-- For the independent variables `c₀, c₁` over `ℚ` and the full coefficient lattice `ℤ²`, the
scattering class of the coordinate axes with the wall functions `1 + c₀ z^{e₁}` and
`1 + c₁ z^{e₂}` has a consistent outgoing representative whose grouped wall functions have
coefficients in `ℕ[c₀, c₁]`. -/
theorem exists_isPositiveWallRepresentative_axesInput :
    ∃ (κ : Type) (E : DirectedDiagram (d := ℕ²) h
        (tropicalVertexWallSpaces (R := MvPolynomial axesInput.Variable ℚ) ℕ²
          (AddMonoidHom.id (ℤ × ℤ))) (axesInput.IncomingIndex ⊕ κ)),
      DirectedDiagram.IsOutgoingCompletion (axesInput.incomingDiagram h MvPolynomial.X).wall E ∧
      E.toClass = (axesInput.incomingDiagram h MvPolynomial.X).Scat
        (axesInput.incomingDiagram_full h MvPolynomial.X) ∧
      E.IsPositiveWallRepresentative
        ((TropicalVertexCoefficientAction.filtration (R := MvPolynomial axesInput.Variable ℚ) ℕ²
          (⊤ : AddSubmonoid (ℤ × ℤ))).completedBCHAction ℕ²
          (tropicalVertexGrading (R := MvPolynomial axesInput.Variable ℚ) ℕ²
            (AddMonoidHom.id (ℤ × ℤ))))
        (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
          (MvPolynomial.map (σ := axesInput.Variable) (Nat.castRingHom ℚ))).rangeS
        axesInput.projection :=
  isTypeA₂_axesInput.exists_isPositiveWallRepresentative_scat h MvPolynomial.X ⊤ trivial trivial
    _ ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩ ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩

end Mei.RankTwoPolynomialInput.Examples
