/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Hexagon.Binomial

/-!
# The coordinate axes with wall functions `1 + c₀ x` and `(1 + c₁ y)^2`

Take `Γ = Λ = ℤ²`, the identity spatial projection and the quadrant `ℕ²` with the coordinate-sum
degree. The horizontal axis `{y = 0}`, cooriented by `-e₂*` and labelled by the binomial label of
`1 + c₀ z^{e₁}`, and the vertical axis `{x = 0}`, cooriented by `e₁*` and labelled by the square of
the binomial label of `1 + c₁ z^{e₂}`, the label of `(1 + c₁ z^{e₂})^2`
(`DirectedDiagram.Examples.axesLabel`), have a ray presentation
(`DirectedDiagram.Examples.axesDiagram`) of type `B₂`
(`DirectedDiagram.Examples.isTypeB₂Presentation_axesDiagram`): `-e₂*(e₂) = -1` and
`e₁*(e₁) = 1`. Hence, for arbitrary coefficients, its scattering class is represented by the
hexagon diagram, whose outgoing walls `{x = y, y ≤ 0}` and `{2 x = y, y ≤ 0}` carry the labels of
`(1 + c₀ c₁ z^{e₁ + e₂})^2` and `1 + c₀ c₁^2 z^{e₁ + 2 e₂}`
(`DirectedDiagram.Examples.scat_axesDiagram`). For the independent variables `c₀, c₁` over `ℚ`
and the full coefficient lattice `ℤ²`, this representative is a positive wall representative
whose grouped wall functions have coefficients in `ℕ[c₀, c₁]`
(`DirectedDiagram.Examples.exists_isPositiveWallRepresentative_axesDiagram`). This is the
scattering diagram of type `B₂` of Gross–Pandharipande–Siebert, *Quivers, curves, and the
tropical vertex*, Example 1.6 (arXiv:0902.0779v3), with `ℓ₁ = 1`, `ℓ₂ = 2` and coefficients.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram.Examples

open Module

local notation "ℕ²" => Basis.positiveDegrees (Basis.finTwoProd ℤ)
local notation "ρ" => AddMonoidHom.id (ℤ × ℤ)

/-- The coorientations `-e₂*` and `e₁*` of the horizontal and the vertical axis. -/
def axesNormal : Fin 2 → (ℤ × ℤ →+ ℤ) := ![-AddMonoidHom.snd ℤ ℤ, AddMonoidHom.fst ℤ ℤ]

/-- The horizontal axis is cooriented by `-e₂*`. -/
@[simp]
theorem axesNormal_zero (q : ℤ × ℤ) : axesNormal 0 q = -q.2 := by simp [axesNormal]

/-- The vertical axis is cooriented by `e₁*`. -/
@[simp]
theorem axesNormal_one (q : ℤ × ℤ) : axesNormal 1 q = q.1 := by simp [axesNormal]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The labels of the axes: the binomial label of `1 + c₀ z^{e₁}` with the normal `-e₂*` on the
horizontal axis, and the square of the binomial label of `1 + c₁ z^{e₂}` with the normal `e₁*` on
the vertical axis. -/
def axesLabel (c : Fin 2 → R) :
    Fin 2 → (ℕ²).completedBCHGroup (tropicalVertexGrading (R := R) ℕ² ρ) :=
  ![binomialLabel (n := ((1, 0) : ℤ × ℤ)) ℕ² ρ (axesNormal 0) (by simp) (by simp) (by simp) (c 0),
    binomialLabel (n := ((0, 1) : ℤ × ℤ)) ℕ² ρ (axesNormal 1) (by simp) (by simp) (by simp)
      (c 1) ^ 2]

/-- The ray factors of the labels of the axes are wall labels with the normals of the axes. -/
theorem rayFactor_axesLabel_mem_wallGroup (c : Fin 2 → R) (j : Fin 2) (w : SupportedRay ℕ²) :
    (ℕ²).rayFactor _ (axesLabel c j) w ∈
      (tropicalVertexWallSpaces (R := R) ℕ² ρ).wallGroup w (axesNormal j) := by
  let : HasUniqueDiv (ℤ × ℤ) := .of_isTorsionFree ℤ _
  fin_cases j
  · simp only [Fin.zero_eta, axesLabel, Matrix.cons_val_zero, binomialLabel_def]
    exact rayFactor_completedBCHExp_completedTropicalTangentField_mem_wallGroup _ _ _ _ w
  · -- The square of the label of `1 + c₁ z^{e₂}` lies on the ray through `e₂`.
    have hprim : TauCeti.IsPrimitive ((0, 1) : ℤ × ℤ) :=
      TauCeti.isPrimitive_def.mpr ⟨LinearMap.snd ℤ ℤ ℤ, rfl⟩
    let v : SupportedRay ℕ² := SupportedRay.ofMem (0, 1) (by simp) hprim
    have hv := SupportedRay.mem_rayDegrees_ofMem (d := ℕ²) (0, 1) (by simp) hprim
    simp only [Fin.mk_one, axesLabel, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    by_cases hw : v = w
    · subst hw
      rw [(ℕ²).rayFactor_eq_self _
        (pow_mem (binomialLabel_mem_completedRaySubgroup _ _ _ _ _ _ _ hv) 2)]
      exact pow_mem (binomialLabel_mem_wallGroup _ _ _ _ _ _ _ hv) 2
    · rw [(ℕ²).rayFactor_eq_one _
        (pow_mem (binomialLabel_mem_completedRaySubgroup _ _ _ _ _ _ _ hv) 2) hw]
      exact one_mem _

variable {latticeMap : ℤ × ℤ →+ ℝ × ℝ} (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The ray presentation of the labels of the axes on the hyperplanes `{y = 0}` and `{x = 0}`. -/
def axesDiagram (c : Fin 2 → R) : DirectedDiagram (d := ℕ²) h
    (tropicalVertexWallSpaces (R := R) ℕ² ρ)
    (Σ j, {w : SupportedRay ℕ² // axesNormal j (ρ w.generator) = 0}) :=
  ofHyperplaneRayFactors h axesNormal
    (fun j => by fin_cases j <;> exact fun he => by simpa using DFunLike.congr_fun he (1, 1))
    (fun _ => 0) (axesLabel c) (rayFactor_axesLabel_mem_wallGroup c) (by
      let : HasUniqueDiv (ℤ × ℤ) := .of_isTorsionFree ℤ _
      exact hasFiniteSupport_rayFactor_sigma _ _ _ fun _ => Set.toFinite _)

/-- The axes form a ray presentation of type `B₂` with the degrees `e₁, e₂` and the coefficients
`c₀, c₁`. -/
theorem isTypeB₂Presentation_axesDiagram (c : Fin 2 → R) :
    (axesDiagram h c).IsTypeB₂Presentation (axesLabel c) 0 1 (1, 0) (0, 1) (c 0) (c 1) where
  isRayFactorPresentation := isRayFactorPresentation_ofHyperplaneRayFactors ..
  eq_or_eq j := by fin_cases j <;> simp
  mem_monoid_fst := by simp
  mem_monoid_snd := by simp
  apply_fst_fst := by simp
  apply_snd_snd := by simp
  apply_fst_snd := by simp
  apply_snd_fst := by simp
  label_fst := by simp [axesLabel]
  label_snd := by simp [axesLabel]

/-- For arbitrary coefficients `c₀, c₁`, the scattering class of the axes with the labels of
`1 + c₀ z^{e₁}` and `(1 + c₁ z^{e₂})^2` is represented by the hexagon diagram, whose outgoing walls
`{x = y, y ≤ 0}` and `{2 x = y, y ≤ 0}` carry the labels of `(1 + c₀ c₁ z^{e₁ + e₂})^2` and
`1 + c₀ c₁^2 z^{e₁ + 2 e₂}`. -/
theorem scat_axesDiagram (c : Fin 2 → R) :
    (axesDiagram h c).Scat (isTypeB₂Presentation_axesDiagram h c).full =
      (isTypeB₂Presentation_axesDiagram h c).hexagonDiagram.toClass :=
  (isTypeB₂Presentation_axesDiagram h c).scat_eq_toClass_hexagonDiagram

open scoped Mei.TropicalVertexCoefficientAction

-- Named explicitly: an anonymous instance of the same type in another Examples file would get the
-- same automatic name.
/-- The quadrant monoid lies in the full coefficient lattice `ℤ²`. -/
local instance factQuadrantMonoidLeTopHexagon :
    Fact ((ℕ²).monoid ≤ (⊤ : AddSubmonoid (ℤ × ℤ))) :=
  ⟨le_top⟩

/-- For the independent variables `c₀, c₁` over `ℚ` and the full coefficient lattice `ℤ²`, the
scattering class of the axes with the labels of `1 + c₀ z^{e₁}` and `(1 + c₁ z^{e₂})^2` has a
consistent outgoing representative whose grouped wall functions `1 + c₀ z^{e₁}`,
`(1 + c₁ z^{e₂})^2`, `(1 + c₀ c₁ z^{e₁ + e₂})^2` and `1 + c₀ c₁^2 z^{e₁ + 2 e₂}` have coefficients
in `ℕ[c₀, c₁]`. -/
theorem exists_isPositiveWallRepresentative_axesDiagram :
    ∃ (κ : Type) (E : DirectedDiagram (d := ℕ²) h
        (tropicalVertexWallSpaces (R := MvPolynomial (Fin 2) ℚ) ℕ² ρ)
        ((Σ j, {w : SupportedRay ℕ² // axesNormal j (ρ w.generator) = 0}) ⊕ κ)),
      IsOutgoingCompletion (axesDiagram h MvPolynomial.X).wall E ∧
      E.toClass = (axesDiagram h MvPolynomial.X).Scat
        (isTypeB₂Presentation_axesDiagram h MvPolynomial.X).full ∧
      E.IsPositiveWallRepresentative
        ((TropicalVertexCoefficientAction.filtration (R := MvPolynomial (Fin 2) ℚ) ℕ²
          (⊤ : AddSubmonoid (ℤ × ℤ))).completedBCHAction ℕ²
          (tropicalVertexGrading (R := MvPolynomial (Fin 2) ℚ) ℕ² ρ))
        (AddMonoidAlgebra.mapRingHom (⊤ : AddSubmonoid (ℤ × ℤ))
          (MvPolynomial.map (σ := Fin 2) (Nat.castRingHom ℚ))).rangeS ρ :=
  -- The monomials `z^{-e₂}` and `z^{e₁}` are invertible, with `-e₂*(-e₂) = e₁*(e₁) = 1` and
  -- `e₁*(-e₂) = 0`.
  (isTypeB₂Presentation_axesDiagram h MvPolynomial.X).exists_isPositiveWallRepresentative_scat ⊤
    ρ _ ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩ ⟨MvPolynomial.X _, MvPolynomial.map_X _ _⟩
    ⟨(0, -1), trivial, trivial, by simp, by simp⟩ ⟨(1, 0), trivial, trivial, by simp⟩

end Mei.DirectedDiagram.Examples
