/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Pentagon.Blocks

/-!
# Two commuting blocks of type `A₂` in `ℤ⁴`

Take `Γ = Λ = ℤ⁴`, `ρ = id` and the orthant `ℕ⁴` with the coordinate-sum degree. The four
coordinate hyperplanes `{x₂ = 0}`, `{x₁ = 0}`, `{x₄ = 0}`, `{x₃ = 0}`, cooriented by `-e₂*`,
`e₁*`, `-e₄*`, `e₃*` (`DirectedDiagram.Examples.blocksNormal`), with the wall functions
`1 + c_j z^{e_j}` for arbitrary coefficients `c_j` (`DirectedDiagram.Examples.blocksLabel`), form
a ray presentation (`DirectedDiagram.Examples.blocksInput`) of type `A₂` in the two blocks
`(0, 1)` and `(2, 3)` (`DirectedDiagram.Examples.isTypeA₂BlocksPresentation_blocksInput`): within a
block, `-e₂*(e₂) = -1` and `e₁*(e₁) = 1`, and the normals of one block vanish on the degrees of the
other, so labels of distinct blocks commute although their walls cross. Hence its scattering class
is represented by the blocks diagram, with the two outgoing walls `{x₁ = x₂, x₂ ≤ 0}` and
`{x₃ = x₄, x₄ ≤ 0}` carrying the binomial labels of `1 + c₀ c₁ z^{e₁ + e₂}` and
`1 + c₂ c₃ z^{e₃ + e₄}` (`DirectedDiagram.Examples.scat_blocksInput`). This is the product of two
copies of the scattering diagram of type `A₂` of Gross–Pandharipande–Siebert, *Quivers, curves,
and the tropical vertex*, Example 1.6 (arXiv:0902.0779v3), with coefficients.
-/

public section

noncomputable section

namespace Mei.DirectedDiagram.Examples

open Module

local notation "ℤ⁴" => Fin 4 → ℤ
local notation "ℕ⁴" => Basis.positiveDegrees (Pi.basisFun ℤ (Fin 4))

/-- The coorientations `-e₂*`, `e₁*`, `-e₄*`, `e₃*` of the four coordinate hyperplanes. -/
def blocksNormal : Fin 4 → (ℤ⁴ →+ ℤ) :=
  ![-Pi.evalAddMonoidHom (fun _ => ℤ) 1, Pi.evalAddMonoidHom (fun _ => ℤ) 0,
    -Pi.evalAddMonoidHom (fun _ => ℤ) 3, Pi.evalAddMonoidHom (fun _ => ℤ) 2]

/-- The coorientations are `-e₂*`, `e₁*`, `-e₄*`, `e₃*`. -/
@[simp]
theorem blocksNormal_apply (j : Fin 4) (x : ℤ⁴) :
    blocksNormal j x = ![-x 1, x 0, -x 3, x 2] j := by
  fin_cases j <;> simp [blocksNormal]

/-- The coorientation `μ_j` pairs with the basis vector `e_k` as listed. -/
theorem blocksNormal_basisFun (j k : Fin 4) :
    blocksNormal j (Pi.basisFun ℤ (Fin 4) k) =
      ![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]] j k := by
  fin_cases j <;> fin_cases k <;> simp

/-- The basis vector `e_j` is tangent to the hyperplane `j`. -/
theorem blocksNormal_basisFun_self (j : Fin 4) : blocksNormal j (Pi.basisFun ℤ (Fin 4) j) = 0 := by
  fin_cases j <;> simp

/-- The coorientations are nonzero. -/
theorem blocksNormal_ne_zero (j : Fin 4) : blocksNormal j ≠ 0 := fun he => by
  have h₁ := congrArg (fun μ : ℤ⁴ →+ ℤ => μ (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 +
    Pi.single 3 1)) he
  fin_cases j <;> simp at h₁

/-- The supported ray through the basis vector `e_j`. -/
def blocksRay (j : Fin 4) : SupportedRay ℕ⁴ :=
  SupportedRay.ofMem _ ((Pi.basisFun ℤ (Fin 4)).mem_positiveDegrees_monoid_self j)
    ((Pi.basisFun ℤ (Fin 4)).isPrimitive j)

/-- The basis vector `e_j` lies on the ray `blocksRay j`. -/
theorem basisFun_mem_blocksRay_rayDegrees (j : Fin 4) :
    Pi.basisFun ℤ (Fin 4) j ∈ (blocksRay j).rayDegrees :=
  SupportedRay.mem_rayDegrees_ofMem ..

variable {R : Type*} [CommRing R] [Algebra ℚ R] (c : Fin 4 → R)

local notation "ℒ" => tropicalVertexGrading (R := R) ℕ⁴ (AddMonoidHom.id ℤ⁴)
local notation "H" => tropicalVertexWallSpaces (R := R) ℕ⁴ (AddMonoidHom.id ℤ⁴)

/-- The binomial label of `1 + c_j z^{e_j}` with the normal `μ_j`. -/
def blocksLabel (j : Fin 4) : ℕ⁴.completedBCHGroup ℒ :=
  binomialLabel ℕ⁴ (AddMonoidHom.id ℤ⁴) (blocksNormal j)
    ((Pi.basisFun ℤ (Fin 4)).mem_positiveDegrees_monoid_self j)
    ((Pi.basisFun ℤ (Fin 4)).ne_zero j) (blocksNormal_basisFun_self j) (c j)

/-- The ray factors of the label of `1 + c_j z^{e_j}` are trivial off the ray through `e_j`. -/
theorem rayFactor_blocksLabel_of_ne {j : Fin 4} {w : SupportedRay ℕ⁴} (hw : w ≠ blocksRay j) :
    ℕ⁴.rayFactor ℒ (blocksLabel c j) w = 1 :=
  let : HasUniqueDiv ℤ⁴ := .of_isTorsionFree ℤ _
  rayFactor_binomialLabel_of_ne _ _ _ _ _ _ _ (basisFun_mem_blocksRay_rayDegrees j) hw

/-- The ray factor of the label of `1 + c_j z^{e_j}` on the ray `w` is a wall label of `w` with the
normal `μ_j`. -/
theorem rayFactor_blocksLabel_mem_wallGroup (j : Fin 4) (w : SupportedRay ℕ⁴) :
    ℕ⁴.rayFactor ℒ (blocksLabel c j) w ∈ (H).wallGroup w (blocksNormal j) := by
  by_cases hw : w = blocksRay j
  · subst hw
    rw [blocksLabel, rayFactor_binomialLabel_self _ _ _ _ _ _ _
      (basisFun_mem_blocksRay_rayDegrees j)]
    exact binomialLabel_mem_wallGroup _ _ _ _ _ _ _ (basisFun_mem_blocksRay_rayDegrees j)
  · rw [rayFactor_blocksLabel_of_ne c hw]
    exact one_mem _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {latticeMap : ℤ⁴ →+ V}
  (h : TauCeti.Toric.IsIntegralLattice latticeMap)

/-- The ray presentation of the wall functions `1 + c_j z^{e_j}` on the four coordinate
hyperplanes `{μ_j = 0}`. -/
def blocksInput : DirectedDiagram (d := ℕ⁴) h H
    (Σ j, {w : SupportedRay ℕ⁴ // blocksNormal j (AddMonoidHom.id ℤ⁴ w.generator) = 0}) :=
  ofHyperplaneRayFactors h blocksNormal blocksNormal_ne_zero 0 (blocksLabel c)
    (rayFactor_blocksLabel_mem_wallGroup c) (by
      let : HasUniqueDiv ℤ⁴ := .of_isTorsionFree ℤ _
      exact hasFiniteSupport_rayFactor_sigma _ _ _ fun _ => Set.toFinite _)

/-- The walls of distinct blocks have commuting labels: the normals of one block vanish on the
degrees of the other, and all other walls are trivial. -/
theorem commute_blocksInput_label
    (x y : Σ j, {w : SupportedRay ℕ⁴ // blocksNormal j (AddMonoidHom.id ℤ⁴ w.generator) = 0})
    (hxy : ¬ ∃ b, (x.1 = ![0, 2] b ∨ x.1 = ![1, 3] b) ∧ (y.1 = ![0, 2] b ∨ y.1 = ![1, 3] b)) :
    Commute ((blocksInput c h).wall x).label ((blocksInput c h).wall y).label := by
  obtain ⟨j, w, hw₀⟩ := x
  obtain ⟨k, v, hv₀⟩ := y
  by_cases hw : w = blocksRay j
  swap
  · rw [blocksInput, ofHyperplaneRayFactors_label, rayFactor_blocksLabel_of_ne c hw]
    exact Commute.one_left _
  by_cases hv : v = blocksRay k
  swap
  · rw [blocksInput, ofHyperplaneRayFactors_label (x := ⟨k, v, _⟩),
      rayFactor_blocksLabel_of_ne c hv]
    exact Commute.one_right _
  subst hw hv
  refine (H).commute_of_mem_wallGroup_of_apply_eq_zero ?_ ?_ ((blocksInput c h).wall _).label_mem
    ((blocksInput c h).wall _).label_mem <;>
  · simp only [blocksInput, ofHyperplaneRayFactors_normal, ofHyperplaneRayFactors_ray, blocksRay,
      SupportedRay.generator_ofMem, AddMonoidHom.id_apply, blocksNormal_basisFun]
    simp only [Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, not_or,
      not_and_or] at hxy
    fin_cases j <;> fin_cases k <;> simp_all

/-- The four coordinate hyperplanes with the wall functions `1 + c_j z^{e_j}` form a ray
presentation of type `A₂` in the two blocks `(0, 1)` and `(2, 3)`. -/
theorem isTypeA₂BlocksPresentation_blocksInput :
    (blocksInput c h).IsTypeA₂BlocksPresentation (blocksLabel c) ![0, 2] ![1, 3]
      (fun b => Pi.basisFun ℤ (Fin 4) (![0, 2] b)) (fun b => Pi.basisFun ℤ (Fin 4) (![1, 3] b))
      (fun b => c (![0, 2] b)) (fun b => c (![1, 3] b)) where
  isRayFactorPresentation := isRayFactorPresentation_ofHyperplaneRayFactors ..
  injective := by decide
  commute := commute_blocksInput_label c h
  mem_monoid_fst _ := (Pi.basisFun ℤ (Fin 4)).mem_positiveDegrees_monoid_self _
  mem_monoid_snd _ := (Pi.basisFun ℤ (Fin 4)).mem_positiveDegrees_monoid_self _
  apply_fst_fst b := by fin_cases b <;> simp
  apply_snd_snd b := by fin_cases b <;> simp
  apply_fst_snd b := by fin_cases b <;> simp
  apply_snd_fst b := by fin_cases b <;> simp
  label_fst _ := by rw [blocksLabel]
  label_snd _ := by rw [blocksLabel]

/-- For arbitrary coefficients `c_j`, the scattering class of the four coordinate hyperplanes with
the wall functions `1 + c_j z^{e_j}` is represented by the blocks diagram, whose outgoing walls
`{x₁ = x₂, x₂ ≤ 0}` and `{x₃ = x₄, x₄ ≤ 0}` carry the binomial labels of
`1 + c₀ c₁ z^{e₁ + e₂}` and `1 + c₂ c₃ z^{e₃ + e₄}`. -/
theorem scat_blocksInput :
    (blocksInput c h).Scat (isTypeA₂BlocksPresentation_blocksInput c h).full =
      (isTypeA₂BlocksPresentation_blocksInput c h).blocksDiagram.toClass :=
  (isTypeA₂BlocksPresentation_blocksInput c h).scat_eq_toClass_blocksDiagram

end Mei.DirectedDiagram.Examples
