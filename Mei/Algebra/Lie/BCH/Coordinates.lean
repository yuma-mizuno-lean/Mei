/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.Graded.Completion

/-!
# Logarithmic coordinates on completed BCH groups

Finite BCH logarithms identify compatible group elements with compatible Lie elements.
The resulting equivalence retains the existing group and module completion carriers.
It provides coordinates for comparison with associative exponential series without
requiring the original Lie algebra to be nilpotent.

The construction uses `BCHGroup.exp`, `LieHom.log_bchGroupMap`, and the compatibility
criteria for `CompletedGroup` and `LieIdeal.completion`.
-/

public section

namespace Mei.PositiveDegrees

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "π" => LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- Levelwise logarithms identify the completed BCH group with the completed Lie algebra
as sets. -/
noncomputable def completedLogEquiv : d.completedBCHGroup ℒ ≃ d.completedLie ℒ where
  toFun g := ⟨fun k => BCHGroup.log (CompletedGroup.projection k.unop g), by
    apply (ModuleFiltration.mem_completionSubmodule_iff _ _).mpr
    intro k l h
    rw [LieIdeal.completionFiltration_transition, LieHom.coe_toLinearMap]
    have hc : (d.truncationMap ℒ h).bchGroupMap (CompletedGroup.projection l g) =
        CompletedGroup.projection k g := CompletedGroup.map_projection k l h g
    simpa only [truncationMap_def] using
      ((d.truncationMap ℒ h).log_bchGroupMap _).symm.trans (congrArg BCHGroup.log hc)⟩
  invFun x := ⟨fun k => BCHGroup.exp (π k x), by
    apply (mem_completedGroup_iff _ _).mpr
    intro k l h
    -- Reveal the concrete BCH quotient groups behind the functor objects.
    change (d.truncationMap ℒ h).bchGroupMap (BCHGroup.exp (π l x)) = BCHGroup.exp (π k x)
    rw [LieHom.bchGroupMap_exp, truncationMap_def, LieIdeal.factor_completionProjection]⟩
  left_inv g := by
    apply CompletedGroup.ext
    intro k
    simp only [CompletedGroup.projection_apply, LieIdeal.completionProjection_apply,
      ModuleFiltration.projection_mk]
    exact BCHGroup.exp_log (L := d.truncatedLie ℒ k) _
  right_inv x := by
    apply ModuleFiltration.completion_ext
    intro k
    simp only [ModuleFiltration.projection_mk, CompletedGroup.projection_apply,
      LieIdeal.completionProjection_apply, BCHGroup.log_exp]

/-- A projection of the completed logarithm is the logarithm of the group projection. -/
@[simp]
theorem projection_completedLogEquiv (k : ℕ) (g : d.completedBCHGroup ℒ) :
    π k (d.completedLogEquiv ℒ g) = BCHGroup.log (CompletedGroup.projection k g) := by
  simp only [completedLogEquiv, Equiv.coe_fn_mk, LieIdeal.completionProjection_apply,
    ModuleFiltration.projection_mk]

/-- The inverse coordinate map exponentiates each Lie projection. -/
@[simp]
theorem projection_completedLogEquiv_symm (k : ℕ) (x : d.completedLie ℒ) :
    CompletedGroup.projection k ((d.completedLogEquiv ℒ).symm x) =
      BCHGroup.exp (π k x) := by
  rw [CompletedGroup.projection_apply, completedLogEquiv]
  rfl

/-- The identity group element has zero completed logarithm. -/
@[simp]
theorem completedLogEquiv_one : d.completedLogEquiv ℒ 1 = 0 := by
  apply ModuleFiltration.completion_ext
  intro k
  rw [← LieIdeal.completionProjection_apply, projection_completedLogEquiv, map_one, map_zero]
  exact BCHGroup.log_one (L := d.truncatedLie ℒ k)

/-- Inversion negates the completed logarithm. -/
@[simp]
theorem completedLogEquiv_inv (g : d.completedBCHGroup ℒ) :
    d.completedLogEquiv ℒ g⁻¹ = -d.completedLogEquiv ℒ g := by
  apply ModuleFiltration.completion_ext
  intro k
  have hk : π k (d.completedLogEquiv ℒ g⁻¹) = π k (-d.completedLogEquiv ℒ g) := by
    rw [map_neg, projection_completedLogEquiv, projection_completedLogEquiv, map_inv]
    exact BCHGroup.log_inv (L := d.truncatedLie ℒ k) _
  simpa only [LieIdeal.completionProjection_apply] using hk

/-- The zero completed Lie element exponentiates to the group identity. -/
@[simp]
theorem completedLogEquiv_symm_zero : (d.completedLogEquiv ℒ).symm 0 = 1 := by
  apply (d.completedLogEquiv ℒ).injective
  simp

/-- Negating a completed Lie coordinate inverts its exponential. -/
@[simp]
theorem completedLogEquiv_symm_neg (x : d.completedLie ℒ) :
    (d.completedLogEquiv ℒ).symm (-x) = ((d.completedLogEquiv ℒ).symm x)⁻¹ := by
  apply (d.completedLogEquiv ℒ).injective
  simp

end Mei.PositiveDegrees
