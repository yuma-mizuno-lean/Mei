/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.BCH.Completion
public import Mei.Algebra.Lie.Graded.Completion

/-!
# Exponential coordinates on completed BCH groups

Levelwise exponential and logarithm identify the compatible-family Lie completion
with the completed BCH group as sets. This comparison lets Lie maps out of the
completion describe group representations in exponential coordinates, without
requiring the original Lie algebra to be nilpotent.

The carriers and transition laws are those of `LieIdeal.completion` and
`Mei.CompletedGroup`; the finite coordinate maps are `Mei.BCHGroup.exp` and
`Mei.BCHGroup.log`.
-/

public section

namespace Mei.PositiveDegrees

open CategoryTheory Opposite

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "π" => LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ)

/-- Levelwise exponential identifies the Lie and BCH group completions as sets. -/
noncomputable def completedBCHExp : d.completedLie ℒ ≃ d.completedBCHGroup ℒ where
  toFun x := ⟨fun k => BCHGroup.exp (π k x), (mem_completedGroup_iff _ _).mpr (by
    intro k l h
    -- The categorical tower map conceals the concrete BCH quotient homomorphism.
    change (d.truncationMap ℒ h).bchGroupMap (BCHGroup.exp (π l x)) =
      BCHGroup.exp (π k x)
    rw [LieHom.bchGroupMap_exp, truncationMap_def,
      LieIdeal.factor_completionProjection])⟩
  invFun g := ⟨fun k =>
    BCHGroup.log (L := d.truncatedLie ℒ k.unop) (CompletedGroup.projection k.unop g),
    (ModuleFiltration.mem_completionSubmodule_iff _ _).mpr (by
      intro k l h
      rw [LieIdeal.completionFiltration_transition, LieHom.coe_toLinearMap]
      have hg := congrArg (BCHGroup.log (L := d.truncatedLie ℒ k))
        (CompletedGroup.map_projection k l h g)
      -- Rewrite the categorical arrow at its concrete quotient group type.
      change BCHGroup.log (L := d.truncatedLie ℒ k) ((d.truncationMap ℒ h).bchGroupMap
        (CompletedGroup.projection l g)) =
          BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) at hg
      simpa only [truncationMap_def] using
        ((d.truncationMap ℒ h).log_bchGroupMap (CompletedGroup.projection l g)).symm.trans hg)⟩
  left_inv x := by
    apply ModuleFiltration.completion_ext
    intro k
    simp only [ModuleFiltration.projection_mk, CompletedGroup.projection_apply,
      BCHGroup.log_exp, LieIdeal.completionProjection_apply]
  right_inv g := by
    apply CompletedGroup.ext
    intro k
    simp only [CompletedGroup.projection_apply, LieIdeal.completionProjection_apply,
      ModuleFiltration.projection_mk]
    exact BCHGroup.exp_log (L := d.truncatedLie ℒ k) (g.val k)

/-- Projection of the completed exponential is the finite exponential coordinate. -/
@[simp]
theorem projection_completedBCHExp (k : ℕ) (x : d.completedLie ℒ) :
    CompletedGroup.projection k (d.completedBCHExp ℒ x) = BCHGroup.exp (π k x) := by
  rw [CompletedGroup.projection_apply, completedBCHExp]
  rfl

/-- Projection of the inverse coordinate map is the logarithm at the same cutoff. -/
@[simp]
theorem completionProjection_completedBCHExp_symm (k : ℕ) (g : d.completedBCHGroup ℒ) :
    π k ((d.completedBCHExp ℒ).symm g) =
      BCHGroup.log (L := d.truncatedLie ℒ k) (CompletedGroup.projection k g) := by
  rw [LieIdeal.completionProjection_apply, completedBCHExp]
  exact ModuleFiltration.projection_mk _ _ _ k

/-- Zero is the exponential coordinate of the identity completed group element. -/
@[simp]
theorem completedBCHExp_zero : d.completedBCHExp ℒ 0 = 1 := by
  apply CompletedGroup.ext
  intro k
  rw [projection_completedBCHExp, map_zero, BCHGroup.exp_zero]
  exact ((CompletedGroup.projection (F := d.groupTower ℒ) k).map_one).symm

/-- Negation of a completed Lie coordinate gives inversion in the completed group. -/
@[simp]
theorem completedBCHExp_neg (x : d.completedLie ℒ) :
    d.completedBCHExp ℒ (-x) = (d.completedBCHExp ℒ x)⁻¹ := by
  apply CompletedGroup.ext
  intro k
  rw [projection_completedBCHExp, map_neg, BCHGroup.exp_neg]
  exact (congrArg Inv.inv (d.projection_completedBCHExp ℒ k x).symm).trans
    ((CompletedGroup.projection k).map_inv (d.completedBCHExp ℒ x)).symm

end Mei.PositiveDegrees
