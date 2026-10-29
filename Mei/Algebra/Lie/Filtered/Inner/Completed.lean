/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Inner.Basic
public import Mei.Algebra.Lie.Filtered.Inner.Map
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Completed inner actions as conjugations

A linear map from a positively graded Lie algebra into a filtered associative
algebra extends to completions when it carries every degree cutoff into the
corresponding ideal. Positivity puts its completed image in the first completion
ideal. If the original Lie action is the commutator with this map, every completed
BCH group element acts by conjugation with the completed exponential of its
completed logarithmic image.

The coefficient extension requires only a filtration-preserving linear map.
The conjugation formulas additionally require the original Lie action to be the
commutator with that map. No faithfulness, separatedness, finite rank, or
injectivity hypothesis is required.
-/

public section

noncomputable section

namespace Mei.AlgFiltration

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (F : AlgFiltration A)

variable {N L : Type*} [AddCommMonoid N] [LieRing L] [LieAlgebra R L]
  [DecidableEq N] (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  (j : L →ₗ[R] A)
  (hj : ∀ k, d.degreeSubmodule ℒ k ≤ ((F.ideal (k + 1)).restrictScalars R).comap j)

variable [LieRingModule L A] [LieModule R L A]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)] [IsDerivationAction L A]
  [Algebra ℚ A]
  (hinner : ∀ x a, ⁅x, a⁆ = j x * a - a * j x)

include hinner in
/-- At each order, a truncated inner action is conjugation by the exponential of its image. -/
theorem truncatedExpLieAction_eq_inner (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : A ⧸ F.ideal (k + 1)) :
    F.truncatedExpLieAction d ℒ k x a =
      IsNilpotent.exp (F.truncatedInnerMap d ℒ j hj k x) * a *
        IsNilpotent.exp (-F.truncatedInnerMap d ℒ j hj k x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  rw [LieIdeal.mkQ_apply, truncatedExpLieAction_mk]
  simpa only [LieIdeal.mkQ_apply, truncatedInnerMap_mk] using
    F.quotientExpLieAction_apply_eq_exp_mul_exp_neg d ℒ k (hinner x)
      (F.innerMap_mem_one d ℒ j hj x) a

variable [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

include hinner in
/-- Arbitrary completed Lie elements act by conjugation on arbitrary completed coefficients. -/
theorem completedBCHAction_exp_eq_inner (x : d.completedLie ℒ) (a : F.completion) :
    F.completedBCHAction d ℒ (d.completedBCHExp ℒ x) a =
      F.completedExp (F.completedInnerElement d ℒ j hj x) * a *
        F.completedExp (-F.completedInnerElement d ℒ j hj x) := by
  apply F.completion_ext
  intro k
  simp only [projection_completedBCHAction, PositiveDegrees.projection_completedBCHExp,
    BCHGroup.log_exp, map_mul, projection_completedExp, Submodule.coe_neg,
    coe_completedInnerElement, map_neg, projection_completedInnerMap]
  exact F.truncatedExpLieAction_eq_inner d ℒ j hj hinner k _ _

include hinner in
/-- Every completed BCH label acts by the exponential of its completed logarithmic image. -/
theorem completedBCHAction_eq_inner (g : d.completedBCHGroup ℒ) (a : F.completion) :
    F.completedBCHAction d ℒ g a =
      F.completedExp (F.completedInnerElement d ℒ j hj ((d.completedBCHExp ℒ).symm g)) *
        a * F.completedExp
          (-F.completedInnerElement d ℒ j hj ((d.completedBCHExp ℒ).symm g)) := by
  simpa only [Equiv.apply_symm_apply] using
    F.completedBCHAction_exp_eq_inner d ℒ j hj hinner ((d.completedBCHExp ℒ).symm g) a

end Mei.AlgFiltration
