/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.UniversalEnveloping.Inner.Basic
public import Mei.Algebra.Lie.UniversalEnveloping.BCH.Completion
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Completed inner BCH actions are conjugation

Every completed BCH label acts on the degree-completed enveloping algebra by
conjugation with its canonical group-like unit. Thus the coefficient representation
and the homomorphism into enveloping units agree on arbitrary compatible families,
including Lie series with infinitely many nonzero homogeneous components.

The finite comparison uses the commutator action from
`UniversalEnvelopingAlgebra.InnerAction` and
`Mei.AlgFiltration.quotientExpLieAction_apply_eq_exp_mul_exp_neg`, which follows
Tau Ceti's adjoint exponential formula. The completed comparison uses the existing
finite projection laws for `completedBCHAction` and `completedBCHToGroupLike`.
No freeness, PBW, or injectivity assumption on the canonical Lie map is required.
-/

public section

open scoped UniversalEnvelopingAlgebra.InnerAction

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UniversalEnvelopingAlgebra.InnerAction

open Mei Mei.UniversalEnvelopingAlgebra

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "F" => degreeFiltration ℒ d.degree
  (fun n hn => d.eq_bot_of_degree_nonpos ℒ n (le_of_lt hn))

/-- Rational scalars on the enveloping algebra are induced from the coefficient ring. -/
local instance rationalCompletedInnerAlgebra : Algebra ℚ U :=
  Algebra.compHom _ (algebraMap ℚ R)

/-- At every cutoff, the inner exponential of a truncated Lie element is
conjugation by the finite exponential of its canonical enveloping image. -/
@[simp]
theorem truncatedExpLieAction_apply (k : ℕ) (x : d.truncatedLie ℒ k)
    (a : U ⧸ (F).ideal (k + 1)) :
    (F).truncatedExpLieAction d ℒ k x a =
      IsNilpotent.exp (truncatedLieToU d ℒ k x) * a *
        IsNilpotent.exp (-truncatedLieToU d ℒ k x) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ k).surjective_mkQ x
  simp only [LieIdeal.mkQ_apply, Mei.AlgFiltration.truncatedExpLieAction_mk,
    truncatedLieToU_mk]
  exact (F).quotientExpLieAction_apply_eq_exp_mul_exp_neg d ℒ k (lie_eq x)
    (ι_mem_degreeFiltration_one ℒ d.degree
      (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn) x) a

variable [LieAlgebra ℚ L] [IsScalarTower ℚ R L]

/-- The finite inner BCH action is conjugation by the canonical enveloping unit. -/
theorem truncatedBCHAction_apply (k : ℕ) (g : BCHGroup (d.truncatedLie ℒ k))
    (a : U ⧸ (F).ideal (k + 1)) :
    (F).truncatedBCHAction d ℒ k g a =
      (truncatedBCHToUnits d ℒ k g : U ⧸ (F).ideal (k + 1)) * a *
        (truncatedBCHToUnits d ℒ k g⁻¹ : U ⧸ (F).ideal (k + 1)) := by
  simp only [Mei.AlgFiltration.truncatedBCHAction_apply,
    truncatedExpLieAction_apply, coe_truncatedBCHToUnits, BCHGroup.log_inv, map_neg]

/-- The inner representation of every completed BCH label is conjugation by its
canonical completed group-like unit. -/
@[simp]
theorem completedBCHAction_apply (g : d.completedBCHGroup ℒ) (a : (F).completion) :
    (F).completedBCHAction d ℒ g a =
      ((completedBCHToGroupLike d ℒ g).val : (F).completion) * a *
        ((completedBCHToGroupLike d ℒ g⁻¹).val : (F).completion) := by
  apply (F).completion_ext
  intro k
  rw [Mei.AlgFiltration.projection_completedBCHAction, map_mul, map_mul,
    projection_completedBCHToGroupLike, projection_completedBCHToGroupLike]
  have h := truncatedBCHAction_apply d ℒ k
    (CompletedGroup.projection k g) ((F).projection k a)
  rw [(F).truncatedBCHAction_apply d ℒ k (CompletedGroup.projection k g)] at h
  simp only [map_inv] at h ⊢
  -- The categorical tower object and its concrete BCH group carry the same operations.
  convert h using 1
  rfl

/-- In completed Lie coordinates, the inner action is conjugation by the completed
exponential of the canonical Lie image, with inverse given by its negative. -/
theorem completedBCHAction_exp_apply (x : d.completedLie ℒ) (a : (F).completion) :
    (F).completedBCHAction d ℒ (d.completedBCHExp ℒ x) a =
      (F).completedExp ⟨completedLieToU d ℒ x,
        completedLieToU_mem_completionIdeal_one d ℒ x⟩ * a *
      (F).completedExp (-⟨completedLieToU d ℒ x,
        completedLieToU_mem_completionIdeal_one d ℒ x⟩) := by
  rw [completedBCHAction_apply]
  simp only [coe_completedBCHToGroupLike, Equiv.symm_apply_apply,
    PositiveDegrees.completedBCHExp_symm_inv, map_neg]
  congr 2

end UniversalEnvelopingAlgebra.InnerAction
