/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Component
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# The leading component of a completed shifted action

A positive Lie action raises the relative coefficient filtration. Consequently
its completed BCH action preserves the relative-degree-zero component of every
shifted coefficient. That component depends only on the order-zero quotient,
on which every positive Lie action vanishes. No faithfulness assumption on the
action or separatedness assumption on the original coefficient module is needed.

The shifted coefficient completion is the one used in Travis Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, §2.1
(arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L M : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)

/-- Completed BCH actions preserve the leading homogeneous component of any shifted
coefficient, without restricting the other components or the ambient shift. -/
@[simp]
theorem shiftedHomogeneousComponent_completedBCHAction (g : d.completedBCHGroup ℒ)
    (x : d.ShiftedCoefficients ℳ p) :
    d.shiftedHomogeneousComponent ℳ p p
        ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g x) =
      d.shiftedHomogeneousComponent ℳ p p x := by
  let g0 : BCHGroup (d.truncatedLie ℒ 0) := CompletedGroup.projection 0 g
  have ha : (d.shiftedLieFiltration ℒ ℳ p).projection 0
      ((d.shiftedLieFiltration ℒ ℳ p).completedBCHAction d ℒ g x) =
      (d.shiftedLieFiltration ℒ ℳ p).projection 0 x :=
    ((d.shiftedLieFiltration ℒ ℳ p).projection_completedBCHAction d ℒ g x 0).trans
      ((d.shiftedLieFiltration ℒ ℳ p).truncatedBCHAction_zero d ℒ g0 _)
  exact (d.shiftedHomogeneousComponent_eq ℳ p p 0 (by simp) _).trans
    ((congrArg (d.shiftedQuotientComponent ℳ p p 0 (by simp)) ha).trans
      (d.shiftedHomogeneousComponent_eq ℳ p p 0 (by simp) x).symm)

end Mei.PositiveDegrees
