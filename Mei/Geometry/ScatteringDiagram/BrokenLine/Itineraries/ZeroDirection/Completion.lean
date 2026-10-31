/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.ZeroDirection.Quotient
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Completion

/-!
# Stationary components of completed BCH ray evaluations

The completed weighted evaluation has zero component in every stationary
absolute degree different from its incoming degree. Here the spatial velocity
of relative degree `n` is the velocity of absolute degree `p + n`. This proves
vanishing for the actual sum over all encounter itineraries in the shifted
completion. Stationary incoming coefficients and nonzero
shifts with unchanged spatial velocity remain permitted.

We combine the finite vanishing theorem
`PositiveDegrees.shiftedQuotientComponent_cutoffDecoratedEvaluation_eq_zero_of_velocity_eq_zero`
with `PositiveDegrees.projection_completedBCHCutoffEvaluation`.
For the stationary-output case of the broken-line recursion, see Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
§3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

section BCH

variable {Γ : Type} {R L M V J K : Type*}
  [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L)
  (ℳ : Γ → Submodule R M) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition ℳ] [SetLike.GradedBracket ℒ ℳ] (p : Γ)
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite J]
  (v : Γ → V) (f : J → V →L[ℝ] ℝ) (c : J → ℝ)
  (ε : J → SignType) (P W : J → Set V) (S : K → Set V) (C : Set V) (Q : V)

/-- The stationary-output vanishing law holds for homogeneous components of
the completed evaluation itself, without choosing a finite cutoff in the API. -/
@[simp]
theorem shiftedHomogeneousComponent_completedBCHCutoffEvaluation_eq_zero_of_velocity_eq_zero
    (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0)
    {q : Γ} (hq : v q = 0) (hne : q ≠ p) :
    d.shiftedHomogeneousComponent ℳ p q
      (d.completedBCHCutoffEvaluation ℒ ℳ p (fun n => v (p + n))
        f c ε P W S C Q g a) = 0 := by
  rw [d.shiftedHomogeneousComponent_eq ℳ p q (d.degree (q - p)).toNat
    (Int.self_le_toNat _), d.projection_completedBCHCutoffEvaluation]
  exact d.shiftedQuotientComponent_cutoffDecoratedEvaluation_eq_zero_of_velocity_eq_zero
    ℳ p v f c ε P W S C Q _ _ _ hq hne _

end BCH

end Mei.PositiveDegrees
