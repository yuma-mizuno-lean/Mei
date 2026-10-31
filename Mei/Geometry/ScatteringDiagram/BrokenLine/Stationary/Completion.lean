/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.BrokenLine.Stationary
public import Mei.Geometry.ScatteringDiagram.BrokenLine.Itineraries.Completion

/-!
# Completed stationary evaluation

For stationary incoming coefficients, the compatible full BCH ray sums are the
canonical image of the incoming coefficient in the shifted completion. This
includes zero coefficients and inputs whose images vanish at individual cutoffs.
Only the incoming spatial direction must vanish; other degree directions and
all wall labels remain unrestricted.

We apply `cutoffDecoratedEvaluation_of_velocity_eq_zero` to the projections of
`PositiveDegrees.completedBCHCutoffEvaluation`. The resulting constant contribution
is the completed version of the theta convention following equation (15) in
Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*
(arXiv:1503.06183v5).
-/

public noncomputable section

namespace Mei.PositiveDegrees

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

/-- The full completed evaluation of a stationary incoming coefficient is its
canonical image in the shifted completion, for arbitrary completed BCH labels. -/
@[simp]
theorem completedBCHCutoffEvaluation_of_velocity_eq_zero
    (g : J → d.completedBCHGroup ℒ) (a : shiftedGrading ℳ d.monoid p 0)
    (hv : v 0 = 0) (hC : Q ∈ C) (hW : ∀ j, Q ∉ W j) (hS : ∀ j, Q ∉ S j) :
    d.completedBCHCutoffEvaluation ℒ ℳ p v f c ε P W S C Q g a =
      (d.shiftedLieFiltration ℒ ℳ p).of a := by
  apply (d.shiftedLieFiltration ℒ ℳ p).completion_ext
  intro k
  rw [projection_completedBCHCutoffEvaluation, ModuleFiltration.projection_of]
  exact cutoffDecoratedEvaluation_of_velocity_eq_zero hv hC hW hS

end Mei.PositiveDegrees
