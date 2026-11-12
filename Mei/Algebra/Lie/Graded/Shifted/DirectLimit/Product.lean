/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.DirectLimit
public import Mei.Algebra.Lie.Graded.Shifted.Product
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Action

/-!
# Global completed BCH actions preserve products

A graded derivation action descends to multiplication on global coefficients.
The coefficient algebra may be noncommutative, and only a graded multiplication
is required: the original unit need not belong to the degree-zero piece.

The shifted coefficient setting is motivated by Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §2.1 and Definition 2.10
([arXiv:1503.06183v5](https://arxiv.org/abs/1503.06183v5)).
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ R L A : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [Ring A] [Algebra R A] [LieRingModule L A] [LieModule R L A]
  [IsDerivationAction L A] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (𝒜 : Γ → Submodule R A)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition 𝒜] [SetLike.GradedBracket ℒ 𝒜]
  [SetLike.GradedMul 𝒜]

/-- Completed BCH labels preserve the global product without a graded unit. -/
@[simp]
theorem shiftedDirectLimitBCHAction_map_mul (g : d.completedBCHGroup ℒ)
    (x y : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitBCHAction ℒ 𝒜 g (x * y) =
      d.shiftedDirectLimitBCHAction ℒ 𝒜 g x * d.shiftedDirectLimitBCHAction ℒ 𝒜 g y := by
  rw [shiftedDirectLimitBCHAction_eq_shiftedDirectLimitAction]
  exact d.shiftedDirectLimitAction_map_mul 𝒜
    (fun p => (d.shiftedLieFiltration ℒ 𝒜 p).completedBCHAction d ℒ)
    (d.shiftedCompletedInclusion_completedBCHAction ℒ 𝒜)
    (d.completedBCHAction_shiftedCompletionMul ℒ 𝒜) g x y

end TauCeti.PositiveDegrees
