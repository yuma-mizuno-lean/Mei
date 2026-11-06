/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Operators.Basic
public import Mei.Geometry.ScatteringDiagram.WallSpace.Action

/-!
# Wall annihilation for operator coefficients

Postcomposition by a tangent wall element kills a homogeneous linear family
because it kills every output. Thus the finite-support operator representation
inherits wall annihilation, with no positivity or nilpotence hypothesis.
-/

public noncomputable section

namespace Mei.GradedOperators

variable {R H M Γ L Λ : Type*} [CommRing R] [AddCommGroup H] [Module R H]
  [AddCommGroup M] [Module R M] [AddCommMonoid Γ] [DecidableEq Γ]
  (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [DirectSum.Decomposition ℒ] [SetLike.GradedBracket ℒ ℳ]
  [AddCommMonoid Λ] {ρ : Γ →+ Λ} (W : DirectedWallSpaces ρ ℒ)
  [IsWallAnnihilating W ℳ]

/-- Tangent wall elements annihilate operator coefficients pointwise. -/
instance lieGrading_isWallAnnihilating :
    IsWallAnnihilating W (lieGrading (H := H) ℳ ℒ) where
  lie_eq_zero hx hf hm := by
    apply Subtype.ext
    ext a
    simp only [LieSubmodule.coe_bracket, LieHom.lie_apply, trivial_lie_zero,
      map_zero, sub_zero]
    exact IsWallAnnihilating.lie_eq_zero (H := W) (𝒜 := ℳ) hx
      ((mem_grading_iff ℳ _ _).mp hf a) hm

end Mei.GradedOperators
