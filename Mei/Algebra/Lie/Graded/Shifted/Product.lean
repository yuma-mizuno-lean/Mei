/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.Bilinear
public import Mei.RingTheory.GradedAlgebra.Shifted.Basic

/-!
# Completed actions preserve shifted coefficient products

A graded derivation action preserves multiplication between two shifted modules
after exponentiation and degree completion. The product may have a different
shift from either input, and the coefficient algebra may be noncommutative.
The proof specializes the general filtered bilinear BCH equivariance theorem.

The shifted coefficient setting is that of Mandel, *Scattering diagrams, theta
functions, and refined tropical curve counts*, §2.1 (arXiv:1503.06183).
-/

public section

noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R L A : Type*} [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [Ring A] [Algebra R A] [LieRingModule L A] [LieModule R L A]
  [IsDerivationAction L A] [DecidableEq Γ]
  (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) (𝒜 : Γ → Submodule R A)
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [DirectSum.Decomposition 𝒜] [SetLike.GradedBracket ℒ 𝒜] [SetLike.GradedMul 𝒜]
  (p q : Γ)

private abbrev shiftedLieMul : d.shiftedLieSubmodule ℒ 𝒜 p →ₗ[R]
    d.shiftedLieSubmodule ℒ 𝒜 q →ₗ[R] d.shiftedLieSubmodule ℒ 𝒜 (p + q) :=
  shiftedMul 𝒜 d.monoid p q

omit [Algebra ℚ R] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieModule R L A] [DirectSum.Decomposition 𝒜] in
private theorem lie_shiftedLieMul (z : L) (x : d.shiftedLieSubmodule ℒ 𝒜 p)
    (y : d.shiftedLieSubmodule ℒ 𝒜 q) :
    ⁅z, d.shiftedLieMul ℒ 𝒜 p q x y⁆ =
      d.shiftedLieMul ℒ 𝒜 p q x ⁅z, y⁆ + d.shiftedLieMul ℒ 𝒜 p q ⁅z, x⁆ y := by
  apply Subtype.ext
  dsimp only [shiftedLieMul]
  rw [LieSubmodule.coe_bracket, LieSubmodule.coe_add,
    coe_shiftedMul, coe_shiftedMul, coe_shiftedMul,
    LieSubmodule.coe_bracket, LieSubmodule.coe_bracket]
  exact IsDerivationAction.lie_mul z (x : A) (y : A)

/-- The completed BCH action is compatible with products between arbitrary shifted modules. -/
@[simp]
theorem completedBCHAction_shiftedCompletionMul (g : d.completedBCHGroup ℒ)
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) :
    (d.shiftedLieFiltration ℒ 𝒜 (p + q)).completedBCHAction d ℒ g
        (d.shiftedCompletionMul 𝒜 p q x y) =
      d.shiftedCompletionMul 𝒜 p q
        ((d.shiftedLieFiltration ℒ 𝒜 p).completedBCHAction d ℒ g x)
        ((d.shiftedLieFiltration ℒ 𝒜 q).completedBCHAction d ℒ g y) := by
  simp only [shiftedCompletionMul_def]
  exact ModuleFiltration.completedBCHAction_completionBilinear
    (d.shiftedLieFiltration ℒ 𝒜 p) (d.shiftedLieFiltration ℒ 𝒜 q)
    (d.shiftedLieFiltration ℒ 𝒜 (p + q)) d ℒ
    (shiftedMul 𝒜 d.monoid p q)
    (fun _ _ _ _ => d.shiftedMul_mem_shiftedFiltration 𝒜 p q)
    (d.lie_shiftedLieMul ℒ 𝒜 p q) g x y

end Mei.PositiveDegrees
