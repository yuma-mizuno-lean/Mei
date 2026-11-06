/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Shifted.Operator
public import Mei.Algebra.Lie.Graded.Shifted.Block

/-!
# Homogeneous blocks of operator BCH actions

On maps from an arbitrary incoming module, each block of the difference
between the BCH action and the identity is postcomposition by the ordinary
coefficient block. This identifies the actual operator action with the
blocks used in lower-degree recursions, including zero component maps.

The action is the existing `operatorBCHAction`, transported through
`operatorCoefficientsEquiv`; no new coefficient action is introduced.
-/

public noncomputable section

open scoped DirectSum

namespace Mei.PositiveDegrees

universe u

variable {Γ : Type} {R H : Type*} {M L : Type u}
  [AddCommGroup Γ] [CommRing R] [Algebra ℚ R]
  [AddCommGroup M] [Module R M] [AddCommMonoid H] [Module R H]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)
  [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
  [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

/-- Between homogeneous operator pieces, the difference of the BCH action and
identity is postcomposition by the ordinary coefficient block. This retains
whole linear maps, including maps that vanish on particular incoming inputs. -/
theorem operatorBCHAction_lof_sub (k : ℕ) (g : d.truncatedGroup ℒ k)
    (n m : d.cutoff k) (f : H →ₗ[R] ℳ (p + m.val)) :
    operatorBCHAction d ℳ p ℒ k g
        (DirectSum.lof R (d.cutoff k) (fun n => H →ₗ[R] ℳ (p + n.val)) m f) n -
      (DirectSum.lof R (d.cutoff k) (fun n => H →ₗ[R] ℳ (p + n.val)) m f) n =
        (labelBlock d ℳ p ℒ k g n m).comp f := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.sub_apply, LinearMap.comp_apply, operatorBCHAction_apply,
    operatorCoefficientsEquiv_lof, labelBlock_apply, LinearMap.sub_apply,
    Module.End.one_apply, map_sub, ← shiftedQuotientInclusion_apply]
  congr 1
  exact (shiftedQuotientComponent_operatorCoefficientsEquiv d ℳ p k
    (DirectSum.lof R (d.cutoff k) (fun n => H →ₗ[R] ℳ (p + n.val)) m f) n x).symm.trans
      (congrArg (d.shiftedQuotientComponent ℳ p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n))
        (operatorCoefficientsEquiv_lof d ℳ p k m f x))

end Mei.PositiveDegrees
