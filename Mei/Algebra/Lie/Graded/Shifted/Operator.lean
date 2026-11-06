/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.Operator
public import Mei.Algebra.Lie.Graded.Shifted.Basic
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# BCH actions on homogeneous operator coefficients

Postcomposition by the truncated BCH action acts on linear families of shifted
coefficients. Transport through `operatorCoefficientsEquiv` gives an action on
the direct sum of their homogeneous operator pieces. Evaluation intertwines it
with the ordinary coefficient action, and the actions commute with cutoff
transitions. The input module is arbitrary, including infinitely generated ones.

This supplies the finite coefficient action for probes with variable incoming
coefficients, as in Mandel, *Scattering diagrams, theta functions, and refined
tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
-/

public noncomputable section

open scoped DirectSum

namespace Mei.PositiveDegrees

variable {Γ R M H : Type*} [AddCommGroup Γ] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid H] [Module R H]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ] (p : Γ)

variable {L : Type*} [LieRing L] [LieAlgebra R L] [Algebra ℚ R]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [LieRingModule L M] [LieModule R L M]
  (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  [SetLike.GradedBracket ℒ ℳ]

local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "O(" k ")" => (⨁ n : d.cutoff k, H →ₗ[R] ℳ (p + (n : Γ)))

/-- The truncated BCH action on homogeneous operator coefficients, by postcomposition
on the associated linear family. -/
def operatorBCHAction (k : ℕ) : d.truncatedGroup ℒ k →* (O(k) ≃ₗ[R] O(k)) :=
  MonoidHom.mk'
    (fun g => (operatorCoefficientsEquiv d ℳ p k).trans
      ((LinearEquiv.congrRight ((F).truncatedBCHAction d ℒ k g)).trans
        (operatorCoefficientsEquiv d ℳ p k).symm))
    (by
      intro g g'
      ext1 f
      apply (operatorCoefficientsEquiv d ℳ p k).injective
      ext x
      simp)

/-- Evaluation of operator coefficients intertwines their BCH action with the ordinary
truncated coefficient action. -/
@[simp]
theorem operatorCoefficientsEquiv_operatorBCHAction (k : ℕ) (g : d.truncatedGroup ℒ k)
    (f : O(k)) (x : H) :
    operatorCoefficientsEquiv d ℳ p k (operatorBCHAction d ℳ p ℒ k g f) x =
      (F).truncatedBCHAction d ℒ k g (operatorCoefficientsEquiv d ℳ p k f x) := by
  simp [operatorBCHAction]

/-- The component of the operator action is the whole component of the ordinary
action on the evaluated input. No basis for `H` or its coefficient pieces is needed. -/
theorem operatorBCHAction_apply (k : ℕ) (g : d.truncatedGroup ℒ k)
    (f : O(k)) (n : d.cutoff k) (x : H) :
    operatorBCHAction d ℳ p ℒ k g f n x =
      d.shiftedQuotientComponent ℳ p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n)
          ((F).truncatedBCHAction d ℒ k g (operatorCoefficientsEquiv d ℳ p k f x)) := by
  rw [← operatorCoefficientsEquiv_operatorBCHAction,
    shiftedQuotientComponent_operatorCoefficientsEquiv]

/-- The operator BCH actions form the same quotient tower as the ordinary actions. -/
theorem operatorTransition_operatorBCHAction {k l : ℕ} (hkl : k ≤ l)
    (g : d.truncatedGroup ℒ l) (f : O(l)) :
    operatorTransition d ℳ p hkl (operatorBCHAction d ℳ p ℒ l g f) =
      operatorBCHAction d ℳ p ℒ k ((d.truncationMap ℒ hkl).bchGroupMap g)
        (operatorTransition d ℳ p hkl f) := by
  apply (operatorCoefficientsEquiv d ℳ p k).injective
  apply LinearMap.ext
  intro x
  simp only [operatorCoefficientsEquiv_operatorTransition,
    operatorCoefficientsEquiv_operatorBCHAction]
  exact (F).transition_truncatedBCHAction d ℒ hkl g _

end Mei.PositiveDegrees
