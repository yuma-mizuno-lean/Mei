/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Sonnet 5.5
-/
module

public import Mei.Algebra.Lie.Graded.Postcomposition
public import Mei.LinearAlgebra.GradedModule.Shifted.Map

/-!
# Finite-order coefficient quotients of graded homomorphism modules

For a module `X` on which the Lie algebra acts trivially, the evaluations at all vectors of `X`
are jointly injective on every finite-order coefficient quotient of the shifted filtration of
`gradedHom ℒ ℳ X` (`quotientGradedHomEval_injective`): a class whose evaluations all vanish has
no component of relative degree at most the order.
-/

public noncomputable section

namespace Mei

variable {R Γ : Type*} {M L : Type u} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L] [LieRingModule L M]
  [LieModule R L M] (d : PositiveDegrees Γ) (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ]
  (ℳ : Γ → Submodule R M) [SetLike.GradedBracket ℒ ℳ] [DirectSum.Decomposition ℳ] (p : Γ)
  (X : Type u) [AddCommGroup X] [Module R X] [LieRingModule L X] [LieModule R L X]
  [LieModule.IsTrivial L X]

/-- The evaluations at all vectors of `X`, on the order-`k` coefficient quotient of the shifted
filtration of `gradedHom ℒ ℳ X`. -/
def quotientGradedHomEval (k : ℕ) :
    (d.shiftedFiltration (gradedHomPiece ℒ ℳ X) p).quotient k →ₗ[R]
      (X → (d.shiftedFiltration ℳ p).quotient k) :=
  LinearMap.pi fun v => PositiveDegrees.quotientCoefficientMap d (gradedHomPiece ℒ ℳ X) ℳ p
    (gradedHomEval ℒ ℳ X v).toLinearMap (fun _ _ ha => gradedHomEval_mem ℒ ℳ X ha) k

@[simp]
theorem quotientGradedHomEval_apply (k : ℕ)
    (y : (d.shiftedFiltration (gradedHomPiece ℒ ℳ X) p).quotient k) (v : X) :
    quotientGradedHomEval d ℒ ℳ p X k y v =
      PositiveDegrees.quotientCoefficientMap d (gradedHomPiece ℒ ℳ X) ℳ p
        (gradedHomEval ℒ ℳ X v).toLinearMap (fun _ _ ha => gradedHomEval_mem ℒ ℳ X ha) k y :=
  (rfl)

/-- A finite-order coefficient of the homomorphism module is determined by its evaluations: a
class whose evaluations all vanish has no component of relative degree at most `k`. -/
theorem quotientGradedHomEval_injective (k : ℕ) :
    Function.Injective (quotientGradedHomEval d ℒ ℳ p X k) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.mk_eq_zero, PositiveDegrees.mem_shiftedFiltration_iff]
  intro q hq
  rw [decompose_gradedHomPiece_eq_zero_iff]
  intro v
  have hv := congrFun hy v
  rw [quotientGradedHomEval_apply, PositiveDegrees.quotientCoefficientMap_mk] at hv
  rw [Pi.zero_apply, Submodule.Quotient.mk_eq_zero, PositiveDegrees.mem_shiftedFiltration_iff]
    at hv
  simpa using hv q hq

end Mei
