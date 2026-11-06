/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Operators.Basic
public import Mei.LinearAlgebra.GradedModule.Operators.Finite
public import Mei.Algebra.Lie.Graded.Shifted.Operator
public import Mei.Algebra.Lie.Graded.Shifted.Map

/-!
# Finite BCH representations on homogeneous operator families

The finite shifted quotient of the graded Hom representation identifies with all
linear maps into the ordinary shifted quotient. Under this existing comparison,
its BCH action is postcomposition by the ordinary BCH action. Its homogeneous
blocks are therefore the same whole linear maps as the blocks of
`PositiveDegrees.operatorBCHAction`.

This connects the graded representation used for semidirect operator probes to
the homogeneous operator coefficients used in endpoint recurrences. The input
module need not be finitely generated, and its homogeneous output pieces need
not be free. Zero evaluations and degree shifts with zero spatial projection are
retained. The operator-probe construction follows Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, §3.3.3 (arXiv:1503.06183v5).
We use `GradedOperators.quotientEquiv`, the filtered BCH naturality theorem, and
the existing operator BCH action, without introducing another representation.
-/

public noncomputable section

open scoped DirectSum

namespace Mei.GradedOperators

variable {Γ R H M L : Type*} [AddCommGroup Γ] [DecidableEq Γ]
  [CommRing R] [Algebra ℚ R] [AddCommGroup H] [Module R H]
  [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [LieRingModule L M] [LieModule R L M]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ]
  (p : Γ) (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ]
  [IsPositiveGrading d ℒ] [SetLike.GradedBracket ℒ ℳ]

local notation "𝒪" => lieGrading (H := H) ℳ ℒ
local notation "F" => d.shiftedLieFiltration ℒ ℳ p
local notation "Fop" => d.shiftedLieFiltration ℒ 𝒪 p
local notation "E(" k ")" => quotientEquiv (H := TrivialLieModule R L H) d ℳ p k

/-- The BCH action on the actual graded operator quotient becomes
postcomposition on the full Hom space under the finite quotient comparison. -/
@[simp↓]
theorem quotientEquiv_truncatedBCHAction (k : ℕ) (g : d.truncatedGroup ℒ k)
    (x) (a : TrivialLieModule R L H) :
    E(k) ((Fop).truncatedBCHAction d ℒ k g x) a =
      (F).truncatedBCHAction d ℒ k g (E(k) x a) := by
  have ht := d.quotientCoefficientMap_truncatedBCHAction
    (M := lieSubmodule (H := H) ℳ ℒ) (N := M) (L := L) 𝒪 ℳ p ℒ (eval ℳ a)
    (fun _ _ hf => eval_mem ℳ a hf) (fun y z => eval_lie ℳ ℒ y z a) k g x
  simpa only [quotientEquiv_apply] using ht

/-- The direct-sum homogeneous maps of the actual operator representation
carry exactly the BCH action used for endpoint operator recurrences. -/
theorem congrLinearEquiv_truncatedBCHAction (k : ℕ) (g : d.truncatedGroup ℒ k) (x) :
    (DirectSum.congrLinearEquiv (fun n : d.cutoff k =>
      pieceEquiv (H := TrivialLieModule R L H) ℳ (p + n.val)))
        (d.shiftedQuotientEquivDirectSum 𝒪 p k
          ((Fop).truncatedBCHAction d ℒ k g x)) =
      PositiveDegrees.operatorBCHAction d ℳ p ℒ k g
        ((DirectSum.congrLinearEquiv (fun n : d.cutoff k =>
          pieceEquiv (H := TrivialLieModule R L H) ℳ (p + n.val)))
            (d.shiftedQuotientEquivDirectSum 𝒪 p k x)) := by
  apply (PositiveDegrees.operatorCoefficientsEquiv d ℳ p k).injective
  ext a
  rw [PositiveDegrees.operatorCoefficientsEquiv_operatorBCHAction]
  simpa only [quotientEquiv_def, LinearEquiv.trans_apply] using
    quotientEquiv_truncatedBCHAction d ℳ p ℒ k g x a

/-- Reconstructing an operator from its Hom family also intertwines the BCH
action. This is the inverse form of the finite representation comparison. -/
@[simp]
theorem quotientEquiv_symm_congrRight (k : ℕ) (g : d.truncatedGroup ℒ k)
    (f : TrivialLieModule R L H →ₗ[R] (F).quotient k) :
    (E(k)).symm ((LinearEquiv.congrRight ((F).truncatedBCHAction d ℒ k g)) f) =
      (Fop).truncatedBCHAction d ℒ k g ((E(k)).symm f) := by
  apply (E(k)).injective
  ext a
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.congrRight_apply_apply,
    quotientEquiv_truncatedBCHAction]

end Mei.GradedOperators
