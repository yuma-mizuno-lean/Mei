/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Operators.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Operator

/-!
# Finite quotients of homogeneous operator families

At each finite shifted cutoff, uniformly finitely supported operator families give
all linear maps into the ordinary coefficient quotient, even for infinitely generated
input modules. The quotient comparison uses `operatorCoefficientsEquiv`, so it reads
the same ambient components as the finite operator action. No completion of a Hom
space with uncontrolled homogeneous support is used.
-/

public noncomputable section

open scoped DirectSum

namespace Mei.GradedOperators

variable {Γ R M H : Type*} [AddCommGroup Γ] [DecidableEq Γ] [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommMonoid H] [Module R H]
  (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M) [DirectSum.Decomposition ℳ] (p : Γ)

/-- The finite shifted quotient of homogeneous operators is the entire space of
linear maps into the finite shifted coefficient quotient. -/
def quotientEquiv (k : ℕ) :
    ModuleFiltration.quotient
      (M := shiftedSubmodule (grading (H := H) ℳ) d.monoid p)
      (d.shiftedFiltration (grading (H := H) ℳ) p) k ≃ₗ[R]
      (H →ₗ[R] (d.shiftedFiltration ℳ p).quotient k) :=
  (d.shiftedQuotientEquivDirectSum (grading (H := H) ℳ) p k).trans
    ((DirectSum.congrLinearEquiv (fun n : d.cutoff k => pieceEquiv ℳ (p + n.val))).trans
      (PositiveDegrees.operatorCoefficientsEquiv d ℳ p k))

/-- The inverse comparison reads each homogeneous map pointwise. -/
@[simp↓]
theorem quotientEquiv_symm_component (k : ℕ)
    (f : H →ₗ[R] (d.shiftedFiltration ℳ p).quotient k) (a : H) (n : d.cutoff k) :
    eval ℳ a (d.shiftedQuotientComponent (grading (H := H) ℳ) p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n)
        ((quotientEquiv (H := H) d ℳ p k).symm f)) =
      (d.shiftedQuotientComponent ℳ p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n) (f a) : M) := by
  rw [quotientEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply,
    ← PositiveDegrees.shiftedQuotientEquivDirectSum_apply,
    LinearEquiv.apply_symm_apply]
  let E := DirectSum.congrLinearEquiv (fun n : d.cutoff k => pieceEquiv (H := H) ℳ (p + n.val))
  have he := congrArg (fun g => g n)
    (E.apply_symm_apply ((PositiveDegrees.operatorCoefficientsEquiv d ℳ p k).symm f))
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_apply] at he
  have ha := congrArg (fun g : H →ₗ[R] ℳ (p + n.val) => (g a : M)) he
  simpa only [E, LinearEquiv.coe_coe, pieceEquiv_apply,
    PositiveDegrees.operatorCoefficientsEquiv_symm_apply] using ha

end Mei.GradedOperators
