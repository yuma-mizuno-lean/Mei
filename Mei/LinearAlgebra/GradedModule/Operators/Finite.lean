/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Operators.Basic
public import Mei.LinearAlgebra.GradedModule.Shifted.Operator
public import Mei.LinearAlgebra.GradedModule.Shifted.Map

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

/-- The finite Hom comparison reads homogeneous operators, then assembles their
values in the ordinary quotient. -/
theorem quotientEquiv_def (k : ℕ) :
    quotientEquiv (H := H) d ℳ p k =
      (d.shiftedQuotientEquivDirectSum (grading (H := H) ℳ) p k).trans
        ((DirectSum.congrLinearEquiv (fun n : d.cutoff k => pieceEquiv ℳ (p + n.val))).trans
          (PositiveDegrees.operatorCoefficientsEquiv d ℳ p k)) := (rfl)

/-- The inverse comparison reads each homogeneous map pointwise. -/
@[simp↓ high]
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

/-- Reading an operator quotient component and evaluating it commutes with
the quotient map induced by evaluation. -/
@[simp↓]
theorem eval_shiftedQuotientComponent (k : ℕ) (x) (a : H) (n : d.cutoff k) :
    eval ℳ a (d.shiftedQuotientComponent (grading (H := H) ℳ) p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n) x) =
      (d.shiftedQuotientComponent ℳ p (p + n.val) k
        (d.degree_add_val_sub_self_le p k n)
        (d.quotientCoefficientMap (grading (H := H) ℳ) ℳ p (eval ℳ a)
          (fun _ _ hf => eval_mem ℳ a hf) k x) : M) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [d.quotientCoefficientMap_mk, d.shiftedQuotientComponent_mk,
      d.shiftedQuotientComponent_mk, eval_decompose, d.coe_shiftedCoefficientMap]

/-- Evaluation of the finite comparison is induced by the original evaluation map. -/
@[simp]
theorem quotientEquiv_apply (k : ℕ) (x) (a : H) :
    quotientEquiv (H := H) d ℳ p k x a =
      d.quotientCoefficientMap (grading (H := H) ℳ) ℳ p (eval ℳ a)
        (fun _ _ hf => eval_mem ℳ a hf) k x := by
  apply d.shiftedQuotient_ext ℳ p
  intro n
  apply Subtype.ext
  have hc := quotientEquiv_symm_component d ℳ p k
    (quotientEquiv (H := H) d ℳ p k x) a n
  rw [LinearEquiv.symm_apply_apply] at hc
  exact hc.symm.trans (eval_shiftedQuotientComponent d ℳ p k x a n)

end Mei.GradedOperators
