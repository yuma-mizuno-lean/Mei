/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform finite expansions of homogeneous histories

When all nonzero homogeneous pieces lie in a fixed finite set, a composite of
linear maps is the sum of its whole-component history maps over that set.
Unlike the support of a single input, this finite index set works simultaneously
for every coefficient, without a finite generation assumption on the modules.
Thus the expansion is an identity of linear maps, suitable for coefficient
identities with a variable incoming parameter.

We use `homogeneousHistory`, Mathlib's internal direct-sum reconstruction, and
`Fin.consEquiv` to enumerate the output degree followed by the remaining history.
-/

public noncomputable section

namespace Mei

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [DecidableEq ι] (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]

/-- If the grading is supported on a finite set, summing all history maps over
that set recovers the composite as a linear map. The same index set works for
every input; zero component maps contribute zero. -/
theorem sum_homogeneousHistory_eq_prod (S : Finset ι)
    (hS : ∀ i, i ∉ S → ℳ i = ⊥) {n : ℕ} (T : Fin n → Module.End R M) :
    ∑ p : Fin n → S, homogeneousHistory ℳ T (fun j => (p j).val) =
      (List.ofFn T).prod := by
  classical
  have hsum (x : M) : ∑ i : S, (DirectSum.decompose ℳ x i.val : M) = x := by
    rw [Finset.sum_coe_sort S (fun i => (DirectSum.decompose ℳ x i : M))]
    have hs : (DirectSum.decompose ℳ x).support ⊆ S := by
      intro i hi
      by_contra hn
      have hz : DirectSum.decompose ℳ x i = 0 :=
        Subtype.ext (by simpa only [ZeroMemClass.coe_zero, hS i hn, Submodule.mem_bot] using
          (DirectSum.decompose ℳ x i).property)
      exact DFinsupp.mem_support_iff.mp hi hz
    simpa only [DFinsupp.sum] using
      (DFinsupp.sum_of_support_subset (f := DirectSum.decompose ℳ x)
        (g := fun i y => (y : M)) hs (by simp)).symm.trans
          (DirectSum.sum_support_decompose ℳ x)
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    ext x
    rw [LinearMap.sum_apply,
      ← (Fin.consEquiv (fun _ : Fin (n + 1) => S)).sum_comp,
      Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, homogeneousHistory_succ_apply,
      Fin.cons_succ]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext y; arg 2; ext i; rw [Fin.cons_zero]
    simp_rw [hsum]
    rw [← map_sum, ← LinearMap.sum_apply, ih, List.ofFn_succ,
      List.prod_cons, Module.End.mul_apply]

end Mei
