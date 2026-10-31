/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.History.Uniform
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform finite expansions of homogeneous histories

When all nonzero homogeneous pieces lie in a fixed finite set, a composite of
linear maps is the sum of its whole-component history maps over that set.
Unlike the support of a single input, this finite index set works simultaneously
for every coefficient, without a finite generation assumption on the modules.
Thus the expansion is an identity of linear maps, suitable for coefficient
identities with a variable incoming parameter.

This is a specialization of `sum_homogeneousHistory_comp_eq`: global grading
support supplies a uniform support on the identity input map. The shared
expansion also applies to infinitely supported gradings on smaller input ranges.
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
  let embed : (Fin n → S) → (Fin n → ι) := fun p j => (p j).val
  have hinj : Function.Injective embed := by
    intro p q hpq
    funext j
    exact Subtype.ext (congrFun hpq j)
  have hzero (p : Fin n → ι) (hp : p ∉ Finset.univ.image embed) :
      (homogeneousHistory ℳ T p).comp LinearMap.id = 0 := by
    ext x
    by_contra hx
    have hmem (j : Fin n) : p j ∈ S := by
      by_contra hj
      have hstage := homogeneousHistoryStage_mem ℳ T p x j
      rw [hS _ hj, Submodule.mem_bot] at hstage
      exact homogeneousHistoryStage_ne_zero ℳ T p hx j.castSucc hstage
    exact hp (Finset.mem_image.mpr ⟨fun j => ⟨p j, hmem j⟩, Finset.mem_univ _, rfl⟩)
  have he := sum_homogeneousHistory_comp_eq ℳ T LinearMap.id
    (Finset.univ.image embed) hzero
  rw [Finset.sum_image (fun p _ q _ hpq => hinj hpq)] at he
  simpa only [LinearMap.comp_id] using he

end Mei
