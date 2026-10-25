/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of positive gradings

Positive support and degree submodules are preserved by scalar extension.
Together with Mathlib's decomposition of the tensor product, these results
identify the degree filtration after changing the coefficient semiring, with
no flatness, freeness, or finiteness assumptions on the modules.
-/

public section

namespace Mei

variable {N R S M : Type*} [AddCommMonoid N] [CommSemiring R]
  [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  (d : PositiveDegrees N) (ℳ : N → Submodule R M)

/-- Scalar extension preserves the support condition of a positive grading. -/
instance IsPositiveGrading.baseChange [IsPositiveGrading d ℳ] :
    IsPositiveGrading d (fun n => (ℳ n).baseChange S) where
  eq_bot n hn := by
    rw [IsPositiveGrading.eq_bot (d := d) (ℒ := ℳ) n hn, Submodule.baseChange_bot]

/-- The sum of pieces above a cutoff commutes with extension of scalars. -/
@[simp]
theorem PositiveDegrees.degreeSubmodule_baseChange (k : ℕ) :
    d.degreeSubmodule (fun n => (ℳ n).baseChange S) k =
      (d.degreeSubmodule ℳ k).baseChange S := by
  simp only [PositiveDegrees.degreeSubmodule_def]
  symm
  rw [Submodule.iSup_eq_span, Submodule.baseChange_span, Set.image_iUnion,
    Submodule.span_iUnion]
  simp only [Submodule.baseChange_eq_span, Submodule.map_coe]

end Mei
