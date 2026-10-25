/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mei.LinearAlgebra.TensorProduct.BaseChange

/-!
# Extension of scalars for positive gradings

Positive support is preserved by extension of scalars, and extending the sum of
pieces above a cutoff gives the sum of the extended pieces above that cutoff.
These statements require neither flatness nor a direct-sum decomposition.
-/

public section

namespace Mei

variable {N R S M : Type*} [AddCommMonoid N] [CommSemiring R]
  [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]
  (d : PositiveDegrees N) (ℳ : N → Submodule R M)

/-- Extension of scalars preserves positive support. -/
instance IsPositiveGrading.baseChange [IsPositiveGrading d ℳ] :
    IsPositiveGrading d (fun n => (ℳ n).baseChange S) where
  eq_bot n hn := by
    rw [IsPositiveGrading.eq_bot (d := d) (ℒ := ℳ) n hn, Submodule.baseChange_bot]

namespace PositiveDegrees

/-- Extending scalars commutes with taking the submodule above a degree cutoff. -/
@[simp]
theorem degreeSubmodule_baseChange (k : ℕ) :
    (d.degreeSubmodule ℳ k).baseChange S =
      d.degreeSubmodule (fun n => (ℳ n).baseChange S) k := by
  simp only [degreeSubmodule_def, Submodule.baseChange_iSup]

end PositiveDegrees
end Mei
