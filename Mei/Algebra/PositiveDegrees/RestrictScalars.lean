/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Grading
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Restriction of scalars for positive gradings

Positive support and degree submodules are preserved by restriction of scalars.
The cutoff comparison applies to arbitrary families of submodules: it requires
neither an internal decomposition nor positivity. Together with the inherited
decompositions, it identifies degree filtrations over different coefficient semirings.
-/

public section

namespace Mei

variable {N R S M : Type*} [AddCommMonoid N] [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module R M] [Module S M] [SMul R S] [IsScalarTower R S M]
  (d : PositiveDegrees N) (ℳ : N → Submodule S M)

/-- Restricting scalars preserves the support of a positive grading. -/
instance IsPositiveGrading.restrictScalars [IsPositiveGrading d ℳ] :
    IsPositiveGrading d (fun n => (ℳ n).restrictScalars R) where
  eq_bot n hn := by
    rw [IsPositiveGrading.eq_bot (d := d) (ℒ := ℳ) n hn,
      Submodule.restrictScalars_bot]

namespace PositiveDegrees

/-- Degree cutoffs commute with restriction of scalars, even without a decomposition. -/
@[simp]
theorem degreeSubmodule_restrictScalars (k : ℕ) :
    d.degreeSubmodule (fun n => (ℳ n).restrictScalars R) k =
      (d.degreeSubmodule ℳ k).restrictScalars R := by
  simp only [degreeSubmodule_def, Submodule.restrictScalars_iSup]

end PositiveDegrees
end Mei
