/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Graded.Sign.Basic

/-!
# Sign subalgebras in uniform-sign chambers

If an additive character has the same sign on every nonzero homogeneous piece,
its subalgebra of that sign is the whole Lie algebra.
-/

public section

namespace Mei

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [DecidableEq N]
  [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
  (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ] (θ : N →+ A)

/-- A character with one sign on every nonzero piece has the whole Lie algebra
as its subalgebra of that sign. -/
theorem signSubalgebra_eq_top_of_sign_eq (s : SignType)
    (hs : ∀ n, ℒ n ≠ ⊥ → SignType.sign (θ n) = s) : signSubalgebra ℒ θ s = ⊤ := by
  apply LieSubalgebra.toSubmodule_injective
  apply top_unique
  rw [← (DirectSum.Decomposition.isInternal ℒ).submodule_iSup_eq_top]
  refine iSup_le fun n => ?_
  by_cases hn : ℒ n = ⊥
  · rw [hn]
    exact bot_le
  · rw [← hs n hn]
    exact le_signSubalgebra _ _ _

end Mei
