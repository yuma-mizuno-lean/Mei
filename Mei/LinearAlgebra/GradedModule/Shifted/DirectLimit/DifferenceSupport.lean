/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Component

/-!
# Ambient degrees of global coefficients

The multiset-indexed global coefficient module has no nonzero component outside
`P - P`. This restriction is meaningful when the positive monoid does not span
the ambient group: even a family supported at a single ambient degree can fail
to come from a global coefficient. No finite-support or multiplication assumption
is needed for the restriction.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R M : Type*} [AddCommGroup Γ] [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (ℳ : Γ → Submodule R M)
  [DirectSum.Decomposition ℳ]

/-- Global homogeneous components vanish outside differences of positive degrees. -/
theorem shiftedDirectLimitComponents_eq_zero_of_not_difference
    (x : d.ShiftedDirectLimit ℳ) {u : Γ}
    (hu : ¬ ∃ a b : d.monoid, u = (a : Γ) - b) :
    d.shiftedDirectLimitComponents ℳ x u = 0 := by
  obtain ⟨s, hs⟩ := (d.mem_range_shiftedDirectLimitComponents_iff ℳ
    (d.shiftedDirectLimitComponents ℳ x)).mp ⟨x, rfl⟩
  apply hs u
  intro h
  apply hu
  refine ⟨⟨u - d.coefficientOrigin s, h⟩, s.sum, ?_⟩
  -- Simplification reads the value of the supported subtype witness above.
  simp only [coefficientOrigin_eq_neg_sum, sub_neg_eq_add,
    add_sub_cancel_right]

/-- A family with a nonzero component outside positive differences is not global. -/
theorem notMem_range_shiftedDirectLimitComponents_of_not_difference
    (a : ∀ u, ℳ u) {u : Γ} (hau : a u ≠ 0)
    (hu : ¬ ∃ p q : d.monoid, u = (p : Γ) - q) :
    a ∉ LinearMap.range (d.shiftedDirectLimitComponents ℳ) := by
  rintro ⟨x, rfl⟩
  exact hau (d.shiftedDirectLimitComponents_eq_zero_of_not_difference ℳ x hu)

end Mei.PositiveDegrees
