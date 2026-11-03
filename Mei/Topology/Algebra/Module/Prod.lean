/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear maps on a product of two copies of the scalars

A continuous linear map out of `R × R` is determined by its values on the two standard basis
vectors `(1, 0)` and `(0, 1)`.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [Semiring R] [TopologicalSpace R] [AddCommMonoid M] [TopologicalSpace M]
  [Module R M]

/-- A continuous linear map on `R × R` is determined by its values on the standard basis. -/
theorem apply_prod_eq_fst_smul_add_snd_smul (l : (R × R) →L[R] M) (p : R × R) :
    l p = p.1 • l (1, 0) + p.2 • l (0, 1) := by
  have hp : p = p.1 • ((1, 0) : R × R) + p.2 • ((0, 1) : R × R) := by ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul]

/-- A continuous linear map on `R × R` is determined on the first axis by its value at
`(1, 0)`. -/
theorem apply_eq_fst_smul_of_snd_eq_zero (l : (R × R) →L[R] M) {p : R × R} (hp : p.2 = 0) :
    l p = p.1 • l (1, 0) := by
  rw [apply_prod_eq_fst_smul_add_snd_smul l p, hp, zero_smul, add_zero]

end ContinuousLinearMap
