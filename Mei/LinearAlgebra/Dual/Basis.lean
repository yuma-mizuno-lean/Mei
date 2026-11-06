/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Positivity of the coordinate pairing of a basis

Over a linearly ordered commutative ring, the pairing `b.toDual` of a basis `b` is positive
definite: a vector pairing to zero with itself is zero (`Module.Basis.toDual_self_eq_zero_iff`).
The basis may be infinite.
-/

public section

namespace Module.Basis

/-- Over a linearly ordered commutative ring, a vector pairing to zero with itself under the
coordinate pairing of a basis is zero. -/
theorem toDual_self_eq_zero_iff {R N ι : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [AddCommGroup N] [Module R N] [DecidableEq ι]
    (b : Basis ι R N) {y : N} : b.toDual y y = 0 ↔ y = 0 := by
  refine ⟨fun hy => ?_, fun hy => by simp [hy]⟩
  -- The self-pairing is the sum of the squares of the coordinates.
  have hsum : b.toDual y y = ∑ j ∈ (b.repr y).support, b.repr y j * b.repr y j := by
    conv_lhs => arg 2; rw [← b.linearCombination_repr y]
    simp [Finsupp.linearCombination_apply, Finsupp.sum, b.toDual_apply_left]
  rw [hsum, Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg _] at hy
  refine b.repr.map_eq_zero_iff.mp (Finsupp.ext fun j => ?_)
  by_contra hj
  exact hj (mul_self_eq_zero.mp (hy j (Finsupp.mem_support_iff.mpr hj)))

end Module.Basis
