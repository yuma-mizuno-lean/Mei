/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Algebra.Lie.BCH.Conjugation

/-!
# Exponentials along a line and conjugation of class two

In the BCH group of a nilpotent rational Lie algebra, exponentials of integer multiples of one
element multiply additively: `exp (m • x) * exp (n • x) = exp ((m + n) • x)`. If
`⁅x, ⁅x, y⁆⁆ = 0`, conjugation by `exp x` adds the commutator:
`exp x * exp y * exp (-x) = exp (y + ⁅x, y⁆)`.

These are the group identities used to compute products of wall-crossing automorphisms whose
logarithms span a Lie algebra of nilpotency class two, such as the Heisenberg-type labels of
two crossing walls and their commutator wall.
-/

public section

namespace Mei.BCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing.IsNilpotent L]

/-- Exponentials of integer multiples of one element multiply additively. -/
theorem exp_zsmul_mul_exp_zsmul (x : L) (m n : ℤ) :
    exp (m • x) * exp (n • x) = exp ((m + n) • x) := by
  rw [exp_zsmul, exp_zsmul, exp_zsmul, zpow_add]

/-- If `⁅x, ⁅x, y⁆⁆ = 0`, conjugation by `exp x` adds the commutator `⁅x, y⁆`. -/
theorem exp_mul_exp_mul_exp_neg_of_lie_lie_eq_zero {x y : L} (h : ⁅x, ⁅x, y⁆⁆ = 0) :
    exp x * exp y * exp (-x) = exp (y + ⁅x, y⁆) := by
  have hx : IsNilpotent (LieAlgebra.ad ℚ L x) :=
    LieModule.isNilpotent_toEnd_of_isNilpotent ℚ L L x
  rw [exp_neg, ← exp_expAd x y hx.exists_pow_apply_eq_zero,
    TauCeti.expAd_apply_of_lie_lie_eq_zero hx.exists_pow_apply_eq_zero h]

end Mei.BCHGroup
