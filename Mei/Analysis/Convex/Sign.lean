/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Basic.Sign.Defs
import Mathlib.Tactic.Linarith

/-!
# Sign regions of an ordered ring

The points of a linearly ordered commutative ring with a prescribed sign form a convex set, which
is open when the sign is nonzero. A convex combination of a point of nonzero sign `σ`
with another point, vanishing strictly before the other point, forces that point to
have sign `-σ`.
-/

public section

open Set

namespace Mei

variable {𝕜 : Type*} [CommRing 𝕜] [LinearOrder 𝕜]

/-- The points of a nonzero sign form an open set. -/
theorem isOpen_setOf_sign_eq [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜]
    {σ : SignType} (hσ : σ ≠ 0) : IsOpen {a : 𝕜 | SignType.sign a = σ} := by
  rcases σ with _ | _ | _
  · exact (hσ rfl).elim
  · simp_rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff]
    exact isOpen_Iio
  · simp_rw [SignType.pos_eq_one, sign_eq_one_iff]
    exact isOpen_Ioi

variable [IsStrictOrderedRing 𝕜]

/-- The points of a given sign form a convex set. -/
theorem convex_setOf_sign_eq (σ : SignType) : Convex 𝕜 {a : 𝕜 | SignType.sign a = σ} := by
  rcases σ with _ | _ | _
  · simp_rw [SignType.zero_eq_zero, sign_eq_zero_iff, Set.ofPred_eq_eq_singleton]
    exact convex_singleton 0
  · simp_rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff]
    exact convex_Iio 0
  · simp_rw [SignType.pos_eq_one, sign_eq_one_iff]
    exact convex_Ioi 0

/-- If a convex combination of a point of nonzero sign `σ` with `b` vanishes before
reaching `b`, then `b` has the opposite sign. -/
theorem sign_eq_neg_of_convexCombination_eq_zero {σ : SignType} (hσ : σ ≠ 0) {a b t : 𝕜}
    (ha : SignType.sign a = σ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hz : (1 - t) * a + t * b = 0) : SignType.sign b = -σ := by
  have hpos : 0 < 1 - t := sub_pos.2 ht1
  rcases σ with _ | _ | _
  · exact (hσ rfl).elim
  · have ha' : a < 0 := sign_eq_neg_one_iff.mp ha
    exact sign_eq_one_iff.mpr (by nlinarith [mul_neg_of_pos_of_neg hpos ha'])
  · have ha' : 0 < a := sign_eq_one_iff.mp ha
    exact sign_eq_neg_one_iff.mpr (by nlinarith [mul_pos hpos ha'])

end Mei
