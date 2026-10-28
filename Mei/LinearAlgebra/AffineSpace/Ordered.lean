/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Ordered
public import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ratios of affine functions along segments

If an affine function `ℓ` is positive at the two ends of a segment, the ratio `m / ℓ`
of another affine function by `ℓ` is monotone along the segment, in the direction in
which it increases between the ends. The level sets of `m / ℓ` form a pencil of
hyperplanes, so a segment on which `ℓ` is positive meets them in the order of their
levels. The proof cross-multiplies, using `AffineMap.apply_lineMap`.
For linear functionals, a crossing of a level hyperplane determines the signs before
and after the crossing along the segment.
-/

public section

open Set

namespace AffineMap

variable {k V P : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- If `ℓ` is positive at both ends of a segment, the ratio `m / ℓ` is monotone along
it whenever its value at the start is at most its value at the end. -/
theorem monotoneOn_div_lineMap (ℓ m : P →ᵃ[k] k) {x y : P} (hx : 0 < ℓ x) (hy : 0 < ℓ y)
    (hxy : m x / ℓ x ≤ m y / ℓ y) :
    MonotoneOn (fun t => m (lineMap x y t) / ℓ (lineMap x y t)) (Icc (0 : k) 1) := by
  have hpos {r : k} (hr : r ∈ Icc (0 : k) 1) : 0 < ℓ (lineMap x y r) := by
    simpa [apply_lineMap] using lineMap_strict_mono_endpoints hx hy hr.1 hr.2
  intro s hs t ht hst
  rw [div_le_div_iff₀ hx hy] at hxy
  dsimp only
  rw [div_le_div_iff₀ (hpos hs) (hpos ht)]
  have hcross : m (lineMap x y s) * ℓ (lineMap x y t) -
      m (lineMap x y t) * ℓ (lineMap x y s) = (t - s) * (m x * ℓ y - m y * ℓ x) := by
    simp only [apply_lineMap, lineMap_apply_module, smul_eq_mul]
    ring
  nlinarith

end AffineMap

namespace LinearMap

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

/-- Along a segment through a hyperplane `μ = c` at parameter `s`, the value of `μ - c` at
parameter `r`, scaled by `s`, is its value at the start scaled by `s - r`. -/
theorem apply_lineMap_sub_mul (μ : V →ₗ[k] k) {u v : V} {s c : k}
    (hs : μ (AffineMap.lineMap u v s) = c) (r : k) :
    (μ (AffineMap.lineMap u v r) - c) * s = (μ u - c) * (s - r) := by
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul] at hs ⊢
  rw [← hs]
  ring

variable [LinearOrder k] [IsStrictOrderedRing k]

/-- Along a segment from `u` meeting the hyperplane `μ = c` at parameter `s > 0`, with
`u` off the hyperplane, points before `s` lie on the side of `u`. -/
theorem mul_pos_of_lt_of_apply_lineMap (μ : V →ₗ[k] k) {u v : V} {s c r : k}
    (hs : μ (AffineMap.lineMap u v s) = c) (hs0 : 0 < s) (hu : μ u - c ≠ 0) (hr : r < s) :
    0 < (μ (AffineMap.lineMap u v r) - c) * (μ u - c) := by
  have : 0 < (μ (AffineMap.lineMap u v r) - c) * (μ u - c) * s := by
    rw [mul_right_comm _ _ s, μ.apply_lineMap_sub_mul hs r, mul_right_comm]
    exact mul_pos (mul_self_pos.mpr hu) (by linarith)
  exact pos_of_mul_pos_left this hs0.le

/-- Along a segment from `u` meeting the hyperplane `μ = c` at parameter `s > 0`, with
`u` off the hyperplane, points after `s` lie on the side opposite to `u`. -/
theorem mul_neg_of_lt_of_apply_lineMap (μ : V →ₗ[k] k) {u v : V} {s c r : k}
    (hs : μ (AffineMap.lineMap u v s) = c) (hs0 : 0 < s) (hu : μ u - c ≠ 0) (hr : s < r) :
    (μ (AffineMap.lineMap u v r) - c) * (μ u - c) < 0 := by
  have : (μ (AffineMap.lineMap u v r) - c) * (μ u - c) * s < 0 := by
    rw [mul_right_comm _ _ s, μ.apply_lineMap_sub_mul hs r, mul_right_comm]
    exact mul_neg_of_pos_of_neg (mul_self_pos.mpr hu) (by linarith)
  by_contra hneg
  exact this.not_ge (mul_nonneg (not_lt.mp hneg) hs0.le)

end LinearMap
