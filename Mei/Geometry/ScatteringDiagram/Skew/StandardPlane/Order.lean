/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.ScatteringDiagram.Skew.StandardPlane.Basic

/-!
# The angular order on plane degrees

The degrees of the standard plane are ordered by angle, counterclockwise from the first axis,
and among collinear degrees by size (`PlaneDegree.key`). A pair `x, y` with positive pairing
`{x, y} > 0` is in this order, `x < y` (`PlaneDegree.lt_of_det_pos`).
-/

public section

noncomputable section

namespace Mei.StandardPlane

open SkewLatticeDatum.Examples

variable {w : Weight}

namespace PlaneDegree

/-- The sort key of a plane degree: the angle coordinate `m₂ / (m₁ + m₂)`, which increases
with the slope of `m`, followed by the size `m₁ + m₂` to separate collinear degrees. -/
def key (m : PlaneDegree w) : ℚ ×ₗ ℤ := toLex ((m.snd : ℚ) / (m.fst + m.snd), m.fst + m.snd)

/-- The coordinate sum of a plane degree is positive. -/
theorem fst_add_snd_pos (m : PlaneDegree w) : 0 < m.fst + m.snd := by
  have := m.fst_nonneg
  have := m.snd_nonneg
  rcases m.fst_ne_zero_or <;> omega

/-- Distinct plane degrees have distinct sort keys. -/
theorem key_injective : Function.Injective (key (w := w)) := by
  intro x y h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx : (0 : ℚ) < x.fst + x.snd := by exact_mod_cast x.fst_add_snd_pos
  have hy : (0 : ℚ) < y.fst + y.snd := by exact_mod_cast y.fst_add_snd_pos
  rw [div_eq_div_iff hx.ne' hy.ne'] at h1
  have h1' : x.snd * (y.fst + y.snd) = y.snd * (x.fst + x.snd) := by exact_mod_cast h1
  rw [← h2] at h1'
  have hsnd : x.snd = y.snd := mul_right_cancel₀ x.fst_add_snd_pos.ne' h1'
  have hfst : x.fst = y.fst := by omega
  exact PlaneDegree.ext (Subtype.ext (Prod.ext hfst hsnd))

/-- Plane degrees are sorted counterclockwise from the first axis, collinear ones by size. -/
instance : LinearOrder (PlaneDegree w) := LinearOrder.lift' key key_injective

-- The order is lifted along `key`, so the next lemma holds by unfolding the lifted order.
/-- Plane degrees compare as their sort keys do. -/
theorem lt_iff_key_lt {x y : PlaneDegree w} : x < y ↔ x.key < y.key := Iff.rfl

/-- If `0 < x.det y` then `x < y` in the angular order. -/
theorem lt_of_det_pos {x y : PlaneDegree w} (h : 0 < x.det y) : x < y := by
  have hx : (0 : ℚ) < x.fst + x.snd := by exact_mod_cast x.fst_add_snd_pos
  have hy : (0 : ℚ) < y.fst + y.snd := by exact_mod_cast y.fst_add_snd_pos
  have h' : x.snd * y.fst < x.fst * y.snd := by rw [det_eq] at h; linarith
  have h'' : (x.snd : ℚ) * y.fst < x.fst * y.snd := by exact_mod_cast h'
  rw [lt_iff_key_lt, key, key, Prod.Lex.toLex_lt_toLex]
  refine Or.inl ?_
  rw [div_lt_div_iff₀ hx hy]
  linarith

/-- If the coefficient form `{x, y}` is positive then `x ≤ y` in the angular order. -/
theorem le_of_coefficientForm_pos {x y : PlaneDegree w}
    (h : 0 < E.coefficientForm ℚ x.vec y.vec) : x ≤ y := by
  rw [coefficientForm_det] at h
  exact (lt_of_det_pos (by exact_mod_cast h)).le

end PlaneDegree

end Mei.StandardPlane
