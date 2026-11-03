/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A joint obstructs the straight segment between its two sides

Take the two lines `x = 0` and `x = y` of `ℝ × ℝ`. They meet only at the origin and have
different directions, so the origin is a singular point of the pair. The points `(-1, 1)` and
`(1, -1)` lie on neither line, but the segment between them passes through the origin. An
admissible path must avoid the singular support, so the segment is not an admissible edge, and
with no free vertex there is no admissible path from `(-1, 1)` to `(1, -1)`
(`Mei.Convex.TwoLines.isEmpty_hom`).

Admissible chains do exist once a free vertex is allowed:
`Mei.Convex.AdmissiblePLPath.exists_length_eq_two` supplies one with two edges
(`Mei.Convex.TwoLines.exists_admissiblePLPath`). The example shows that the requirement of a
free vertex for the admissibility of a path cannot be dropped.
-/

public section

open Set

namespace Mei.Convex.TwoLines

/-- The defining functionals of the lines `x = 0` (`false`) and `x = y` (`true`). -/
def row : Bool → (ℝ × ℝ) →L[ℝ] ℝ
  | false => ContinuousLinearMap.fst ℝ ℝ ℝ
  | true => ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The functional of the line `x = 0` is the first coordinate. -/
@[simp]
theorem row_false_apply (v : ℝ × ℝ) : row false v = v.1 := (rfl)

/-- The functional of the line `x = y` is the difference of the coordinates. -/
@[simp]
theorem row_true_apply (v : ℝ × ℝ) : row true v = v.1 - v.2 := (rfl)

/-- The two lines `x = 0` and `x = y` of the plane, as a family of walls. -/
def lines (i : Bool) : Set (ℝ × ℝ) := LinearMap.ker (row i).toLinearMap

/-- A point lies on a line when its defining functional vanishes. -/
@[simp]
theorem mem_lines {i : Bool} {v : ℝ × ℝ} : v ∈ lines i ↔ row i v = 0 := LinearMap.mem_ker

/-- Both defining functionals are nonzero. -/
theorem row_ne_zero (i : Bool) : (row i).toLinearMap ≠ 0 := by
  intro h0
  have := LinearMap.congr_fun h0 (1, 0)
  cases i <;> simp [row] at this

/-- The direction of each line is the kernel of its functional. -/
theorem direction_affineSpan_lines (i : Bool) :
    (affineSpan ℝ (lines i)).direction = LinearMap.ker (row i).toLinearMap := by
  rw [lines, ← Submodule.coe_toAffineSubspace, AffineSubspace.affineSpan_coe,
    Submodule.toAffineSubspace_direction]

/-- The origin is a singular point: the two lines meet there with different directions. -/
theorem zero_mem_singularSupport : (0 : ℝ × ℝ) ∈ singularSupport lines := by
  refine mem_singularSupport.mpr (Or.inr ⟨false, true, ?_, by simp, by simp⟩)
  rw [direction_affineSpan_lines, direction_affineSpan_lines]
  intro he
  have h01 : ((0, 1) : ℝ × ℝ) ∈ LinearMap.ker (row false).toLinearMap := by simp [row]
  rw [he] at h01
  simp [row] at h01

/-- The point `(-1, 1)`, on neither line. -/
def left : WallComplement lines :=
  ⟨(-1, 1), fun i => by cases i <;> norm_num [row]⟩

/-- The point `(1, -1)`, on neither line. -/
def right : WallComplement lines :=
  ⟨(1, -1), fun i => by cases i <;> norm_num [row]⟩

/-- The coordinates of the point `(-1, 1)`. -/
@[simp]
theorem left_val : left.val = (-1, 1) := (rfl)

/-- The coordinates of the point `(1, -1)`. -/
@[simp]
theorem right_val : right.val = (1, -1) := (rfl)

/-- The segment from `(-1, 1)` to `(1, -1)` passes through the origin. -/
theorem lineMap_left_right : AffineMap.lineMap left.val right.val (1 / 2 : ℝ) = 0 := by
  ext <;> norm_num [left, right, AffineMap.lineMap_apply]

/-- **No admissible edge from `(-1, 1)` to `(1, -1)`.** Without a free vertex there is no
admissible path between these allowed endpoints: the only polygonal path is the straight
segment, which meets the singular origin. -/
theorem isEmpty_hom : IsEmpty (left ⟶ right) := by
  refine ⟨fun e => ?_⟩
  refine e.down.regular (1 / 2) ⟨by norm_num, by norm_num⟩ ?_
  rw [lineMap_left_right]
  exact zero_mem_singularSupport

/-- Each line is a convex polyhedron. -/
theorem isConvexPolyhedron_lines (i : Bool) : TauCeti.IsConvexPolyhedron (lines i) := by
  have h := (TauCeti.isConvexPolyhedron_setOf_le (row i).toContinuousAffineMap).inter
    (TauCeti.isConvexPolyhedron_setOf_le (-(row i).toContinuousAffineMap))
  convert h using 1
  ext v
  simp [le_antisymm_iff, and_comm]

/-- **A free vertex repairs the obstruction.** The two endpoints are joined by an admissible
chain with two edges. -/
theorem exists_admissiblePLPath : ∃ p : AdmissiblePLPath left right, p.length = 2 :=
  AdmissiblePLPath.exists_length_eq_two isConvexPolyhedron_lines
    (fun i => by
      rw [direction_affineSpan_lines, Module.finrank_prod, Module.finrank_self]
      simpa using Module.Dual.finrank_ker_add_one_of_ne_zero (row_ne_zero i))
    left right

end Mei.Convex.TwoLines
