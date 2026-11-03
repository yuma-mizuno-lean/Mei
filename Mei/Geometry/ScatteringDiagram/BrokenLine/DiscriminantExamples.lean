/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CoordinateAxes
public import Mei.Geometry.Convex.PolyhedralComplex.Discriminant

/-!
# An example of endpoint discriminants

Backward broken lines from an endpoint `Q` run along the line `Q + ℝ v` for a velocity `v`.
An endpoint is generic for the singular-sweep part of the discriminant exactly when none of
these lines meets the affine span of a cell of codimension at least two
(`FinitePolyhedralComplex.singularDiscriminant`). An example shows what the genericity
condition does not control.

Genericity is not detected by the chamber of the endpoint. For the coordinate axes of the plane
and the velocity `(1, 1)`, every point of the open positive quadrant lies off all walls, and
hence in an open chamber, while the points of the diagonal in it are not generic: their line
through the origin is a joint incidence
(`FinitePolyhedralComplex.exists_isOpen_notMem_walls_not_isGeneric_coordinateAxes_diagonal`).
-/

public section

open Set Filter Topology

namespace Mei.FinitePolyhedralComplex

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- A point of the plane with both coordinates positive lies on no wall of the coordinate
axes. -/
theorem coordinateAxes_notMem_walls_of_pos {v : ℝ × ℝ} (h₁ : 0 < v.1) (h₂ : 0 < v.2)
    (P : (coordinateAxes h).walls) : v ∉ (P : Set (ℝ × ℝ)) := by
  intro hv
  obtain ⟨j, hj⟩ := (exists_mem_coordinateAxes_walls_iff h).mp ⟨P, hv⟩
  cases j <;> simp only [axisRow_false_apply, axisRow_true_apply] at hj <;> linarith

/-- The points of the diagonal are not generic for the singular sweeps of the coordinate axes
along `(1, 1)`: the line through such a point in that direction passes through the joint at
the origin. -/
theorem not_isGeneric_singularDiscriminant_coordinateAxes_diagonal (s : ℝ) :
    ¬ ((coordinateAxes h).singularDiscriminant {((1 : ℝ), (1 : ℝ))}).IsGeneric (s, s) := by
  intro hgen
  have h0 : (0 : ℝ × ℝ) ∈ Convex.singularSupport
      (fun P : (coordinateAxes h).walls => (P : Set (ℝ × ℝ))) := by
    rw [singularSupport_coordinateAxes]
    exact Set.mem_singleton _
  refine (coordinateAxes h).add_smul_notMem_singularSupport_walls hgen
    (Finset.mem_singleton_self _) (-s) ?_
  have hsum : ((s, s) : ℝ × ℝ) + (-s) • ((1 : ℝ), (1 : ℝ)) = 0 := by ext <;> simp
  rw [hsum]
  exact h0

/-- Check for the singular-sweep discriminant of the coordinate axes. A point `(s, s)` of the
diagonal with `s > 0` has an open neighbourhood missing every wall, so it lies in an open
chamber, yet it is not generic for the sweeps along `(1, 1)`. -/
theorem exists_isOpen_notMem_walls_not_isGeneric_coordinateAxes_diagonal {s : ℝ}
    (hs : 0 < s) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (s, s) ∈ U ∧ (∀ v ∈ U, ∀ P : (coordinateAxes h).walls,
        v ∉ (P : Set (ℝ × ℝ))) ∧
      ¬ ((coordinateAxes h).singularDiscriminant {((1 : ℝ), (1 : ℝ))}).IsGeneric (s, s) :=
  ⟨{v | 0 < v.1 ∧ 0 < v.2},
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd),
    ⟨hs, hs⟩, fun _ hv => coordinateAxes_notMem_walls_of_pos h hv.1 hv.2,
    not_isGeneric_singularDiscriminant_coordinateAxes_diagonal h s⟩

end Mei.FinitePolyhedralComplex
