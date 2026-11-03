/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Affine.Arrangement
public import Mei.Geometry.Convex.PolyhedralComplex.CoordinateAxes
public import Mei.Geometry.Convex.PolyhedralComplex.Discriminant

/-!
# Two examples of endpoint discriminants

Backward broken lines from an endpoint `Q` run along the line `Q + ℝ v` for a velocity `v`.
An endpoint is generic for the singular-sweep part of the discriminant exactly when none of
these lines meets the affine span of a cell of codimension at least two
(`FinitePolyhedralComplex.singularDiscriminant`). Two examples show what the genericity
condition does and does not control.

* Genericity is not detected by the chamber of the endpoint. For the coordinate axes of the plane
  and the velocity `(1, 1)`, every point of the open positive quadrant lies off all walls, and
  hence in an open chamber, while the points of the diagonal in it are not generic: their line
  through the origin is a joint incidence
  (`FinitePolyhedralComplex.exists_isOpen_notMem_walls_not_isGeneric_coordinateAxes_diagonal`).
* Countably many arrangements have a dense common generic locus
  (`ExceptionalArrangement.dense_iInter_isGeneric`), but this locus need not be open,
  and a common generic point need not have a generic neighbourhood. The points
  `1 / (j + 1)` accumulate at the common generic point `0`
  (`ExceptionalArrangement.isGeneric_pointArrangement_zero`,
  `ExceptionalArrangement.not_isOpen_setOf_forall_isGeneric_pointArrangement`).
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
    rfl
  refine (coordinateAxes h).add_smul_notMem_singularSupport_walls hgen
    (Finset.mem_singleton_self _) (-s) ?_
  convert h0 using 1
  ext <;> simp

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

namespace Mei.ExceptionalArrangement

/-- The arrangement of the single point `1 / (j + 1)` of the line. -/
noncomputable def pointArrangement (j : ℕ) : ExceptionalArrangement ℝ :=
  ofAffineForms (fun _ : Unit =>
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap + AffineMap.const ℝ ℝ (-(1 / ((j : ℝ) + 1))))

/-- A point is generic for `pointArrangement j` when it differs from `1 / (j + 1)`. -/
@[simp]
theorem isGeneric_pointArrangement_iff (j : ℕ) (x : ℝ) :
    (pointArrangement j).IsGeneric x ↔ x ≠ 1 / ((j : ℝ) + 1) := by
  have hid : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ≠ 0 := fun h0 => by simpa using LinearMap.congr_fun h0 1
  simp [pointArrangement, isGeneric_ofAffineForms_iff, hid, sub_eq_zero, ← sub_eq_add_neg]

/-- The origin is generic for every arrangement of the family. -/
theorem isGeneric_pointArrangement_zero (j : ℕ) : (pointArrangement j).IsGeneric 0 := by
  simp only [isGeneric_pointArrangement_iff]
  positivity

/-- No neighbourhood of the common generic point `0` is generic for all arrangements
`pointArrangement j`: the exceptional points `1 / (j + 1)` accumulate at `0`. -/
theorem exists_not_isGeneric_pointArrangement_of_mem_nhds {U : Set ℝ} (hU : U ∈ 𝓝 (0 : ℝ)) :
    ∃ j : ℕ, ∃ x ∈ U, ¬ (pointArrangement j).IsGeneric x := by
  have hlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨j, hj⟩ := (hlim.eventually hU).exists
  exact ⟨j, _, hj, by simp⟩

/-- The common generic locus of the family `pointArrangement` contains `0` but is not
open, in contrast to the finite case (`isOpen_isGeneric`). -/
theorem not_isOpen_setOf_forall_isGeneric_pointArrangement :
    ¬ IsOpen {x : ℝ | ∀ j, (pointArrangement j).IsGeneric x} := by
  intro hopen
  obtain ⟨j, x, hx, hxj⟩ := exists_not_isGeneric_pointArrangement_of_mem_nhds
    (hopen.mem_nhds (fun j => isGeneric_pointArrangement_zero j))
  exact hxj (hx j)

end Mei.ExceptionalArrangement
