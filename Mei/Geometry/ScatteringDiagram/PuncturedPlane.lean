/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.ScatteringDiagram.CoordinateAxes

/-!
# A loop around the origin that is not null-homotopic in the punctured plane

Subdivide the axes of `ℝ × ℝ` into the origin and four closed half-axes. Give the half-axis
`w = {(x, 0) | 0 ≤ x}` a label `g` and the other three half-axes the label `1`, each wall
being cooriented by the coordinate vanishing on its axis, so that `w` is cooriented by `dy`.
The counterclockwise square loop `(1,1) → (-1,1) → (-1,-1) → (1,-1) → (1,1)` crosses `w` once,
from below, in its last edge, so its path product is `g⁻¹`, whereas the constant loop has
product `1` (`FiniteWallDiagram.pathProduct_positiveHalfAxis_squareLoop`).

Path products of homotopic paths agree once the labels kill the meridians of the joints
inside the region of homotopy (`FiniteWallDiagram.pathProduct_eq_of_homotopy`). The only joint
of this complex is the origin, so for a nontrivial label the square loop is not homotopic to
the constant loop, relative to its endpoints, through a homotopy avoiding the origin
(`FiniteWallDiagram.not_exists_homotopy_squareLoop_nil`). In the whole plane the origin is
available to the homotopy and carries the obstruction.

This is the example showing that the hypothesis on joints in the open region cannot be dropped
from homotopy invariance of path products.
-/

public section

open Set Mei.Convex Mei.FinitePolyhedralComplex

namespace Mei.FiniteWallDiagram

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {H : Type*}

section One

variable [One H]

open Classical in
/-- The diagram on the coordinate axes of the plane whose only nontrivial wall is the half-axis
through `(1, 0)`, labelled `g`. Every wall is cooriented by the coordinate vanishing on its
axis, so the wall through `(1, 0)` is cooriented by the second coordinate. -/
noncomputable def positiveHalfAxis (g : H) :
    FiniteWallDiagram (FinitePolyhedralComplex.coordinateAxes h) H where
  normal P := axisRow (coordinateAxesWallAxis h P)
  ker_normal P := (direction_eq_ker_of_mem_coordinateAxes_walls h P.property
    (subset_axisRow_coordinateAxesWallAxis h P)).symm
  label P := if ((1, 0) : ℝ × ℝ) ∈ (P : Set (ℝ × ℝ)) then g else 1

/-- Each wall is cooriented by the coordinate vanishing on it. -/
@[simp]
theorem positiveHalfAxis_normal (g : H) (P : (FinitePolyhedralComplex.coordinateAxes h).walls) :
    (positiveHalfAxis h g).normal P = axisRow (coordinateAxesWallAxis h P) := (rfl)

/-- The wall through `(1, 0)` carries `g`. -/
@[simp]
theorem positiveHalfAxis_label_of_mem (g : H)
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls} (hP : ((1, 0) : ℝ × ℝ) ∈ (P : Set _)) :
    (positiveHalfAxis h g).label P = g := by simp [positiveHalfAxis, hP]

/-- A wall missing `(1, 0)` carries `1`. -/
@[simp]
theorem positiveHalfAxis_label_of_notMem (g : H)
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls}
    (hP : ((1, 0) : ℝ × ℝ) ∉ (P : Set _)) : (positiveHalfAxis h g).label P = 1 := by
  simp [positiveHalfAxis, hP]

end One

variable [Group H]

/-- The square loop crosses the wall `w` once, from below, and no other wall of nontrivial
label, so its product is `g⁻¹`. -/
@[simp]
theorem pathProduct_positiveHalfAxis_squareLoop (g : H) :
    (positiveHalfAxis h g).pathProduct (coordinateAxesSquareLoop h) = g⁻¹ := by
  rw [coordinateAxesSquareLoop_def]
  simp only [pathProduct_cons]
  -- The first three edges cross walls of label `1`, at `(0, 1)`, `(-1, 0)` and `(0, -1)`.
  have he0 (e : offAxisPoint h (1, 1) one_ne_zero one_ne_zero ⟶
      offAxisPoint h (-1, 1) (by norm_num) one_ne_zero) :
      (positiveHalfAxis h g).pathProduct e.toPath = 1 := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq_of_axisRow_eq_zero h
      (positiveHalfAxis h g) e
      (j := false) (by simp) (t := 1 / 2) (by norm_num) (q := (0, 1))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_notMem h g
      (one_zero_notMem_of_mem_coordinateAxes_walls_of_snd_ne_zero h hP one_ne_zero)]
    simp
  have he1 (e : offAxisPoint h (-1, 1) (by norm_num) one_ne_zero ⟶
      offAxisPoint h (-1, -1) (by norm_num) (by norm_num)) :
      (positiveHalfAxis h g).pathProduct e.toPath = 1 := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq_of_axisRow_eq_zero h
      (positiveHalfAxis h g) e
      (j := true) (by simp) (t := 1 / 2) (by norm_num) (q := (-1, 0))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_notMem h g
      (one_zero_notMem_of_neg_one_zero_mem_coordinateAxes_walls h hP)]
    simp
  have he2 (e : offAxisPoint h (-1, -1) (by norm_num) (by norm_num) ⟶
      offAxisPoint h (1, -1) one_ne_zero (by norm_num)) :
      (positiveHalfAxis h g).pathProduct e.toPath = 1 := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq_of_axisRow_eq_zero h
      (positiveHalfAxis h g) e
      (j := false) (by simp) (t := 1 / 2) (by norm_num) (q := (0, -1))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_notMem h g
      (one_zero_notMem_of_mem_coordinateAxes_walls_of_snd_ne_zero h hP (by norm_num))]
    simp
  -- The last edge crosses the wall through `(1, 0)` upward.
  have he3 (e : offAxisPoint h (1, -1) one_ne_zero (by norm_num) ⟶
      offAxisPoint h (1, 1) one_ne_zero one_ne_zero) :
      (positiveHalfAxis h g).pathProduct e.toPath = g⁻¹ := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq_of_axisRow_eq_zero h
      (positiveHalfAxis h g) e
      (j := true) (by simp) (t := 1 / 2) (by norm_num) (q := (1, 0))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_mem h g hP, positiveHalfAxis_normal,
      coordinateAxesWallAxis_eq_true_of_one_zero_mem h hP]
    simp
  rw [he3, he2, he1, he0]
  simp

end Mei.FiniteWallDiagram

namespace Mei.FiniteWallDiagram

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- **A loop that is not null-homotopic in the punctured plane.** The square loop around the
origin is not homotopic relative to its endpoints, through a homotopy missing the origin, to
the constant loop. Labelling the half-axis by a nontrivial element of a group (here the
generator of `Multiplicative ℤ`), their path products are `g⁻¹` and `1`, and no joint of the
coordinate-axes complex lies in the punctured plane. -/
theorem not_exists_homotopy_squareLoop_nil :
    ¬ ∃ F : (coordinateAxesSquareLoop h).toContinuousPath.Homotopy
        (Quiver.Path.nil : AdmissiblePLPath (offAxisPoint h (1, 1) one_ne_zero one_ne_zero)
          (offAxisPoint h (1, 1) one_ne_zero one_ne_zero)).toContinuousPath,
      ∀ z, F z ∈ ({0}ᶜ : Set (ℝ × ℝ)) := by
  rintro ⟨F, hF⟩
  have hloop := (positiveHalfAxis h (Multiplicative.ofAdd (1 : ℤ))).pathProduct_eq_of_homotopy
    (support_coordinateAxes h) isOpen_compl_singleton (by simp) _ _ F hF
  rw [pathProduct_positiveHalfAxis_squareLoop, pathProduct_nil, inv_eq_one] at hloop
  exact absurd hloop (by decide)

end Mei.FiniteWallDiagram
