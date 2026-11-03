/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CoordinateAxes
public import Mei.Geometry.ScatteringDiagram.Finite

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
of this complex is the origin, so for `g ≠ 1` the square loop is not homotopic to the constant
loop, relative to its endpoints, through a homotopy avoiding the origin
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
theorem positiveHalfAxis_label_of_mem (g : H)
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls} (hP : ((1, 0) : ℝ × ℝ) ∈ (P : Set _)) :
    (positiveHalfAxis h g).label P = g := by simp [positiveHalfAxis, hP]

/-- A wall missing `(1, 0)` carries `1`. -/
theorem positiveHalfAxis_label_of_notMem (g : H)
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls}
    (hP : ((1, 0) : ℝ × ℝ) ∉ (P : Set _)) : (positiveHalfAxis h g).label P = 1 := by
  simp [positiveHalfAxis, hP]

end One

/-- A wall through a point off the horizontal axis lies in the vertical axis, so it misses
`(1, 0)`. -/
private theorem one_zero_notMem_of_mem_of_snd_ne_zero
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls} {v : ℝ × ℝ} (hv : v ∈ (P : Set _))
    (h₂ : v.2 ≠ 0) : ((1, 0) : ℝ × ℝ) ∉ (P : Set _) := by
  intro h10
  have hv0 := subset_axisRow_coordinateAxesWallAxis h P hv
  have h10' := subset_axisRow_coordinateAxesWallAxis h P h10
  cases hj : coordinateAxesWallAxis h P <;> simp_all

/-- No wall contains both `(1, 0)` and `(-1, 0)`. -/
private theorem one_zero_notMem_of_neg_one_zero_mem
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls}
    (hv : ((-1, 0) : ℝ × ℝ) ∈ (P : Set _)) : ((1, 0) : ℝ × ℝ) ∉ (P : Set _) := by
  intro h10
  rcases fst_nonneg_or_fst_nonpos_of_mem_coordinateAxes_walls h P.property with hP | hP
  · linarith [hP _ hv]
  · linarith [hP _ h10]

/-- A wall through `(1, 0)` is cooriented by the second coordinate. -/
private theorem coordinateAxesWallAxis_eq_true_of_one_zero_mem
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls}
    (hv : ((1, 0) : ℝ × ℝ) ∈ (P : Set _)) : coordinateAxesWallAxis h P = true := by
  have := subset_axisRow_coordinateAxesWallAxis h P hv
  cases hj : coordinateAxesWallAxis h P <;> simp_all

variable [Group H]

/-- A segment along which one coordinate keeps its sign and which meets the other axis at an
interior parameter crosses exactly one wall, through that point, and its product is the
corresponding signed label. -/
private theorem exists_pathProduct_toPath_eq
    (D : FiniteWallDiagram (FinitePolyhedralComplex.coordinateAxes h) H) {j : Bool}
    {x y : WallComplement
      (fun P : (FinitePolyhedralComplex.coordinateAxes h).walls => (P : Set (ℝ × ℝ)))}
    (e : x ⟶ y) (hxy : SignType.sign (axisRow (!j) x.val) = SignType.sign (axisRow (!j) y.val))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {q : ℝ × ℝ} (hq : AffineMap.lineMap x.val y.val t = q)
    (hz : axisRow j q = 0) :
    ∃ P : (FinitePolyhedralComplex.coordinateAxes h).walls, q ∈ (P : Set (ℝ × ℝ)) ∧
      D.pathProduct e.toPath =
        if 0 < D.normal P (y.val - x.val) then (D.label P)⁻¹ else D.label P := by
  subst hq
  obtain ⟨P, hP, hmem, -⟩ := exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero h hz
  have hc : (⟨P, hP⟩, t) ∈ WallComplement.crossings x y :=
    (WallComplement.mem_crossings _ _ _ _).mpr ⟨Ioo_subset_Icc_self ht, hmem⟩
  exact ⟨⟨P, hP⟩, hmem, D.pathProduct_toPath_eq_of_crossings_eq_singleton e
    (crossings_eq_singleton_of_mem_crossings hxy hc)⟩

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
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq h (positiveHalfAxis h g) e
      (j := false) (by simp) (t := 1 / 2) (by norm_num) (q := (0, 1))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_notMem h g
      (one_zero_notMem_of_mem_of_snd_ne_zero h hP one_ne_zero)]
    simp
  have he1 (e : offAxisPoint h (-1, 1) (by norm_num) one_ne_zero ⟶
      offAxisPoint h (-1, -1) (by norm_num) (by norm_num)) :
      (positiveHalfAxis h g).pathProduct e.toPath = 1 := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq h (positiveHalfAxis h g) e
      (j := true) (by simp) (t := 1 / 2) (by norm_num) (q := (-1, 0))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_notMem h g (one_zero_notMem_of_neg_one_zero_mem h hP)]
    simp
  have he2 (e : offAxisPoint h (-1, -1) (by norm_num) (by norm_num) ⟶
      offAxisPoint h (1, -1) one_ne_zero (by norm_num)) :
      (positiveHalfAxis h g).pathProduct e.toPath = 1 := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq h (positiveHalfAxis h g) e
      (j := false) (by simp) (t := 1 / 2) (by norm_num) (q := (0, -1))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_notMem h g
      (one_zero_notMem_of_mem_of_snd_ne_zero h hP (by norm_num))]
    simp
  -- The last edge crosses the wall through `(1, 0)` upward.
  have he3 (e : offAxisPoint h (1, -1) one_ne_zero (by norm_num) ⟶
      offAxisPoint h (1, 1) one_ne_zero one_ne_zero) :
      (positiveHalfAxis h g).pathProduct e.toPath = g⁻¹ := by
    obtain ⟨P, hP, hprod⟩ := exists_pathProduct_toPath_eq h (positiveHalfAxis h g) e
      (j := true) (by simp) (t := 1 / 2) (by norm_num) (q := (1, 0))
      (by ext <;> norm_num [AffineMap.lineMap_apply]) (by simp)
    rw [hprod, positiveHalfAxis_label_of_mem h g hP, positiveHalfAxis_normal,
      coordinateAxesWallAxis_eq_true_of_one_zero_mem h hP]
    simp
  rw [he3, he2, he1, he0]
  simp

end Mei.FiniteWallDiagram

namespace Mei.FinitePolyhedralComplex

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The coordinate-axes complex has no joint meridian in the punctured plane: its only joint is
the origin, which every isolating triangle must meet. -/
theorem jointMeridianWords_coordinateAxes_compl_zero
    (ν : (coordinateAxes h).walls → ℝ × ℝ →ₗ[ℝ] ℝ) :
    (coordinateAxes h).jointMeridianWords ν ({0}ᶜ : Set (ℝ × ℝ)) = ∅ := by
  refine eq_empty_of_forall_notMem fun g hg => ?_
  obtain ⟨J, -, hJ⟩ := ((coordinateAxes h).mem_jointMeridianWords ν _ g).mp hg
  obtain ⟨x, y, z, e, f, r, q, -, -, hU, -, hinter, -⟩ :=
    ((coordinateAxes h).mem_jointTriangleWords ν J _ g).mp hJ
  have hq : q ∈ convexHull ℝ {x.val, y.val, z.val} ∩
      ((coordinateAxes h).codimensionAtLeast 2).support := by
    rw [hinter]
    rfl
  exact hU hq.1 (support_codimensionAtLeast_two_coordinateAxes_subset h hq.2)

end Mei.FinitePolyhedralComplex

namespace Mei.FiniteWallDiagram

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {H : Type*} [Group H]

/-- **A loop that is not null-homotopic in the punctured plane.** For `g ≠ 1`, the square loop
around the origin is not homotopic relative to its endpoints, through a homotopy missing the
origin, to the constant loop: their path products are `g⁻¹` and `1`, and no joint of the
coordinate-axes complex lies in the punctured plane. -/
theorem not_exists_homotopy_squareLoop_nil {g : H} (hg : g ≠ 1) :
    ¬ ∃ F : (coordinateAxesSquareLoop h).toContinuousPath.Homotopy
        (Quiver.Path.nil : AdmissiblePLPath (offAxisPoint h (1, 1) one_ne_zero one_ne_zero)
          (offAxisPoint h (1, 1) one_ne_zero one_ne_zero)).toContinuousPath,
      ∀ z, F z ∈ ({0}ᶜ : Set (ℝ × ℝ)) := by
  rintro ⟨F, hF⟩
  have hloop := (positiveHalfAxis h g).pathProduct_eq_of_homotopy (support_coordinateAxes h)
    isOpen_compl_singleton (by simp [jointMeridianWords_coordinateAxes_compl_zero]) _ _ F hF
  rw [pathProduct_positiveHalfAxis_squareLoop, pathProduct_nil, inv_eq_one] at hloop
  exact hg hloop

end Mei.FiniteWallDiagram
