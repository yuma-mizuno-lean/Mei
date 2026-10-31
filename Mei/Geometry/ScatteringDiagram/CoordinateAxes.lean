/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CoordinateAxes
public import Mei.Geometry.ScatteringDiagram.LocalProduct

/-!
# The commutator diagram on the coordinate axes

Label the walls on the horizontal axis of `ℝ × ℝ` by `a`, cooriented by the second
coordinate, and the walls on the vertical axis by `b`, cooriented by the first coordinate.
The counterclockwise square loop `(1,1) → (-1,1) → (-1,-1) → (1,-1) → (1,1)` crosses
`b, a, b⁻¹, a⁻¹` in this order, so its path product is `a⁻¹ * b⁻¹ * a * b`. Hence the
diagram is consistent exactly when `a` and `b` commute: without commutativity the path
product of a loop around a joint need not vanish.

Along a segment on which one coordinate keeps its sign, only walls on the other axis are
crossed, at most once. Its product is therefore read off from the signs of the varying
coordinate at its endpoints (`FiniteWallDiagram.pathProduct_coordinateAxes_toPath`). For
commuting labels these single-axis formulas are the local crossing formulas of
`FiniteWallDiagram.consistent_of_local` for the potential
`coordinateAxesFactor a b true * coordinateAxesFactor a b false`, which records the open
quadrant.

This is the basic example accompanying the definition of path products and consistency in
Tom Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*,
[arXiv:1603.00416](https://arxiv.org/abs/1603.00416), Definitions 2.1–2.2.
-/

public section

open Set Mei.Convex Mei.FinitePolyhedralComplex

namespace Mei.FiniteWallDiagram

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {H : Type*}

/-- The diagram on the coordinate axes of the plane whose walls on the horizontal axis carry
`a` and are cooriented by the second coordinate, and whose walls on the vertical axis carry
`b` and are cooriented by the first coordinate. -/
noncomputable def coordinateAxes (a b : H) :
    FiniteWallDiagram (FinitePolyhedralComplex.coordinateAxes h) H where
  normal P := axisRow (coordinateAxesWallAxis h P)
  ker_normal P := (direction_eq_ker_of_mem_coordinateAxes_walls h P.property
    (subset_axisRow_coordinateAxesWallAxis h P)).symm
  label P := cond (coordinateAxesWallAxis h P) a b

/-- Each wall is cooriented by the coordinate vanishing on it. -/
@[simp]
theorem coordinateAxes_normal (a b : H) (P : (FinitePolyhedralComplex.coordinateAxes h).walls) :
    (coordinateAxes h a b).normal P = axisRow (coordinateAxesWallAxis h P) := (rfl)

/-- Horizontal walls carry `a` and vertical walls carry `b`. -/
@[simp]
theorem coordinateAxes_label (a b : H) (P : (FinitePolyhedralComplex.coordinateAxes h).walls) :
    (coordinateAxes h a b).label P = cond (coordinateAxesWallAxis h P) a b := (rfl)

/-- Relabelling the coordinate-axes diagram relabels its two labels. -/
@[simp]
theorem relabel_coordinateAxes {K : Type*} [Group H] [Group K] (a b : H) (f : H →* K) :
    (coordinateAxes h a b).relabel f = coordinateAxes h (f a) (f b) := by
  refine FiniteWallDiagram.ext (funext fun P => by simp) (funext fun P => ?_)
  rw [relabel_label, coordinateAxes_label, coordinateAxes_label]
  cases coordinateAxesWallAxis h P <;> rfl

/-- The crossing factor of the axis `j` at `v`: the inverse of the label of that axis on its
positive side, and `1` elsewhere. Crossing the axis `j` from `x` to `y` multiplies by
`coordinateAxesFactor a b j y * (coordinateAxesFactor a b j x)⁻¹`. -/
noncomputable def coordinateAxesFactor [Inv H] [One H] (a b : H) (j : Bool) (v : ℝ × ℝ) : H :=
  if 0 < axisRow j v then (cond j a b)⁻¹ else 1

/-- The crossing factor is the inverse label on the positive side of its axis. -/
theorem coordinateAxesFactor_def [Inv H] [One H] (a b : H) (j : Bool) (v : ℝ × ℝ) :
    coordinateAxesFactor a b j v = if 0 < axisRow j v then (cond j a b)⁻¹ else 1 := (rfl)

/-- The crossing factor depends only on the side of its axis. -/
theorem coordinateAxesFactor_eq_of_sign_eq [Inv H] [One H] (a b : H) {j : Bool} {v w : ℝ × ℝ}
    (hvw : SignType.sign (axisRow j v) = SignType.sign (axisRow j w)) :
    coordinateAxesFactor a b j v = coordinateAxesFactor a b j w := by
  simp only [coordinateAxesFactor_def, ← sign_eq_one_iff, hvw]

variable [Group H]

/-- Factors of different axes commute when the two labels do. -/
private theorem commute_coordinateAxesFactor {a b : H} (hab : Commute a b) (v w : ℝ × ℝ) :
    Commute (coordinateAxesFactor a b true v) (coordinateAxesFactor a b false w) := by
  simp only [coordinateAxesFactor_def]
  split_ifs <;> simp [hab.inv_inv]

variable {h} in
/-- A segment along which the coordinate `!j` keeps its sign crosses only walls of the axis
`j`: at a crossing the coordinate `!j` cannot vanish. -/
private theorem coordinateAxesWallAxis_eq_of_mem_crossings {j : Bool}
    {x y : WallComplement
      (fun P : (FinitePolyhedralComplex.coordinateAxes h).walls => (P : Set (ℝ × ℝ)))}
    (hxy : SignType.sign (axisRow (!j) x.val) = SignType.sign (axisRow (!j) y.val))
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls} {t : ℝ}
    (hc : (P, t) ∈ WallComplement.crossings x y) : coordinateAxesWallAxis h P = j := by
  obtain ⟨ht, hP⟩ := (WallComplement.mem_crossings _ _ _ _).mp hc
  by_contra hne
  have hzero := subset_axisRow_coordinateAxesWallAxis h P hP
  have hl : axisRow (!j) (AffineMap.lineMap x.val y.val t) =
      AffineMap.lineMap (axisRow (!j) x.val) (axisRow (!j) y.val) t :=
    (axisRow (!j)).toLinearMap.toAffineMap.apply_lineMap x.val y.val t
  rw [Bool.eq_not.mpr hne] at hzero
  have hs := (convex_setOf_sign_eq (SignType.sign (axisRow (!j) x.val))).lineMap_mem
    rfl hxy.symm ht
  rw [Set.mem_ofPred_eq, ← hl, hzero, sign_zero, eq_comm, sign_eq_zero_iff] at hs
  exact axisRow_val_ne_zero h x (!j) hs

/-- A segment along which the coordinate `!j` keeps its sign crosses only walls of the axis
`j`, at most once. Its product is therefore determined by the sides of the axis `j` containing
its endpoints: crossing to the positive side contributes the inverse label, crossing to the
nonpositive side the label. -/
theorem pathProduct_coordinateAxes_toPath (a b : H) (j : Bool)
    {x y : WallComplement
      (fun P : (FinitePolyhedralComplex.coordinateAxes h).walls => (P : Set (ℝ × ℝ)))}
    (e : x ⟶ y) (hxy : SignType.sign (axisRow (!j) x.val) = SignType.sign (axisRow (!j) y.val)) :
    (coordinateAxes h a b).pathProduct e.toPath =
      coordinateAxesFactor a b j y.val * (coordinateAxesFactor a b j x.val)⁻¹ := by
  let C := FinitePolyhedralComplex.coordinateAxes h
  have hx := axisRow_val_ne_zero h x j
  have hy := axisRow_val_ne_zero h y j
  -- Every crossing is a zero of the coordinate `j`, at a positive parameter.
  have hzero {c : C.walls × ℝ} (hc : c ∈ C.orderedCrossings e) :
      axisRow j (AffineMap.lineMap x.val y.val c.2) = 0 ∧ 0 < c.2 := by
    have hc' := (C.mem_orderedCrossings e c).mp hc
    have hz := subset_axisRow_coordinateAxesWallAxis h c.1
      ((WallComplement.mem_crossings _ _ _ _).mp hc').2
    rw [coordinateAxesWallAxis_eq_of_mem_crossings hxy hc'] at hz
    exact ⟨hz, (WallComplement.mem_Ioo_of_mem_crossings hc').1⟩
  -- After a crossing at `s`, the coordinate `j` has the sign opposite to its sign at `x`.
  have hafter {s r : ℝ} (hs : axisRow j (AffineMap.lineMap x.val y.val s) = 0) (hs0 : 0 < s)
      (hr : s < r) : axisRow j (AffineMap.lineMap x.val y.val r) * axisRow j x.val < 0 := by
    simpa using (axisRow j).toLinearMap.mul_neg_of_lt_of_apply_lineMap hs hs0
      (by simpa using hx) hr
  rw [pathProduct_toPath]
  rcases hlist : C.orderedCrossings e with _ | ⟨c, _ | ⟨c', l⟩⟩
  · -- No crossing: by the intermediate value theorem, `x` and `y` lie on the same side.
    have hsame : (0 < axisRow j y.val ↔ 0 < axisRow j x.val) := by
      by_contra hne
      have h0 : (0 : ℝ) ∈ uIcc (axisRow j x.val) (axisRow j y.val) := by
        rw [mem_uIcc]
        by_cases hpy : 0 < axisRow j y.val <;> by_cases hpx : 0 < axisRow j x.val
        · exact absurd (iff_of_true hpy hpx) hne
        · exact Or.inl ⟨not_lt.mp hpx, hpy.le⟩
        · exact Or.inr ⟨not_lt.mp hpy, hpx.le⟩
        · exact absurd (iff_of_false hpy hpx) hne
      have hcont : ContinuousOn (fun t : ℝ => axisRow j (AffineMap.lineMap x.val y.val t))
          (uIcc 0 1) :=
        ((axisRow j).continuous.comp AffineMap.lineMap_continuous).continuousOn
      obtain ⟨t, ht, hzt⟩ := intermediate_value_uIcc hcont (by simpa using h0)
      obtain ⟨P, hP, hmem, -⟩ := exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero h hzt
      have hc := (C.mem_orderedCrossings e (⟨P, hP⟩, t)).mpr
        ((WallComplement.mem_crossings _ _ _ _).mpr ⟨by simpa using ht, hmem⟩)
      simp [hlist] at hc
    by_cases hpos : 0 < axisRow j x.val <;>
      simp only [List.reverse_nil, List.map_nil, List.prod_nil, coordinateAxesFactor_def, hpos,
        hsame, ite_true, ite_false, inv_one, mul_one, mul_inv_cancel]
  · -- One crossing: `x` and `y` lie on opposite sides.
    have hc : c ∈ C.orderedCrossings e := by simp [hlist]
    obtain ⟨hzc, hc0⟩ := hzero hc
    have hopp : axisRow j y.val * axisRow j x.val < 0 := by
      rcases lt_or_eq_of_le (((WallComplement.mem_crossings _ _ _ _).mp
          ((C.mem_orderedCrossings e c).mp hc)).1.2) with hc1 | hc1
      · simpa using hafter hzc hc0 hc1
      · exact absurd (by simpa [hc1] using hzc) hy
    have hj := coordinateAxesWallAxis_eq_of_mem_crossings hxy ((C.mem_orderedCrossings e c).mp hc)
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, coordinateAxes_normal,
      coordinateAxes_label, hj, map_sub, coordinateAxesFactor_def]
    rcases lt_or_gt_of_ne hx with hx' | hx'
    · have hy' : 0 < axisRow j y.val := pos_of_mul_neg_left hopp hx'.le
      simp [hy', not_lt.mpr hx'.le, sub_pos.mpr (hx'.trans hy')]
    · have hy' : axisRow j y.val < 0 := neg_of_mul_neg_left hopp hx'.le
      simp [hx', not_lt.mpr hy'.le, not_lt.mpr (sub_nonpos.mpr (hy'.trans hx').le)]
  · -- Two crossings: the coordinate `j` would vanish after its first zero.
    have hpair := C.pairwise_orderedCrossings e
    rw [hlist] at hpair
    obtain ⟨hzc, hc0⟩ := hzero (c := c) (by simp [hlist])
    have hlt := hafter hzc hc0 ((List.pairwise_cons.mp hpair).1 c' (by simp))
    rw [(hzero (c := c') (by simp [hlist])).1, zero_mul] at hlt
    exact absurd hlt (lt_irrefl 0)

end Mei.FiniteWallDiagram

namespace Mei.FinitePolyhedralComplex

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The counterclockwise square loop `(1,1) → (-1,1) → (-1,-1) → (1,-1) → (1,1)` around the
origin, as an admissible path through the coordinate axes. Each edge keeps one coordinate
fixed, so it crosses one half-axis transversally. -/
noncomputable def coordinateAxesSquareLoop :
    AdmissiblePLPath (offAxisPoint h (1, 1) one_ne_zero one_ne_zero)
      (offAxisPoint h (1, 1) one_ne_zero one_ne_zero) :=
  (((Quiver.Hom.toPath
    (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := true) (by simp)⟩ :
      offAxisPoint h (1, 1) one_ne_zero one_ne_zero ⟶
        offAxisPoint h (-1, 1) (by norm_num) one_ne_zero)).cons
    (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := false) (by simp)⟩ :
      _ ⟶ offAxisPoint h (-1, -1) (by norm_num) (by norm_num))).cons
    (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := true) (by simp)⟩ :
      _ ⟶ offAxisPoint h (1, -1) one_ne_zero (by norm_num))).cons
    (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := false) (by simp)⟩ :
      _ ⟶ offAxisPoint h (1, 1) one_ne_zero one_ne_zero)

end Mei.FinitePolyhedralComplex

namespace Mei.FiniteWallDiagram

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))
  {H : Type*} [Group H]

/-- The square loop crosses `b, a, b⁻¹, a⁻¹` in this order, so its product is the commutator
`a⁻¹ * b⁻¹ * a * b`. -/
theorem pathProduct_coordinateAxes_squareLoop (a b : H) :
    (coordinateAxes h a b).pathProduct (coordinateAxesSquareLoop h) = a⁻¹ * b⁻¹ * a * b := by
  simp only [coordinateAxesSquareLoop, pathProduct_cons]
  rw [pathProduct_coordinateAxes_toPath h a b true _ (by simp),
    pathProduct_coordinateAxes_toPath h a b false _ (by simp),
    pathProduct_coordinateAxes_toPath h a b true _ (by simp),
    pathProduct_coordinateAxes_toPath h a b false _ (by simp)]
  norm_num [coordinateAxesFactor_def, mul_assoc]

/-- For commuting labels, the product of every short segment near a regular wall point is
the change of the potential `coordinateAxesFactor a b true * coordinateAxesFactor a b false`. -/
private theorem pathProduct_coordinateAxes_toPath_of_commute {a b : H} (hab : Commute a b)
    (P : (FinitePolyhedralComplex.coordinateAxes h).walls) {θ : ℝ × ℝ} (hθP : θ ∈ (P : Set _))
    (hθ : θ ∉ singularSupport
      (fun Q : (FinitePolyhedralComplex.coordinateAxes h).walls => (Q : Set (ℝ × ℝ)))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (x y : WallComplement
        (fun Q : (FinitePolyhedralComplex.coordinateAxes h).walls => (Q : Set (ℝ × ℝ))))
      (e : x ⟶ y), dist x.val θ < ε → dist y.val θ < ε →
      (coordinateAxes h a b).pathProduct e.toPath =
        coordinateAxesFactor a b true y.val * coordinateAxesFactor a b false y.val *
          (coordinateAxesFactor a b true x.val * coordinateAxesFactor a b false x.val)⁻¹ := by
  have hθj : axisRow (coordinateAxesWallAxis h P) θ = 0 :=
    subset_axisRow_coordinateAxesWallAxis h P hθP
  generalize coordinateAxesWallAxis h P = j at hθj
  -- Off the origin, `θ` lies off the other axis.
  have hθn : axisRow (!j) θ ≠ 0 := by
    intro hn
    rw [singularSupport_coordinateAxes] at hθ
    apply hθ
    cases j <;> simp only [Bool.not_false, Bool.not_true, axisRow_false_apply,
      axisRow_true_apply] at hθj hn <;> ext <;> simp [hθj, hn]
  refine ⟨|axisRow (!j) θ|, abs_pos.mpr hθn, fun x y e hx hy => ?_⟩
  have hxy := (sign_axisRow_eq_of_dist_lt hx).trans (sign_axisRow_eq_of_dist_lt hy).symm
  rw [pathProduct_coordinateAxes_toPath h a b j e hxy]
  have hsame := coordinateAxesFactor_eq_of_sign_eq a b hxy
  cases j <;> simp only [Bool.not_false, Bool.not_true] at hsame <;> rw [← hsame]
  · -- Crossing the vertical axis: the horizontal factor commutes past.
    rw [(commute_coordinateAxesFactor hab x.val y.val).eq, mul_inv_rev,
      ← (commute_coordinateAxesFactor hab x.val x.val).inv_inv.eq]
    group
  · group

/-- The coordinate-axes diagram is consistent exactly when its two labels commute. -/
theorem consistent_coordinateAxes_iff (a b : H) :
    (coordinateAxes h a b).Consistent ↔ Commute a b := by
  constructor
  · intro hc
    have hloop := (coordinateAxes h a b).consistent_iff_loops.mp hc _
      (coordinateAxesSquareLoop h)
    rw [pathProduct_coordinateAxes_squareLoop] at hloop
    rw [← Commute.inv_inv_iff, ← commutatorElement_eq_one_iff_commute, commutatorElement_def,
      inv_inv, inv_inv]
    exact hloop
  · intro hab
    refine (coordinateAxes h a b).consistent_of_local
      (F := fun v => coordinateAxesFactor a b true v * coordinateAxesFactor a b false v) ?_
      fun P θ hθP hθ => ?_
    · -- Off the walls, both coordinates keep their signs nearby.
      intro θ hθ
      have hθ' (k : Bool) : axisRow k θ ≠ 0 := fun hk =>
        (exists_mem_coordinateAxes_walls_iff h).mpr ⟨k, hk⟩ |>.elim fun P hP => hθ P hP
      filter_upwards [Metric.ball_mem_nhds θ (abs_pos.mpr (hθ' true)),
        Metric.ball_mem_nhds θ (abs_pos.mpr (hθ' false))] with v ht hf
      rw [coordinateAxesFactor_eq_of_sign_eq a b (sign_axisRow_eq_of_dist_lt ht),
        coordinateAxesFactor_eq_of_sign_eq a b (sign_axisRow_eq_of_dist_lt hf)]
    · obtain ⟨ε, hε, hseg⟩ := pathProduct_coordinateAxes_toPath_of_commute h hab P hθP hθ
      exact ⟨ε, hε, fun x y e hx hy _ => hseg x y e hx hy⟩

end Mei.FiniteWallDiagram
