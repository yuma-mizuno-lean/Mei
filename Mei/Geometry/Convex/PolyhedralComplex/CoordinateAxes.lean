/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.AmbientSubdivision
public import Mei.Geometry.Convex.PolyhedralComplex.Star
public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mei.Analysis.Convex.Sign
public import Mei.LinearAlgebra.AffineSpace.Ordered

/-!
# The coordinate axes of the plane

The two coordinate functionals of `ℝ × ℝ` cut the plane into the closures of their realized
sign cells: four closed quadrants, four closed half-axes and the origin. This is the smallest
complex on which wall-crossing products around a joint can be computed by hand.

Every wall of this complex lies in one coordinate axis, and its direction is that axis
(`FinitePolyhedralComplex.coordinateAxesWallAxis_eq_iff`). A point lies on a wall exactly
when one of its coordinates vanishes, and the only singular point of the wall family is the
origin (`FinitePolyhedralComplex.singularSupport_coordinateAxes`). Consequently a segment along
which one coordinate keeps a strict sign is admissible.

The complex is `FinitePolyhedralComplex.ofArrangement` of the coordinate rows. The wall
classification uses `Mei.Convex.exists_zero_sign_of_affineSpan_ne_top`, and the singular
support is computed from
`FinitePolyhedralComplex.singularSupport_walls_subset_support_codimensionAtLeast`.
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

/-- The coordinate functionals of the plane: `axisRow false` is the first coordinate and
`axisRow true` the second, so `axisRow true` vanishes on the horizontal axis. -/
def axisRow (j : Bool) : (ℝ × ℝ) →L[ℝ] ℝ :=
  bif j then ContinuousLinearMap.snd ℝ ℝ ℝ else ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The row `false` is the first coordinate. -/
@[simp]
theorem axisRow_false_apply (v : ℝ × ℝ) : axisRow false v = v.1 := (rfl)

/-- The row `true` is the second coordinate. -/
@[simp]
theorem axisRow_true_apply (v : ℝ × ℝ) : axisRow true v = v.2 := (rfl)

/-- Both coordinate functionals are nonzero. -/
theorem axisRow_ne_zero (j : Bool) : axisRow j ≠ 0 := by
  intro h0
  have := congrArg (fun f : (ℝ × ℝ) →L[ℝ] ℝ => f (1, 1)) h0
  cases j <;> simp at this

/-- A coordinate with equal nonzero signs at the endpoints stays nonzero along the segment. -/
theorem axisRow_lineMap_ne_zero_of_sign_eq {j : Bool} {v w : ℝ × ℝ} {t : ℝ}
    (hvw : SignType.sign (axisRow j v) = SignType.sign (axisRow j w))
    (hv : axisRow j v ≠ 0) (ht : t ∈ Icc (0 : ℝ) 1) :
    axisRow j (AffineMap.lineMap v w t) ≠ 0 := by
  have hs : SignType.sign (axisRow j (AffineMap.lineMap v w t)) =
      SignType.sign (axisRow j v) := by
    have hl : axisRow j (AffineMap.lineMap v w t) =
        AffineMap.lineMap (axisRow j v) (axisRow j w) t :=
      (axisRow j).toLinearMap.toAffineMap.apply_lineMap v w t
    rw [hl]
    exact (convex_setOf_sign_eq (SignType.sign (axisRow j v))).lineMap_mem rfl hvw.symm ht
  intro hz
  apply hv
  apply sign_eq_zero_iff.mp
  rw [← hs, hz, sign_zero]

/-- Points closer to `θ` than `θ` is to a coordinate axis lie on the same side of that axis. -/
theorem sign_axisRow_eq_of_dist_lt {j : Bool} {v θ : ℝ × ℝ} (hv : dist v θ < |axisRow j θ|) :
    SignType.sign (axisRow j v) = SignType.sign (axisRow j θ) := by
  have hd : |axisRow j v - axisRow j θ| < |axisRow j θ| := by
    refine lt_of_le_of_lt ?_ hv
    rw [Prod.dist_eq]
    cases j <;> simp only [axisRow_false_apply, axisRow_true_apply, ← Real.dist_eq]
    · exact le_max_left _ _
    · exact le_max_right _ _
  rcases lt_trichotomy (axisRow j θ) 0 with hn | h0 | hp
  · rw [abs_of_neg hn] at hd
    rw [sign_neg hn, sign_neg (by linarith [(abs_sub_lt_iff.mp hd).1])]
  · exact absurd hd (by simp [h0])
  · rw [abs_of_pos hp] at hd
    rw [sign_pos hp, sign_pos (by linarith [(abs_sub_lt_iff.mp hd).2])]

/-- The two coordinate axes are different lines. -/
private theorem ker_axisRow_true_ne :
    LinearMap.ker (axisRow true).toLinearMap ≠ LinearMap.ker (axisRow false).toLinearMap := by
  intro he
  have h10 : ((1, 0) : ℝ × ℝ) ∈ LinearMap.ker (axisRow true).toLinearMap := by simp
  rw [he] at h10
  simp at h10

variable (h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ)))

/-- The coordinate rows are rational for the standard lattice. -/
theorem isRationalFunctional_axisRow (j : Bool) :
    Toric.IsRationalFunctional h (axisRow j).toLinearMap := by
  cases j
  · convert Toric.IsRationalFunctional.realCharacter h (LinearMap.fst ℤ ℤ ℤ) using 1
    exact h.eq_realCharacter (by intro x; simp)
  · convert Toric.IsRationalFunctional.realCharacter h (LinearMap.snd ℤ ℤ ℤ) using 1
    exact h.eq_realCharacter (by intro x; simp)

/-- The subdivision of the plane by its two coordinate axes. -/
noncomputable def coordinateAxes : FinitePolyhedralComplex h :=
  ofArrangement (fun j => (axisRow j).toContinuousAffineMap) (isRationalFunctional_axisRow h)

/-- The coordinate-axes complex is the arrangement complex of the two coordinate rows. -/
theorem coordinateAxes_eq_ofArrangement :
    coordinateAxes h =
      ofArrangement (fun j => (axisRow j).toContinuousAffineMap) (isRationalFunctional_axisRow h) :=
  (rfl)

/-- The coordinate axes subdivide the entire plane. -/
@[simp]
theorem support_coordinateAxes : (coordinateAxes h).support = univ := by
  rw [coordinateAxes_eq_ofArrangement]
  exact support_ofArrangement _ _

/-- Every wall of the coordinate-axes complex lies in a coordinate axis. -/
theorem exists_subset_axisRow_eq_zero_of_mem_coordinateAxes_walls {P : Set (ℝ × ℝ)}
    (hP : P ∈ (coordinateAxes h).walls) : ∃ j, P ⊆ {v | axisRow j v = 0} := by
  have hd := (coordinateAxes h).finrank_direction_add_one_of_mem_walls hP
  have hPC := (coordinateAxes h).mem_cells_of_mem_walls hP
  rw [coordinateAxes_eq_ofArrangement] at hPC
  obtain ⟨σ, hσ, rfl⟩ := mem_ofArrangement_cells.mp hPC
  have hspan : affineSpan ℝ
      (closure (signCell (fun j => (axisRow j).toContinuousAffineMap) σ)) ≠ ⊤ :=
    AffineSubspace.ne_top_of_finrank_direction_add_one_eq _ hd
  obtain ⟨j, hj⟩ := exists_zero_sign_of_affineSpan_ne_top hσ hspan
  refine ⟨j, fun v hv => ?_⟩
  rw [closure_signCell hσ] at hv
  simpa using (mem_weakSignCell.mp hv j).1 hj

/-- Each point of a coordinate axis lies on a wall contained in that axis. -/
theorem exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero {j : Bool} {v : ℝ × ℝ}
    (hv : axisRow j v = 0) :
    ∃ P ∈ (coordinateAxes h).walls, v ∈ P ∧ P ⊆ {w | axisRow j w = 0} := by
  rw [coordinateAxes_eq_ofArrangement]
  have hne : (axisRow j).toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
    intro h0
    apply axisRow_ne_zero j
    apply ContinuousLinearMap.coe_injective
    exact h0
  simpa using exists_mem_ofArrangement_walls_subset_zeroLocus
    (fun j => (axisRow j).toContinuousAffineMap) (isRationalFunctional_axisRow h) hne
    (x := v) (by simpa using hv)

/-- A wall in a coordinate axis has that axis as its direction. -/
theorem direction_eq_ker_of_mem_coordinateAxes_walls {P : Set (ℝ × ℝ)}
    (hP : P ∈ (coordinateAxes h).walls)
    {j : Bool} (hPj : P ⊆ {v | axisRow j v = 0}) :
    (affineSpan ℝ P).direction = LinearMap.ker (axisRow j).toLinearMap := by
  exact ((axisRow j).toLinearMap.ker_eq_direction_affineSpan
    (by exact_mod_cast axisRow_ne_zero j) (fun v hv => hPj hv)
    ((coordinateAxes h).finrank_direction_add_one_of_mem_walls hP)).symm

/-- No wall lies in both coordinate axes. -/
private theorem not_subset_axisRow_true_and_false {P : Set (ℝ × ℝ)}
    (hP : P ∈ (coordinateAxes h).walls) (htrue : P ⊆ {v | axisRow true v = 0})
    (hfalse : P ⊆ {v | axisRow false v = 0}) : False :=
  ker_axisRow_true_ne ((direction_eq_ker_of_mem_coordinateAxes_walls h hP htrue).symm.trans
    (direction_eq_ker_of_mem_coordinateAxes_walls h hP hfalse))

open Classical in
/-- The coordinate axis containing a wall: `true` for the horizontal axis, where the second
coordinate vanishes, and `false` for the vertical axis. -/
noncomputable def coordinateAxesWallAxis (P : (coordinateAxes h).walls) : Bool :=
  decide ((P : Set (ℝ × ℝ)) ⊆ {v | axisRow true v = 0})

/-- A wall lies in the axis named by `coordinateAxesWallAxis`, and in no other. -/
theorem coordinateAxesWallAxis_eq_iff (P : (coordinateAxes h).walls) (j : Bool) :
    coordinateAxesWallAxis h P = j ↔ (P : Set (ℝ × ℝ)) ⊆ {v | axisRow j v = 0} := by
  cases j
  · simp only [coordinateAxesWallAxis, decide_eq_false_iff_not]
    constructor
    · intro htrue
      obtain ⟨j, hj⟩ := exists_subset_axisRow_eq_zero_of_mem_coordinateAxes_walls h P.property
      cases j
      · exact hj
      · exact (htrue hj).elim
    · exact fun hfalse htrue => not_subset_axisRow_true_and_false h P.property htrue hfalse
  · simp [coordinateAxesWallAxis]

/-- Every wall lies in its named coordinate axis. -/
theorem subset_axisRow_coordinateAxesWallAxis (P : (coordinateAxes h).walls) :
    (P : Set (ℝ × ℝ)) ⊆ {v | axisRow (coordinateAxesWallAxis h P) v = 0} :=
  (coordinateAxesWallAxis_eq_iff h P _).mp rfl

/-- A point lies on a wall exactly when one of its coordinates vanishes. -/
theorem exists_mem_coordinateAxes_walls_iff {v : ℝ × ℝ} :
    (∃ P : (coordinateAxes h).walls, v ∈ (P : Set (ℝ × ℝ))) ↔ ∃ j, axisRow j v = 0 := by
  constructor
  · rintro ⟨P, hv⟩
    exact ⟨_, subset_axisRow_coordinateAxesWallAxis h P hv⟩
  · rintro ⟨j, hj⟩
    obtain ⟨P, hP, hv, -⟩ := exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero h hj
    exact ⟨⟨P, hP⟩, hv⟩

/-- Every wall of the coordinate-axes complex lies in a closed half-plane bounded by the
vertical axis: no wall crosses from one half-axis to the opposite one. -/
theorem fst_nonneg_or_fst_nonpos_of_mem_coordinateAxes_walls {P : Set (ℝ × ℝ)}
    (hP : P ∈ (coordinateAxes h).walls) : (∀ v ∈ P, 0 ≤ v.1) ∨ ∀ v ∈ P, v.1 ≤ 0 := by
  have hPC := (coordinateAxes h).mem_cells_of_mem_walls hP
  rw [coordinateAxes_eq_ofArrangement] at hPC
  obtain ⟨σ, hσ, rfl⟩ := mem_ofArrangement_cells.mp hPC
  rw [closure_signCell hσ]
  have hrow (v : ℝ × ℝ) (hv : v ∈ weakSignCell (fun j => (axisRow j).toContinuousAffineMap) σ) :=
    mem_weakSignCell.mp hv false
  cases hs : σ false
  · exact Or.inl fun v hv => by simpa using ((hrow v hv).1 hs).ge
  · exact Or.inr fun v hv => by simpa using (hrow v hv).2.1 hs
  · exact Or.inl fun v hv => by simpa using (hrow v hv).2.2 hs

/-- The codimension-two skeleton of the coordinate-axes complex is contained in the origin. -/
theorem support_codimensionAtLeast_two_coordinateAxes_subset :
    ((coordinateAxes h).codimensionAtLeast 2).support ⊆ {0} := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := mem_support.mp hx
  obtain ⟨hQC, hdim⟩ := ((coordinateAxes h).mem_codimensionAtLeast_cells 2 Q).mp hQ
  have hbot : (affineSpan ℝ Q).direction = ⊥ :=
    Submodule.finrank_eq_zero.mp (by
      rw [Module.finrank_prod, Module.finrank_self] at hdim
      omega)
  rw [coordinateAxes_eq_ofArrangement] at hQC
  obtain ⟨σ, hσ, rfl⟩ := mem_ofArrangement_cells.mp hQC
  -- Cells of a linear arrangement contain the origin.
  have h0 : (0 : ℝ × ℝ) ∈
      closure (signCell (fun j => (axisRow j).toContinuousAffineMap) σ) := by
    rw [closure_signCell hσ, mem_weakSignCell]
    intro j
    simp
  have hmem := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hxQ)
    (subset_affineSpan ℝ _ h0)
  rw [hbot, Submodule.mem_bot, vsub_eq_sub, sub_zero] at hmem
  exact hmem

/-- The only singular point of the walls of the coordinate axes is the origin. -/
@[simp]
theorem singularSupport_coordinateAxes :
    singularSupport (fun P : (coordinateAxes h).walls => (P : Set (ℝ × ℝ))) = {0} := by
  apply Subset.antisymm
  · exact fun x hx => support_codimensionAtLeast_two_coordinateAxes_subset h
      ((coordinateAxes h).singularSupport_walls_subset_support_codimensionAtLeast hx)
  · rintro x rfl
    obtain ⟨P, hP, hP0, hPt⟩ :=
      exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero h (j := true) (v := 0) (by simp)
    obtain ⟨Q, hQ, hQ0, hQf⟩ :=
      exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero h (j := false) (v := 0) (by simp)
    refine mem_singularSupport.mpr (Or.inr ⟨⟨P, hP⟩, ⟨Q, hQ⟩, ?_, hP0, hQ0⟩)
    rw [direction_eq_ker_of_mem_coordinateAxes_walls h hP hPt,
      direction_eq_ker_of_mem_coordinateAxes_walls h hQ hQf]
    exact ker_axisRow_true_ne

/-- Both coordinates of an off-wall point are nonzero. -/
theorem axisRow_val_ne_zero
    (x : WallComplement (fun P : (coordinateAxes h).walls => (P : Set (ℝ × ℝ)))) (j : Bool) :
    axisRow j x.val ≠ 0 := by
  intro hj
  obtain ⟨P, hP, hxP, -⟩ := exists_mem_coordinateAxes_walls_subset_of_axisRow_eq_zero h hj
  exact x.notMem ⟨P, hP⟩ hxP

/-- A segment between off-wall points along whose endpoints one coordinate has the same sign
is admissible: it avoids the origin, the only singular point. -/
theorem admissibleSegment_coordinateAxes_of_sign_eq
    {x y : WallComplement (fun P : (coordinateAxes h).walls => (P : Set (ℝ × ℝ)))} {j : Bool}
    (hxy : SignType.sign (axisRow j x.val) = SignType.sign (axisRow j y.val)) :
    WallComplement.AdmissibleSegment x y := by
  refine (convex_segment x.val y.val).admissibleSegment_of_disjoint_singularSupport ?_
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  rw [singularSupport_coordinateAxes, disjoint_singleton_right, segment_eq_image_lineMap]
  rintro ⟨t, ht, h0⟩
  apply axisRow_lineMap_ne_zero_of_sign_eq hxy (axisRow_val_ne_zero h x j) ht
  rw [h0, map_zero]

/-- A point of the plane with both coordinates nonzero, as a vertex of admissible paths
through the coordinate axes. -/
def offAxisPoint (v : ℝ × ℝ) (h₁ : v.1 ≠ 0) (h₂ : v.2 ≠ 0) :
    WallComplement (fun P : (coordinateAxes h).walls => (P : Set (ℝ × ℝ))) where
  val := v
  notMem P hv := by
    obtain ⟨j, hj⟩ := (exists_mem_coordinateAxes_walls_iff h).mp ⟨P, hv⟩
    cases j
    · exact h₁ hj
    · exact h₂ hj

/-- An off-axis vertex sits at the given point. -/
@[simp]
theorem offAxisPoint_val (v : ℝ × ℝ) (h₁ : v.1 ≠ 0) (h₂ : v.2 ≠ 0) :
    (offAxisPoint h v h₁ h₂).val = v := (rfl)

variable {h} in
/-- A segment along which the coordinate `!j` keeps its sign crosses only walls of the axis
`j`: at a crossing the coordinate `!j` cannot vanish. -/
theorem coordinateAxesWallAxis_eq_of_mem_crossings {j : Bool}
    {x y : WallComplement
      (fun P : (FinitePolyhedralComplex.coordinateAxes h).walls => (P : Set (ℝ × ℝ)))}
    (hxy : SignType.sign (axisRow (!j) x.val) = SignType.sign (axisRow (!j) y.val))
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls} {t : ℝ}
    (hc : (P, t) ∈ WallComplement.crossings x y) : coordinateAxesWallAxis h P = j := by
  obtain ⟨ht, hP⟩ := (WallComplement.mem_crossings _ _ _ _).mp hc
  by_contra hne
  have hzero := subset_axisRow_coordinateAxesWallAxis h P hP
  rw [Bool.eq_not.mpr hne] at hzero
  exact axisRow_lineMap_ne_zero_of_sign_eq hxy (axisRow_val_ne_zero h x (!j)) ht hzero

variable {h} in
/-- A segment along which the coordinate `!j` keeps its sign meets at most one wall: if it
crosses the wall `P` at the parameter `t`, then `(P, t)` is its only crossing. -/
theorem crossings_eq_singleton_of_mem_crossings {j : Bool}
    {x y : WallComplement
      (fun P : (FinitePolyhedralComplex.coordinateAxes h).walls => (P : Set (ℝ × ℝ)))}
    (hxy : SignType.sign (axisRow (!j) x.val) = SignType.sign (axisRow (!j) y.val))
    {P : (FinitePolyhedralComplex.coordinateAxes h).walls} {t : ℝ}
    (hc : (P, t) ∈ WallComplement.crossings x y) :
    WallComplement.crossings x y = {(P, t)} := by
  ext ⟨Q, s⟩
  rw [Set.mem_singleton_iff, Prod.mk.injEq]
  refine ⟨fun hs => ?_, ?_⟩
  · have hs' := (WallComplement.mem_crossings _ _ _ _).mp hs
    have ht' := (WallComplement.mem_crossings _ _ _ _).mp hc
    have hzs : axisRow j (AffineMap.lineMap x.val y.val s) = 0 := by
      have := subset_axisRow_coordinateAxesWallAxis h Q hs'.2
      rwa [coordinateAxesWallAxis_eq_of_mem_crossings hxy hs] at this
    have hzt : axisRow j (AffineMap.lineMap x.val y.val t) = 0 := by
      have := subset_axisRow_coordinateAxesWallAxis h P ht'.2
      rwa [coordinateAxesWallAxis_eq_of_mem_crossings hxy hc] at this
    -- Along the segment the coordinate `j` vanishes at one parameter only.
    have hst : s = t := by
      have hmul := (axisRow j).toLinearMap.apply_lineMap_sub_mul (c := 0) hzt s
      simp only [ContinuousLinearMap.coe_coe, hzs, sub_zero, zero_mul] at hmul
      have := mul_eq_zero.mp hmul.symm
      exact (sub_eq_zero.mp (this.resolve_left (axisRow_val_ne_zero h x j))).symm
    subst hst
    refine ⟨?_, rfl⟩
    refine FinitePolyhedralComplex.eq_of_mem_wall_of_notMem_singularSupport
      (C := FinitePolyhedralComplex.coordinateAxes h) hs'.2 ht'.2 ?_
    rw [singularSupport_coordinateAxes, mem_singleton_iff]
    intro h0
    exact axisRow_lineMap_ne_zero_of_sign_eq hxy (axisRow_val_ne_zero h x (!j)) hs'.1
      (by rw [h0, map_zero])
  · rintro ⟨rfl, rfl⟩
    exact hc

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

/-- The square loop is the concatenation of its four counterclockwise edges. -/
theorem coordinateAxesSquareLoop_def :
    coordinateAxesSquareLoop h =
      (((Quiver.Hom.toPath
        (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := true) (by simp)⟩ :
          offAxisPoint h (1, 1) one_ne_zero one_ne_zero ⟶
            offAxisPoint h (-1, 1) (by norm_num) one_ne_zero)).cons
        (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := false) (by simp)⟩ :
          _ ⟶ offAxisPoint h (-1, -1) (by norm_num) (by norm_num))).cons
        (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := true) (by simp)⟩ :
          _ ⟶ offAxisPoint h (1, -1) one_ne_zero (by norm_num))).cons
        (⟨admissibleSegment_coordinateAxes_of_sign_eq h (j := false) (by simp)⟩ :
          _ ⟶ offAxisPoint h (1, 1) one_ne_zero one_ne_zero) := (rfl)

/-- The ambient vertices of the counterclockwise square loop around the origin. -/
@[simp]
theorem coordinateAxesSquareLoop_vertices :
    (coordinateAxesSquareLoop h).vertices.map WallComplement.val =
      [(1, 1), (-1, 1), (-1, -1), (1, -1), (1, 1)] := by
  simp [coordinateAxesSquareLoop, Quiver.Path.vertices_cons, Quiver.Path.vertices_toPath]

/-- A wall through a point off the horizontal axis lies in the vertical axis, so it misses
`(1, 0)`. -/
theorem one_zero_notMem_of_mem_coordinateAxes_walls_of_snd_ne_zero
    {P : (coordinateAxes h).walls} {v : ℝ × ℝ} (hv : v ∈ (P : Set _)) (h₂ : v.2 ≠ 0) :
    ((1, 0) : ℝ × ℝ) ∉ (P : Set _) := by
  intro h10
  have hv0 := subset_axisRow_coordinateAxesWallAxis h P hv
  have h10' := subset_axisRow_coordinateAxesWallAxis h P h10
  cases hj : coordinateAxesWallAxis h P <;> simp_all

/-- No wall of the coordinate axes contains both `(1, 0)` and `(-1, 0)`. -/
theorem one_zero_notMem_of_neg_one_zero_mem_coordinateAxes_walls
    {P : (coordinateAxes h).walls} (hv : ((-1, 0) : ℝ × ℝ) ∈ (P : Set _)) :
    ((1, 0) : ℝ × ℝ) ∉ (P : Set _) := by
  intro h10
  rcases fst_nonneg_or_fst_nonpos_of_mem_coordinateAxes_walls h P.property with hP | hP
  · linarith [hP _ hv]
  · linarith [hP _ h10]

/-- A wall of the coordinate axes through `(1, 0)` lies in the horizontal axis, whose
coordinate is the second one. -/
theorem coordinateAxesWallAxis_eq_true_of_one_zero_mem
    {P : (coordinateAxes h).walls} (hv : ((1, 0) : ℝ × ℝ) ∈ (P : Set _)) :
    coordinateAxesWallAxis h P = true := by
  have := subset_axisRow_coordinateAxesWallAxis h P hv
  cases hj : coordinateAxesWallAxis h P <;> simp_all

/-- The coordinate-axes complex has no joint meridian in the punctured plane: its only joint is
the origin, which every isolating triangle must meet. -/
@[simp]
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
