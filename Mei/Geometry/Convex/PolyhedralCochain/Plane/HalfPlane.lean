/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Plane.Basic
public import Mei.Geometry.Convex.PolyhedralCochain.CoboundaryPairing

/-!
# The coboundary of the upper half-plane

The upper half-plane `{y ≥ 0}` of `ℝ × ℝ`, with the standard orientation of a full-dimensional
cell, has exactly one boundary facet, the horizontal axis `{y = 0}`. The facet carries the
conormal orientation `+dy`: contracting `dy` with the outward vector `-∂ᵧ` gives the negative
of the orientation of the half-plane. Hence the coboundary of the half-plane with coefficient `c`
is the axis with orientation `+dy` and coefficient `c`.

The axis meets the vertical segment `γ(t) = (0, 1 - 2t)` transversally once, and `γ` crosses it
downwards, against `dy`. The pairing of the coboundary with `γ` is therefore `-c`: the
half-plane is the locally constant potential `c · 1_{y ≥ 0}`, which drops by `c` along `γ`. This
holds for every presentation of the coboundary cochain whose cells are transverse to `γ`.
-/

public section

open Set Module

namespace Mei

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]
  {h : TauCeti.Toric.IsIntegralLattice ((Int.castAddHom ℝ).prodMap (Int.castAddHom ℝ))}

namespace OrientedCell

variable (h) in
/-- The upper half-plane `{y ≥ 0}`, oriented by the constant `0`-form `1`. -/
noncomputable def upperHalfPlane : OrientedCell h 0 where
  carrier := {p | 0 ≤ p.2}
  rational := Plane.isRationalNormalPolyhedron_upperHalfPlane h
  nonempty := ⟨(0, 0), by simp⟩
  finrank_direction_add := by
    rw [direction_affineSpan, Plane.vectorSpan_upperHalfPlane]
    simp
  orientation := rayOfNeZero ℝ Plane.constOne Plane.constOne_ne_zero
  isConormal := (Module.Ray.isConormal_rayOfNeZero_iff _).mpr
    (Submodule.mem_conormalForms.mpr fun _ j => Fin.elim0 j)

@[simp]
theorem upperHalfPlane_carrier : (upperHalfPlane h).carrier = {p | 0 ≤ p.2} := (rfl)

@[simp]
theorem upperHalfPlane_orientation :
    (upperHalfPlane h).orientation = rayOfNeZero ℝ Plane.constOne Plane.constOne_ne_zero := (rfl)

variable (h) in
/-- The horizontal axis `{y = 0}`, oriented by the conormal form `+dy`. -/
noncomputable def horizontalLine : OrientedCell h 1 where
  carrier := {p | p.2 = 0}
  rational := Plane.isRationalNormalPolyhedron_horizontalLine h
  nonempty := ⟨(0, 0), rfl⟩
  finrank_direction_add := by
    rw [direction_affineSpan, Plane.vectorSpan_horizontalLine, Plane.finrank_horizontal]
    simp
  orientation := rayOfNeZero ℝ Plane.dy Plane.dy_ne_zero
  isConormal := by
    rw [direction_affineSpan, Plane.vectorSpan_horizontalLine]
    exact (Module.Ray.isConormal_rayOfNeZero_iff _).mpr Plane.dy_mem_conormalForms

@[simp]
theorem horizontalLine_carrier : (horizontalLine h).carrier = {p | p.2 = 0} := (rfl)

@[simp]
theorem horizontalLine_orientation :
    (horizontalLine h).orientation = rayOfNeZero ℝ Plane.dy Plane.dy_ne_zero := (rfl)

/-- A functional `(x, y) ↦ x * a + y * b` that attains its maximum over the upper half-plane at a
point `w` has `a = 0` and `b ≤ 0`: moving `w` horizontally by `±1` or up by `1` stays in the
half-plane. -/
private theorem eq_zero_and_le_zero_of_forall_le {a b : ℝ} {w : ℝ × ℝ} (hw : 0 ≤ w.2)
    (hmax : ∀ p : ℝ × ℝ, 0 ≤ p.2 → p.1 * a + p.2 * b ≤ w.1 * a + w.2 * b) :
    a = 0 ∧ b ≤ 0 := by
  have h₁ := hmax (w.1 + 1, w.2) hw
  have h₂ := hmax (w.1 - 1, w.2) hw
  have h₃ := hmax (w.1, w.2 + 1) (by simpa using hw.trans (by linarith))
  refine ⟨le_antisymm ?_ ?_, ?_⟩ <;> simp only at h₁ h₂ h₃ <;> linarith

/-- Every nonempty exposed set of the upper half-plane whose span has codimension one is the
horizontal axis. A supporting functional `a * x + b * y` has `a = 0` and `b ≤ 0`; `b = 0` exposes
the whole half-plane, which has the wrong dimension, and `b < 0` exposes the axis. -/
private theorem eq_axis_of_isExposed_upperHalfPlane {F : Set (ℝ × ℝ)}
    (hF : IsExposed ℝ (upperHalfPlane h).carrier F) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ (upperHalfPlane h).carrier)) :
    F = (horizontalLine h).carrier := by
  obtain ⟨l, hl⟩ := hF hne
  obtain ⟨w, hw⟩ := hne
  obtain ⟨a, b, hlp⟩ : ∃ a b : ℝ, ∀ p : ℝ × ℝ, l p = p.1 * a + p.2 * b := by
    refine ⟨l (1, 0), l (0, 1), fun p => ?_⟩
    have : p = p.1 • ((1, 0) : ℝ × ℝ) + p.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hl] at hw
  obtain ⟨hw0, hwmax⟩ := hw
  obtain ⟨ha, hb⟩ := eq_zero_and_le_zero_of_forall_le (a := a) (b := b) hw0 fun p hp => by
    simpa only [hlp] using hwmax p hp
  rcases hb.eq_or_lt with hb0 | hb0
  · exfalso
    have hl0 : F = (upperHalfPlane h).carrier := by
      rw [hl]
      ext x
      simp [hlp, ha, hb0]
    rw [hl0] at hdim
    omega
  · rw [hl]
    ext x
    simp only [upperHalfPlane_carrier, horizontalLine_carrier, mem_ofPred_eq, hlp, ha, mul_zero,
      zero_add]
    constructor
    · rintro ⟨hx0, hx⟩
      have := hx (x.1, 0) le_rfl
      dsimp only at this
      exact le_antisymm ((mul_le_mul_right_of_neg hb0).mp (by simpa using this)) hx0
    · intro hx
      refine ⟨hx.ge, fun y hy => ?_⟩
      rw [hx]
      exact mul_le_mul_of_nonpos_right (by simpa using hy) hb0.le

/-- The horizontal axis is an exposed set of the upper half-plane. -/
private theorem isExposed_horizontalLine :
    IsExposed ℝ (upperHalfPlane h).carrier (horizontalLine h).carrier := by
  intro _
  refine ⟨-FinitePolyhedralComplex.axisRow true, ?_⟩
  ext x
  simp only [horizontalLine_carrier, upperHalfPlane_carrier, mem_ofPred_eq, neg_apply,
    FinitePolyhedralComplex.axisRow_true_apply, neg_le_neg_iff]
  exact ⟨fun hx => ⟨hx.ge, fun y hy => by rwa [hx]⟩, fun ⟨hx0, hx⟩ =>
    le_antisymm (by simpa using hx (0, 0) le_rfl) hx0⟩

/-- The horizontal axis has the horizontal direction. -/
theorem direction_affineSpan_horizontalLine :
    (affineSpan ℝ (horizontalLine h).carrier).direction = Plane.horizontal := by
  rw [direction_affineSpan, horizontalLine_carrier, Plane.vectorSpan_horizontalLine]

/-- The horizontal axis has dimension one less than the upper half-plane. -/
private theorem finrank_vectorSpan_horizontalLine_add_one :
    finrank ℝ (vectorSpan ℝ (horizontalLine h).carrier) + 1 =
      finrank ℝ (vectorSpan ℝ (upperHalfPlane h).carrier) := by
  rw [horizontalLine_carrier, upperHalfPlane_carrier, Plane.vectorSpan_horizontalLine,
    Plane.vectorSpan_upperHalfPlane, Plane.finrank_horizontal]
  simp

/-- The horizontal axis with orientation `+dy` is the signed boundary facet of the upper
half-plane: contracting `dy` with the outward vector `-∂ᵧ` gives the negative of the
half-plane's orientation. -/
private theorem horizontalLine_eq_boundaryFacet
    (hF : IsExposed ℝ (upperHalfPlane h).carrier (horizontalLine h).carrier)
    (hne : (horizontalLine h).carrier.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ (horizontalLine h).carrier) + 1 =
      finrank ℝ (vectorSpan ℝ (upperHalfPlane h).carrier)) :
    horizontalLine h = (upperHalfPlane h).boundaryFacet hF hne hdim := by
  have hx : ((0, 1) : ℝ × ℝ) ∈ (upperHalfPlane h).carrier := by simp
  have hy : ((0, 0) : ℝ × ℝ) ∈ (horizontalLine h).carrier := rfl
  have hxF : ((0, 1) : ℝ × ℝ) ∉ (horizontalLine h).carrier := by simp
  refine ((upperHalfPlane h).eq_boundaryFacet_iff hF hne hdim _ rfl
    ⟨(0, 0) - (0, 1), vsub_mem_vectorSpan ℝ (hF.subset hy) hx⟩ ?_
    ((hF.outwardNormal_apply_pos_iff hne hdim hx hy).mpr hxF)).mpr ?_
  · rw [direction_affineSpan_horizontalLine]
    simp
  · simp only [horizontalLine_orientation, upperHalfPlane_orientation,
      Module.Ray.contract_rayOfNeZero, neg_rayOfNeZero]
    refine (ray_eq_iff _ _).mpr ?_
    have : Plane.dy.curryLeft ((0, 0) - (0, 1)) = -Plane.constOne := by
      ext w
      simp
    rw [this]
    exact SameRay.refl _

open Classical in
/-- The upper half-plane has exactly one signed boundary facet, the horizontal axis with
orientation `+dy`. -/
theorem upperHalfPlane_boundaryFacets :
    (upperHalfPlane h).boundaryFacets = {horizontalLine h} := by
  ext τ
  rw [mem_boundaryFacets, Finset.mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro ⟨F, hF, hne, hdim, rfl⟩
    have hFeq := eq_axis_of_isExposed_upperHalfPlane hF hne hdim
    subst hFeq
    exact (horizontalLine_eq_boundaryFacet hF hne hdim).symm
  · rintro rfl
    exact ⟨_, isExposed_horizontalLine, ⟨(0, 0), rfl⟩, finrank_vectorSpan_horizontalLine_add_one,
      horizontalLine_eq_boundaryFacet isExposed_horizontalLine ⟨(0, 0), rfl⟩
        finrank_vectorSpan_horizontalLine_add_one⟩

/-- The coboundary of the upper half-plane with coefficient `c` is the horizontal axis with
orientation `+dy` and coefficient `c`. -/
theorem upperHalfPlane_cellCoboundary (c : E) :
    (upperHalfPlane h).cellCoboundary (R := R) c = PolyhedralCochain.mk (horizontalLine h) c := by
  rw [cellCoboundary_apply, upperHalfPlane_boundaryFacets, Finset.sum_singleton]

/-- The vertical segment from `(0, 1)` to `(0, -1)` crosses the horizontal axis downwards,
against `dy`. -/
theorem intersectionIndex_horizontalLine_verticalSegment :
    (horizontalLine h).intersectionIndex ![((0 : ℝ), (1 : ℝ)), (0, -1)] = -1 := by
  rw [intersectionIndex_of_nonempty]
  · simp
  · refine ⟨(0, 0), ?_, rfl⟩
    rw [Matrix.range_cons_cons_empty, convexHull_pair]
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by ext <;> simp⟩

/-- The horizontal axis has empty relative boundary. -/
private theorem intrinsicFrontier_horizontalLine :
    intrinsicFrontier ℝ (horizontalLine h).carrier = ∅ := by
  have hpre : ((↑) : affineSpan ℝ (horizontalLine h).carrier → ℝ × ℝ) ⁻¹'
      (horizontalLine h).carrier = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hx0 : ((0, 0) : ℝ × ℝ) ∈ affineSpan ℝ (horizontalLine h).carrier :=
      subset_affineSpan ℝ _ rfl
    have := (AffineSubspace.vsub_right_mem_direction_iff_mem hx0 x.1).mpr x.2
    rw [direction_affineSpan_horizontalLine] at this
    simpa using this
  rw [intrinsicFrontier, hpre, frontier_univ, image_empty]

/-- The vertical segment is transverse to the horizontal axis. -/
theorem isTransverse_horizontalLine_verticalSegment :
    (horizontalLine h).IsTransverse ![((0 : ℝ), (1 : ℝ)), (0, -1)] where
  disjoint_intrinsicFrontier := by
    rw [intrinsicFrontier_horizontalLine]
    exact disjoint_empty _
  linearIndependent _ := by
    rw [direction_affineSpan_horizontalLine, linearIndependent_unique_iff]
    norm_num [Submodule.Quotient.mk_eq_zero]

end OrientedCell

namespace PolyhedralCochain

open OrientedCell

/-- The coboundary of the upper half-plane with coefficient `c` pairs with the segment from
`(0, 1)` to `(0, -1)` to give `-c`, for the signed boundary presentation. -/
theorem intersectionPairing_coboundaryPresentation_upperHalfPlane (c : E) :
    intersectionPairing (R := R) ![((0 : ℝ), (1 : ℝ)), (0, -1)]
      (coboundaryPresentation (R := R) (Finsupp.single (upperHalfPlane h) c)) = -c := by
  rw [coboundaryPresentation_single, upperHalfPlane_boundaryFacets, Finset.sum_singleton,
    intersectionPairing_single, intersectionIndex_horizontalLine_verticalSegment]
  simp

open Classical in
/-- Every presentation of the coboundary of the upper half-plane by cells transverse to the
segment from `(0, 1)` to `(0, -1)` pairs with it to give `-c`. -/
theorem intersectionPairing_eq_neg_of_ofFinsupp_eq_coboundary_upperHalfPlane (c : E)
    {y : OrientedCell h 1 →₀ E}
    (hy : ofFinsupp (R := R) y = coboundaryOfFinsupp (Finsupp.single (upperHalfPlane h) c))
    (hT : ∀ τ ∈ y.support, τ.IsTransverse ![((0 : ℝ), (1 : ℝ)), (0, -1)]) :
    intersectionPairing (R := R) ![((0 : ℝ), (1 : ℝ)), (0, -1)] y = -c := by
  rw [← intersectionPairing_coboundaryPresentation_upperHalfPlane (R := R) (h := h) c]
  refine intersectionPairing_eq_coboundaryPresentation_of_ofFinsupp_eq c hy (fun τ hτ => ?_) hT
  rw [upperHalfPlane_boundaryFacets, Finset.mem_singleton] at hτ
  rw [hτ]
  exact isTransverse_horizontalLine_verticalSegment

end PolyhedralCochain

end Mei
