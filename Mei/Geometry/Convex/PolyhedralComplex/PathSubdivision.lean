/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.Geometry.Convex.Polyhedron.SegmentSubdivision

/-!
# Crossing words under path subdivision

Inserting an allowed vertex inside an admissible segment preserves its signed
crossing word. The ordered crossing list is the concatenation of the two
subsegment lists, with their parameters rescaled to the original interval.
The rescalings have positive slopes, so signs and traversal order are preserved.
The same equality holds when the subdivided edge lies inside a longer polygonal path.

We use the membership and strict-order characterization `orderedCrossings_eq_iff`
and Mathlib's list append, map and product operations; no wall-label relations are needed.
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}
  {t : ℝ}

/-- The crossing list splits at an inserted allowed vertex, retaining the original times. -/
theorem orderedCrossings_subdivide (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    C.orderedCrossings e =
      ((C.orderedCrossings e₁).map fun a => (a.1, a.2 * t)) ++
      ((C.orderedCrossings e₂).map fun a => (a.1, 1 - (1 - a.2) * (1 - t))) := by
  symm
  apply (C.orderedCrossings_eq_iff e _).mpr
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr ((C.pairwise_orderedCrossings e₁).imp ?_),
      List.pairwise_map.mpr ((C.pairwise_orderedCrossings e₂).imp ?_), ?_⟩
    · intro a b hab
      exact mul_lt_mul_of_pos_right hab ht.1
    · intro a b hab
      dsimp
      nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2)]
    · intro a ha b hb
      obtain ⟨a, ha₀, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb₀, rfl⟩ := List.mem_map.mp hb
      have ha' := (WallComplement.mem_crossings x z a.1 a.2).mp
        ((C.mem_orderedCrossings e₁ a).mp ha₀)
      have hb' := (WallComplement.mem_crossings z y b.1 b.2).mp
        ((C.mem_orderedCrossings e₂ b).mp hb₀)
      have ha'' := (e₁.down.crossing_mem_intrinsicInterior ha'.1 ha'.2).1
      have hb'' := (e₂.down.crossing_mem_intrinsicInterior hb'.1 hb'.2).1
      dsimp
      nlinarith [mul_pos (sub_pos.mpr ha''.2) ht.1,
        mul_pos hb''.1 (sub_pos.mpr ht.2)]
  · intro a
    rw [WallComplement.crossings_subdivide hz ht]
    simp only [List.mem_append, List.mem_map, mem_orderedCrossings,
      mem_union, mem_image]

/-- Positive parameter rescaling on the first subsegment preserves every crossing sign. -/
theorem crossingLetter_subdivide_left (ν : C.walls → V →ₗ[ℝ] ℝ)
    (ht : 0 < t) (hz : z.val = AffineMap.lineMap x.val y.val t) (P : C.walls) :
    C.crossingLetter ν x z P = C.crossingLetter ν x y P := by
  rw [crossingLetter_def, crossingLetter_def, hz,
    AffineMap.lineMap_apply_module', add_sub_cancel_right, map_smul]
  simp only [smul_eq_mul, mul_pos_iff_of_pos_left ht]

/-- Positive parameter rescaling on the last subsegment preserves every crossing sign. -/
theorem crossingLetter_subdivide_right (ν : C.walls → V →ₗ[ℝ] ℝ)
    (ht : t < 1) (hz : z.val = AffineMap.lineMap x.val y.val t) (P : C.walls) :
    C.crossingLetter ν z y P = C.crossingLetter ν x y P := by
  have hv : y.val - z.val = (1 - t) • (y.val - x.val) := by
    rw [hz]
    exact AffineMap.right_vsub_lineMap x.val y.val t
  rw [crossingLetter_def, crossingLetter_def, hv, map_smul]
  simp only [smul_eq_mul, mul_pos_iff_of_pos_left (sub_pos.mpr ht)]

/-- Inserting an allowed vertex at any parameter in `[0, 1]` preserves the segment
word; the last subsegment's factors remain on the left. Endpoint insertions give
stationary segments with empty words. -/
theorem segmentCrossingWord_subdivide (ν : C.walls → V →ₗ[ℝ] ℝ)
    (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y)
    (ht : t ∈ Icc (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    C.segmentCrossingWord ν e =
      C.segmentCrossingWord ν e₂ * C.segmentCrossingWord ν e₁ := by
  rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · have hzx : z = x := WallComplement.ext (by
      simpa only [← ht0, AffineMap.lineMap_apply_zero] using hz)
    subst z
    simpa only [segmentCrossingWord_self, mul_one] using
      congrArg (C.segmentCrossingWord ν) (PLift.ext (Subsingleton.elim e.down e₂.down))
  rcases eq_or_lt_of_le ht.2 with ht1 | ht1
  · have hzy : z = y := WallComplement.ext (by
      simpa only [ht1, AffineMap.lineMap_apply_one] using hz)
    subst z
    simpa only [segmentCrossingWord_self, one_mul] using
      congrArg (C.segmentCrossingWord ν) (PLift.ext (Subsingleton.elim e.down e₁.down))
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  simp only [segmentCrossingWord_def, C.orderedCrossings_subdivide e e₁ e₂ ht' hz,
    List.reverse_append, List.map_append, List.prod_append, List.map_reverse,
    List.map_map, Function.comp_def,
    C.crossingLetter_subdivide_left ν ht0 hz,
    C.crossingLetter_subdivide_right ν ht1 hz]

end Mei.FinitePolyhedralComplex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}
  {x y : WallComplement (fun P : C.walls => (P : Set V))}

/-- Every finite subdivision by allowed interior vertices preserves the crossing word. -/
theorem IsSubdivision.crossingWord_eq {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    q.crossingWord ν = p.crossingWord ν := by
  induction hpq with
  | refl p => rfl
  | split e e₁ e₂ ht hz =>
    simpa only [crossingWord_comp, Quiver.Hom.toPath, crossingWord_cons,
      crossingWord_nil, mul_one] using
      (C.segmentCrossingWord_subdivide ν e e₁ e₂ ⟨ht.1.le, ht.2.le⟩ hz).symm
  | comp hp hq ihp ihq => simp only [crossingWord_comp, ihp, ihq]
  | trans hpq hqr ihpq ihqr => exact ihqr.trans ihpq

end Quiver.Path
