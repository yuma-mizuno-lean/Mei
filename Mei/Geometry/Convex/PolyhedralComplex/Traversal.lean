/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Chamber
public import Mei.Geometry.Convex.PolyhedralComplex.Incidence
public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Chambers along a single wall crossing

An admissible segment crossing exactly one wall runs through the interiors of
the two full cells incident to that wall. Its entire portion before the crossing
lies in the source cell's interior, and its entire portion after the crossing
lies in the target cell's interior. The two cells meet exactly in the crossed
wall. Only a neighborhood of the crossing must be covered by the complex.

This extends the short-ray incidence theorem
`FinitePolyhedralComplex.exists_transverse_wall_chambers` to the actual endpoints
of a segment. The extension uses
`FinitePolyhedralComplex.subset_interior_of_isPreconnected_of_disjoint_walls`:
a connected portion avoiding all walls cannot leave a full cell's interior.
These statements allow geometric path crossings to be assigned to the incident
chambers carrying transport potentials, without replacing the given segment by
a short one. Real offsets, unbounded cells and lineality are allowed.
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  (C : FinitePolyhedralComplex h)
  {x y : WallComplement (fun W : C.walls => (W : Set V))}

/-- A segment crossing no wall remains in the interior of its initial full
cell, including both endpoints. The segment need not be admissible. -/
theorem lineMap_mem_interior_of_crossings_eq_empty {P : Set V}
    (hP : P ∈ C.cellsOfCodimension 0) (hx : x.val ∈ interior P)
    (he : WallComplement.crossings x y = ∅) :
    ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∈ interior P := by
  have hsub := C.subset_interior_of_isPreconnected_of_disjoint_walls hP
    ((isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) 1)).image
      (AffineMap.lineMap x.val y.val : ℝ → V)
      AffineMap.lineMap_continuous.continuousOn)
    ⟨x.val, ⟨0, by simp, by simp⟩, hx⟩
    (fun W hW => Set.disjoint_left.mpr fun z hz hzW => by
      obtain ⟨t, ht, rfl⟩ := hz
      have hm : (⟨W, hW⟩, t) ∈ WallComplement.crossings x y :=
        (WallComplement.mem_crossings x y ⟨W, hW⟩ t).mpr ⟨ht, hzW⟩
      simp only [he, Set.mem_empty_iff_false] at hm)
  exact fun t ht => hsub (mem_image_of_mem _ ht)

/-- The two full chambers traversed by an actual single-crossing segment.
Every point strictly before or after the crossing belongs to the corresponding
ordinary interior, including the segment's initial and final endpoints.
The complex need only cover a neighborhood of the crossing point. -/
theorem exists_chambers_of_crossings_singleton (e : x ⟶ y) (W : C.walls) (t : ℝ)
    (he : WallComplement.crossings x y = {(W, t)})
    (hcover : AffineMap.lineMap x.val y.val t ∈ interior C.support) :
    ∃ P ∈ C.cellsOfCodimension 0, ∃ Q ∈ C.cellsOfCodimension 0,
      P ≠ Q ∧ P ∩ Q = (W : Set V) ∧
      (∀ u ∈ Ico (0 : ℝ) t, AffineMap.lineMap x.val y.val u ∈ interior P) ∧
      (∀ u ∈ Ioc t 1, AffineMap.lineMap x.val y.val u ∈ interior Q) := by
  have htW : (W, t) ∈ WallComplement.crossings x y := by rw [he]; exact mem_singleton _
  obtain ⟨ht, hW⟩ := (WallComplement.mem_crossings x y W t).mp htW
  obtain ⟨⟨ht0, ht1⟩, hri⟩ := e.down.crossing_mem_intrinsicInterior ht hW
  obtain ⟨P, hP, Q, hQ, hne, hinter, ε, hε, hshort⟩ :=
    C.exists_transverse_wall_chambers W.property hri hcover
      (e.down.transverse W ⟨t, ht, hW⟩)
  have hPi := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    (C.affineSpan_eq_top_of_mem_cellsOfCodimension_zero hP)
  have hQi := Mei.intrinsicInterior_eq_interior_of_affineSpan_eq_top
    (C.affineSpan_eq_top_of_mem_cellsOfCodimension_zero hQ)
  -- Seed each half of the segment with a short ray in its incident chamber.
  obtain ⟨a, ha, hsmall⟩ := exists_between (lt_min hε (lt_min ht0 (sub_pos.mpr ht1)))
  obtain ⟨haε, hat, ha1⟩ : a < ε ∧ a < t ∧ a < 1 - t := by
    simpa only [lt_min_iff] using hsmall
  have hminus : AffineMap.lineMap x.val y.val (t - a) ∈ interior P := by
    have hm := (hshort a ⟨ha, haε⟩).1
    rw [hPi] at hm
    simpa only [AffineMap.lineMap_apply_module', sub_smul,
      sub_eq_add_neg, add_smul, neg_smul, add_assoc, add_left_comm, add_comm] using hm
  have hplus : AffineMap.lineMap x.val y.val (t + a) ∈ interior Q := by
    have hm := (hshort a ⟨ha, haε⟩).2
    rw [hQi] at hm
    simpa only [AffineMap.lineMap_apply_module', add_smul, add_assoc,
      add_left_comm, add_comm] using hm
  -- The two parameter intervals avoid every wall, so connectedness propagates
  -- the seeds all the way to the original endpoints.
  have havoid {s : Set ℝ} (hs : s ⊆ Icc (0 : ℝ) 1) (hts : t ∉ s) :
      ∀ R ∈ C.walls, Disjoint (AffineMap.lineMap x.val y.val '' s) R := by
    intro R hR
    apply Set.disjoint_left.mpr
    rintro z ⟨u, hu, rfl⟩ hz
    have hm : (⟨R, hR⟩, u) ∈ WallComplement.crossings x y :=
      (WallComplement.mem_crossings x y ⟨R, hR⟩ u).mpr ⟨hs hu, hz⟩
    rw [he, Set.mem_singleton_iff, Prod.mk.injEq] at hm
    exact hts (hm.2 ▸ hu)
  refine ⟨P, hP, Q, hQ, hne, hinter, ?_, ?_⟩
  · have hsub := C.subset_interior_of_isPreconnected_of_disjoint_walls hP
      ((isPreconnected_Ico : IsPreconnected (Ico (0 : ℝ) t)).image
        (AffineMap.lineMap x.val y.val : ℝ → V)
        AffineMap.lineMap_continuous.continuousOn)
      ⟨_, ⟨t - a, ⟨by linarith, by linarith⟩, rfl⟩, hminus⟩
      (havoid (fun u hu => ⟨hu.1, hu.2.le.trans ht.2⟩) (by simp))
    exact fun u hu => hsub (mem_image_of_mem _ hu)
  · have hsub := C.subset_interior_of_isPreconnected_of_disjoint_walls hQ
      ((isPreconnected_Ioc : IsPreconnected (Ioc t (1 : ℝ))).image
        (AffineMap.lineMap x.val y.val : ℝ → V)
        AffineMap.lineMap_continuous.continuousOn)
      ⟨_, ⟨t + a, ⟨by linarith, by linarith⟩, rfl⟩, hplus⟩
      (havoid (fun u hu => ⟨ht.1.trans hu.1.le, hu.2⟩) (by simp))
    exact fun u hu => hsub (mem_image_of_mem _ hu)

end Mei.FinitePolyhedralComplex
