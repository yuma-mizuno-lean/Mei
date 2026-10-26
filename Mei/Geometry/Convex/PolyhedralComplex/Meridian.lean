/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Joint
public import Mei.Geometry.Convex.Polyhedron.Path.Meridian
public import Mathlib.Analysis.Convex.Combination

/-!
# Isolating triangular meridians of polyhedral joints

At every relative interior point of a codimension-two cell, construct an
arbitrarily small triangle in a complementary plane, with an admissible closed
polygonal boundary. Its filled triangle meets the codimension-at-least-two
skeleton exactly at the center, misses the relative boundary of the joint and
all other joints, and meets only walls containing that joint.

No transverse plane or admissible loop is assumed: the plane comes from
`FinitePolyhedralComplex.exists_isolating_ball_joint`, and its transversality
to every nearby wall follows from complementary directions and codimension.
The boundary is supplied by `Mei.Convex.exists_admissible_triangle`.
The vertex ordering is not prescribed by a conormal orientation; either ordering
can subsequently be used when evaluating signed meridian products.
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- There are arbitrarily small isolating triangular meridians about every
relative interior point of a joint. The filled triangle meets the whole
codimension-at-least-two skeleton exactly once, avoids every other joint and
the joint's relative boundary, and meets only walls containing the joint.
Its three boundary edges form an actual admissible loop. The ordering of the
vertices is free; no orientation of the normal quotient is specified here. -/
theorem exists_isolating_joint_meridian (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) {p : V} (hp : p ∈ intrinsicInterior ℝ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : Submodule ℝ V) (s : Affine.Triangle ℝ V)
      (x : WallComplement (fun P : C.walls => (P : Set V))) (γ : AdmissiblePLPath x x),
      IsCompl (affineSpan ℝ J).direction T ∧ Module.finrank ℝ T = 2 ∧
      s.centroid = p ∧
      γ.vertices.map WallComplement.val = [s.points 0, s.points 1, s.points 2, s.points 0] ∧
      convexHull ℝ (range s.points) ⊆
        Metric.ball p ε ∩ (AffineSubspace.mk' p T : Set V) ∧
      convexHull ℝ (range s.points) ∩ (C.codimensionAtLeast 2).support = {p} ∧
      Disjoint (convexHull ℝ (range s.points)) (intrinsicFrontier ℝ J) ∧
      (∀ Q ∈ C.joints, Q ≠ J → Disjoint (convexHull ℝ (range s.points)) Q) ∧
      ∀ P ∈ C.walls, (convexHull ℝ (range s.points) ∩ P).Nonempty → J ⊆ P := by
  classical
  let := h.finiteDimensional
  -- Shrink an isolating neighborhood to the requested size.
  obtain ⟨r, T, hr, hT, hdim, hskeleton, hfrontier, hother, hcells⟩ :=
    C.exists_isolating_ball_joint hJ hp
  let r' := min r ε
  have hr' : 0 < r' := lt_min hr hε
  have hball : Metric.ball p r' ⊆ Metric.ball p r := Metric.ball_subset_ball (min_le_left _ _)
  have hballε : Metric.ball p r' ⊆ Metric.ball p ε := Metric.ball_subset_ball (min_le_right _ _)
  -- Complementarity makes the slice transverse to every nearby wall.
  have hwall (P : C.walls) (hmeet : ((P : Set V) ∩ Metric.ball p r').Nonempty) :
      p ∈ affineSpan ℝ (P : Set V) ∧ ¬ T ≤ (affineSpan ℝ (P : Set V)).direction := by
    obtain ⟨y, hyP, hyball⟩ := hmeet
    have hJP := hcells P (C.mem_cells_of_mem_walls P.property) ⟨y, hball hyball, hyP⟩
    exact ⟨subset_affineSpan ℝ _ (hJP (intrinsicInterior_subset hp)),
      C.not_le_wall_direction_of_isCompl hJP P.property hT⟩
  have hsingular (y : V) (hyball : y ∈ Metric.ball p r')
      (hyT : y ∈ AffineSubspace.mk' p T)
      (hys : y ∈ singularSupport (fun P : C.walls => (P : Set V))) : y = p := by
    apply Set.mem_singleton_iff.mp
    rw [← hskeleton]
    exact ⟨⟨hball hyball, hyT⟩, C.singularSupport_walls_subset_support_codimensionAtLeast hys⟩
  obtain ⟨s, x, γ, hsp, hvertices, hfill⟩ := exists_admissible_triangle
    (fun P : C.walls => (P : Set V)) T (by omega) hr' hwall hsingular
  -- The filled triangle inherits all isolation properties of the ball and slice.
  have hfillball : convexHull ℝ (range s.points) ⊆ Metric.ball p r :=
    fun y hy => hball (hfill hy).1
  have hpfill : p ∈ convexHull ℝ (range s.points) := by
    rw [← hsp]
    exact affineCombination_mem_convexHull
      (fun j _ => by simp [Finset.centroidWeights_apply])
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ Finset.univ (by simp))
  refine ⟨T, s, x, γ, hT, hdim, hsp, hvertices,
    fun y hy => ⟨hballε (hfill hy).1, (hfill hy).2⟩, ?_,
    hfrontier.mono_left hfillball, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨hyfill, hys⟩
      rw [← hskeleton]
      exact ⟨⟨hfillball hyfill, (hfill hyfill).2⟩, hys⟩
    · rintro y (rfl : y = p)
      exact ⟨hpfill, mem_support.mpr
        ⟨J, C.cellsOfCodimension_subset_codimensionAtLeast_cells 2 hJ,
          intrinsicInterior_subset hp⟩⟩
  · exact fun Q hQ hne => (hother Q hQ hne).mono_left hfillball
  · rintro P hP ⟨y, hyfill, hyP⟩
    exact hcells P (C.mem_cells_of_mem_walls hP) ⟨y, hfillball hyfill, hyP⟩

end Mei.FinitePolyhedralComplex
