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
# Isolating triangular loops at polyhedral joints

At every relative interior point of a joint of a finite polyhedral complex,
construct an arbitrarily small nondegenerate triangle with an admissible
three-edge boundary. Its plane complements the joint direction. The filled
triangle meets the codimension-at-least-two skeleton exactly at its centroid,
misses the relative boundary of the joint and every other joint, and meets only
cells containing the chosen joint. Thus its wall crossings can be used to
compute local joint products without contributions from unrelated walls.

The construction combines `FinitePolyhedralComplex.exists_isolating_ball_joint`
with `Mei.Convex.exists_admissible_triangle`. The missing transversality follows
from the common-face incidence in the isolating ball: every wall meeting that
ball contains the joint, so a complement to the joint direction cannot lie in
the direction of that wall. No orientation of the normal plane is chosen here.
Cells may be unbounded and have lineality.
-/

public section

open Set Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A joint admits arbitrarily small admissible triangular loops in a
complementary plane. The whole filled triangle isolates the joint, including
its relative boundary and all other joints. Every cell meeting the filled
triangle contains the joint. The vertex formula specifies the actual loop,
and the triangle's centroid is the chosen relative interior point. -/
theorem exists_isolating_joint_triangle (C : FinitePolyhedralComplex h) {J : Set V}
    (hJ : J ∈ C.joints) {p : V} (hp : p ∈ intrinsicInterior ℝ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Affine.Triangle ℝ V)
      (x : WallComplement (fun W : C.walls => (W : Set V)))
      (γ : AdmissiblePLPath x x),
      s.centroid = p ∧
      γ.vertices.map WallComplement.val = [s.points 0, s.points 1, s.points 2, s.points 0] ∧
      IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ (range s.points)) ∧
      convexHull ℝ (range s.points) ⊆ Metric.ball p ε ∧
      convexHull ℝ (range s.points) ∩ (C.codimensionAtLeast 2).support = {p} ∧
      Disjoint (convexHull ℝ (range s.points)) (intrinsicFrontier ℝ J) ∧
      (∀ Q ∈ C.joints, Q ≠ J → Disjoint (convexHull ℝ (range s.points)) Q) ∧
      ∀ Q ∈ C.cells, (convexHull ℝ (range s.points) ∩ Q).Nonempty → J ⊆ Q := by
  classical
  let := h.finiteDimensional
  obtain ⟨r, T, hr, hT, hdimT, hskeleton, hfrontier, hother, hcells⟩ :=
    C.exists_isolating_ball_joint hJ hp
  have hball : Metric.ball p (min r ε) ⊆ Metric.ball p r :=
    Metric.ball_subset_ball (min_le_left _ _)
  -- Incidence in the isolating ball forces transversality to its incident walls.
  have hwall (W : C.walls) (hW : ((W : Set V) ∩ Metric.ball p (min r ε)).Nonempty) :
      p ∈ affineSpan ℝ (W : Set V) ∧ ¬ T ≤ (affineSpan ℝ (W : Set V)).direction := by
    have hJW : J ⊆ (W : Set V) := hcells W (C.mem_cells_of_mem_walls W.property)
      (by obtain ⟨y, hyW, hyball⟩ := hW; exact ⟨y, hball hyball, hyW⟩)
    refine ⟨subset_affineSpan ℝ _ (hJW (intrinsicInterior_subset hp)), ?_⟩
    intro hle
    have htop : (⊤ : Submodule ℝ V) ≤ (affineSpan ℝ (W : Set V)).direction := by
      rw [← hT.sup_eq_top]
      exact sup_le (AffineSubspace.direction_le (affineSpan_mono ℝ hJW)) hle
    have heq := top_unique htop
    have hdim := C.finrank_direction_add_one_of_mem_walls W.property
    rw [heq, finrank_top] at hdim
    omega
  have hsingular : ∀ y ∈ Metric.ball p (min r ε), y ∈ AffineSubspace.mk' p T →
      y ∈ singularSupport (fun W : C.walls => (W : Set V)) → y = p := by
    intro y hyball hyT hy
    exact Set.mem_singleton_iff.mp (hskeleton ▸
      ⟨⟨hball hyball, hyT⟩, C.singularSupport_walls_subset_support_codimensionAtLeast hy⟩)
  obtain ⟨s, x, γ, hsp, hvertices, hfill⟩ := exists_admissible_triangle
    (fun W : C.walls => (W : Set V)) T (by omega) (lt_min hr hε) hwall hsingular
  -- Nondegeneracy makes the triangle span the whole chosen normal plane.
  have hfillball : convexHull ℝ (range s.points) ⊆ Metric.ball p r :=
    fun y hy => hball (hfill hy).1
  have hplane : vectorSpan ℝ (range s.points) = T := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [← direction_affineSpan, ← AffineSubspace.direction_mk' p T]
      apply AffineSubspace.direction_le
      exact affineSpan_le.mpr fun y hy => (hfill (subset_convexHull ℝ _ hy)).2
    · rw [s.independent.finrank_vectorSpan (Fintype.card_fin 3), hdimT]
  have hcenter : p ∈ convexHull ℝ (range s.points) := by
    rw [← hsp, s.centroid_eq_affineCombination]
    exact affineCombination_mem_convexHull (by simp [Finset.centroidWeights_apply])
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ Finset.univ_nonempty)
  -- Pass all isolation conditions from the ball to the actual filled triangle.
  refine ⟨s, x, γ, hsp, hvertices, hplane ▸ hT, ?_, ?_,
    hfrontier.mono_left hfillball, ?_, ?_⟩
  · exact fun y hy => Metric.ball_subset_ball (min_le_right _ _) (hfill hy).1
  · apply Set.Subset.antisymm
    · rintro y ⟨hy, hys⟩
      exact hskeleton ▸ ⟨⟨hfillball hy, (hfill hy).2⟩, hys⟩
    · intro y hy
      have heq := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨hcenter, mem_support.mpr ⟨J,
        C.cellsOfCodimension_subset_codimensionAtLeast_cells 2 hJ,
        intrinsicInterior_subset hp⟩⟩
  · exact fun Q hQ hne => (hother Q hQ hne).mono_left hfillball
  · rintro Q hQ ⟨y, hy, hyQ⟩
    exact hcells Q hQ ⟨y, hfillball hy, hyQ⟩

end Mei.FinitePolyhedralComplex
