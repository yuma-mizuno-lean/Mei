/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Triangle
public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Admissible triangular boundaries around isolated singularities

Suppose a two-dimensional affine slice meets singular support in a ball only
at its center. If the slice is transverse to the affine spans of the walls
meeting the ball, and these spans contain the center, there is a nondegenerate
triangle centered there with admissible polygonal boundary. Its entire filled
triangle remains in the ball and slice. Walls missing the ball require no
transversality assumption.

The geometric input is local isolation; the construction supplies actual
vertices and admissible edges, rather than assuming a meridian exists. It uses
`Mei.exists_small_transverse_triangle_in_slice`, Mathlib's simplex centroid and its
avoidance of proper faces, and Mei's quiver of admissible segments.
-/

public section

open Set

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Countable ι]
  (W : ι → Set V) (T : Submodule ℝ V) [FiniteDimensional ℝ T]
  {p : V} {r : ℝ}

/-- A small triangle centered at an isolated point of singular support has an
actual admissible three-edge boundary. Its filled triangle lies in the given
ball and affine slice. Only walls meeting the ball must be transverse to the
slice and have affine span through the center.

The slice may have any dimension at least two; a transverse plane is the usual
application. No polyhedral or rational presentation is required by this local
construction. -/
theorem exists_admissible_triangle (hdim : 2 ≤ Module.finrank ℝ T) (hr : 0 < r)
    (hwall : ∀ j, (W j ∩ Metric.ball p r).Nonempty →
      p ∈ affineSpan ℝ (W j) ∧ ¬ T ≤ (affineSpan ℝ (W j)).direction)
    (hsingular : ∀ x ∈ Metric.ball p r, x ∈ AffineSubspace.mk' p T →
      x ∈ singularSupport W → x = p) :
    ∃ (s : Affine.Triangle ℝ V) (x : WallComplement W) (γ : AdmissiblePLPath x x),
      s.centroid = p ∧
      γ.vertices.map WallComplement.val = [s.points 0, s.points 1, s.points 2, s.points 0] ∧
      convexHull ℝ (Set.range s.points) ⊆
        Metric.ball p r ∩ (AffineSubspace.mk' p T : Set V) := by
  obtain ⟨s, hsp, hmem, hedge, hvertex⟩ :=
    Mei.exists_small_transverse_triangle_in_slice W T hdim hr hwall
  let a : Fin 3 → WallComplement W := fun j => ⟨s.points j, hvertex j⟩
  have hadm (j k : Fin 3) (hjk : j ≠ k) : (a j).AdmissibleSegment (a k) := by
    refine ⟨?_, ?_⟩
    · intro b hb
      obtain ⟨t, ht, htb⟩ := hb
      have hm := (convex_ball p r).lineMap_mem (hmem j).1 (hmem k).1 ht
      exact hedge j k hjk b ⟨_, htb, hm⟩
    · intro t ht he
      have hb := (convex_ball p r).lineMap_mem (hmem j).1 (hmem k).1 ht
      have hT := AffineMap.lineMap_mem t (hmem j).2 (hmem k).2
      have heq := hsingular _ hb hT he
      exact s.centroid_ne_lineMap j k t (hsp.trans heq.symm)
  let e01 : a 0 ⟶ a 1 := ⟨hadm 0 1 (by decide)⟩
  let e12 : a 1 ⟶ a 2 := ⟨hadm 1 2 (by decide)⟩
  let e20 : a 2 ⟶ a 0 := ⟨hadm 2 0 (by decide)⟩
  let γ : AdmissiblePLPath (a 0) (a 0) :=
    ((Quiver.Path.nil.cons e01).cons e12).cons e20
  refine ⟨s, a 0, γ, hsp, ?_, ?_⟩
  · rfl
  · exact convexHull_min (Set.range_subset_iff.mpr hmem)
      ((convex_ball p r).inter (AffineSubspace.mk' p T).convex)

end Mei.Convex
