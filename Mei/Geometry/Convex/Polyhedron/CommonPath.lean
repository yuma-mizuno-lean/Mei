/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.SimultaneousPath
public import Mei.Combinatorics.Quiver.Path

/-!
# Common admissible paths for wall families

`CommonWallComplement W` consists of the points allowed for every family `W j`.
An edge is a segment admissible for each family separately. Thus a quiver path
records one vertex list, with an admissible realization in every family. No
transversality to intersections between different families is imposed.

Projection to a family preserves vertices, concatenation and reversal. For
countably many finite codimension-one polyhedral families, any two common
allowed points are joined by such a path with two edges. This applies
`dense_setOf_forall_admissiblePairs`, based on Mathlib's Baire theorem, to the
existing `WallComplement.AdmissibleSegment` predicates. More generally, any
nonempty finite list of interior vertices admits arbitrarily close common
admissible paths with the same number of vertices and fixed endpoints.
-/

public section

open Set

namespace Mei.Convex

variable {V J : Type*} {I : J → Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A point allowed for every wall family. Edges are admissible in each family
separately, rather than in their union. -/
@[ext]
structure CommonWallComplement (W : ∀ j, I j → Set V) where
  /-- The common ambient point. -/
  val : V
  /-- The point lies on no wall in any family. -/
  notMem : ∀ j i, val ∉ W j i

namespace CommonWallComplement

variable {W : ∀ j, I j → Set V}

/-- View a common allowed point in one wall complement. -/
-- Endpoints must compute when restricting a projected path to a smaller family.
@[expose]
def projection (j : J) (x : CommonWallComplement W) : WallComplement (W j) :=
  ⟨x.val, x.notMem j⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp]
theorem projection_val (j : J) (x : CommonWallComplement W) :
    (projection j x).val = x.val := (rfl)

/-- A common edge is one geometric segment admissible in every family. -/
instance : Quiver (CommonWallComplement W) where
  Hom x y := PLift (∀ j, WallComplement.AdmissibleSegment (projection j x) (projection j y))

/-- Forget all admissibility conditions except those for the selected family. -/
-- Objects must compute to the projected endpoints in dependent path types.
@[expose]
def projectionPrefunctor (j : J) : CommonWallComplement W ⥤q WallComplement (W j) where
  obj := projection j
  map e := ⟨e.down j⟩

@[simp]
theorem projectionPrefunctor_obj (j : J) (x : CommonWallComplement W) :
    (projectionPrefunctor j).obj x = projection j x := (rfl)

/-- Reversal preserves simultaneous admissibility. -/
instance : Quiver.HasInvolutiveReverse (CommonWallComplement W) where
  reverse' e := ⟨fun j => (e.down j).symm⟩
  inv' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projections preserve reversal of edges, hence also reversal of paths. -/
instance (j : J) : (projectionPrefunctor (W := W) j).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

variable {x y : CommonWallComplement W}

/-- Every projected path has precisely the original ambient vertex list. -/
theorem vertices_projection (j : J) (p : Quiver.Path x y) :
    ((projectionPrefunctor j).mapPath p).vertices.map WallComplement.val =
      p.vertices.map CommonWallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    projectionPrefunctor_obj, projection_val]

/-- Any nonempty list of interior vertices can be approximated by a path
admissible for countably many finite polyhedral wall families simultaneously.
The endpoints stay fixed, and no extra vertices are inserted. -/
theorem exists_forall₂_dist_lt [FiniteDimensional ℝ V] [Countable J]
    [∀ j, Finite (I j)]
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    {l : List V} (hl : l ≠ []) {ε : ℝ} (hε : 0 < ε)
    (x y : CommonWallComplement W) :
    ∃ p : Quiver.Path x y, List.Forall₂ (fun a b => dist a b < ε)
      (x.val :: (l ++ [y.val])) (p.vertices.map CommonWallComplement.val) := by
  have hvertex (a b : CommonWallComplement W) (v : V) :
      ∃ z : CommonWallComplement W, dist v z.val < ε ∧ Nonempty (a ⟶ z) ∧
        Nonempty (z ⟶ b) := by
    obtain ⟨z, hz, hseg⟩ :=
      (dense_setOf_forall_admissiblePairs W hpoly hdim a.notMem b.notMem).inter_open_nonempty
        (Metric.ball v ε) Metric.isOpen_ball (Metric.nonempty_ball.mpr hε)
    have hzW : ∀ j i, z ∉ W j i := by
      intro j
      obtain ⟨_, hzj, _⟩ := mem_admissiblePairs.mp (hseg j).1
      exact hzj
    let c : CommonWallComplement W := ⟨z, hzW⟩
    exact ⟨c, Metric.mem_ball'.mp hz,
      ⟨⟨fun j => (mem_admissiblePairs_iff _ _).mp (hseg j).1⟩⟩,
      ⟨⟨fun j => (mem_admissiblePairs_iff _ _).mp (hseg j).2⟩⟩⟩
  -- Choose the first free vertex near its prescribed value, then approximate the tail.
  induction l generalizing x with
  | nil => exact absurd rfl hl
  | cons v l ih =>
    by_cases hl' : l = []
    · subst l
      obtain ⟨z, hz, ⟨hxz⟩, ⟨hzy⟩⟩ := hvertex x y v
      refine ⟨(Quiver.Path.nil.cons hxz).cons hzy, ?_⟩
      simpa using List.Forall₂.cons (by simpa using hε)
        (List.Forall₂.cons hz (List.Forall₂.cons (by simpa using hε) .nil))
    · obtain ⟨z, hz, ⟨hxz⟩, _⟩ := hvertex x x v
      obtain ⟨q, hq⟩ := ih hl' z
      refine ⟨hxz.toPath.comp q, ?_⟩
      obtain ⟨T, hT⟩ : ∃ T, q.vertices.map CommonWallComplement.val = z.val :: T := by
        rcases hv : q.vertices with _ | ⟨a, T⟩
        · exact absurd hv q.vertices_ne_nil
        · have ha := q.vertices_head?
          rw [hv, List.head?_cons, Option.some.injEq] at ha
          exact ⟨T.map CommonWallComplement.val, by rw [List.map_cons, ha]⟩
      rw [hT] at hq
      have hcomp : (hxz.toPath.comp q).vertices.map CommonWallComplement.val =
          x.val :: z.val :: T := by
        simp [Quiver.Path.vertices_comp, hT]
      rw [hcomp, List.cons_append]
      exact .cons (by simpa using hε) (.cons hz (List.forall₂_cons.mp hq).2)

/-- Countably many finite polyhedral wall families admit a common two-edge path
between any common allowed endpoints. -/
theorem exists_length_eq_two [FiniteDimensional ℝ V] [Countable J]
    [∀ j, Finite (I j)]
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    (x y : CommonWallComplement W) : ∃ p : Quiver.Path x y, p.length = 2 := by
  obtain ⟨p, hp⟩ := exists_forall₂_dist_lt hpoly hdim
    (List.cons_ne_nil (0 : V) []) zero_lt_one x y
  refine ⟨p, ?_⟩
  have hlen := hp.length_eq
  simpa using hlen.symm

end CommonWallComplement
end Mei.Convex
