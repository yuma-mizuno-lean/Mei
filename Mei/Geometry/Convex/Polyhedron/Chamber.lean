/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Connected.Adjacency
public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Adjacency connects the chambers of an open convex region

For a finite family of codimension-one polyhedra, the actual connected
components of the wall complement in an open convex region form a connected
adjacency graph. Adjacency means that their ambient closures share a point
inside the region and outside the actual singular support. Balls are a special
case. Walls may be unbounded, have lineality, or be repeated in the family.

These results give finite adjacency walks between chambers even when the wall
complement is disconnected. Chambers use Mathlib's `ConnectedComponents` and
`connectedComponentIn`, and regularity uses Mei's actual singular support.
-/

public section

open Set AffineSubspace

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual chambers in the wall complement of a region, adjacent at regular
common closure points inside that region. -/
def chamberGraph (W : ι → Set V) (U : Set V) :
    SimpleGraph (ConnectedComponents ↥(U \ ⋃ i, W i)) :=
  componentAdjacencyGraph (U \ ⋃ i, W i) (U \ singularSupport W)

/-- At represented chambers, adjacency is witnessed by closures of the actual
ambient `connectedComponentIn` sets, at a nonsingular point of the region. -/
theorem chamberGraph_adj {W : ι → Set V} {U : Set V} {x y : ↥(U \ ⋃ i, W i)} :
    (chamberGraph W U).Adj (ConnectedComponents.mk x) (ConnectedComponents.mk y) ↔
      ConnectedComponents.mk x ≠ ConnectedComponents.mk y ∧
        ∃ p ∈ U, p ∉ singularSupport W ∧
          p ∈ closure (connectedComponentIn (U \ ⋃ i, W i) x.val) ∧
          p ∈ closure (connectedComponentIn (U \ ⋃ i, W i) y.val) := by
  simp only [chamberGraph, componentAdjacencyGraph_adj, mem_sdiff,
    ConnectedComponents.carrier_mk, and_assoc]

end Mei.Convex

namespace Convex

open Mei Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem lineMap_reachable [Finite ι] {W : ι → Set V} {U : Set V}
    (hconv : Convex ℝ U) (x y : ↥(U \ ⋃ i, W i))
    (htrans : ∀ i, y.val - x.val ∉ (affineSpan ℝ (W i)).direction)
    (hreg : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x.val y.val t ∉ singularSupport W) :
    (chamberGraph W U).Reachable (ConnectedComponents.mk x) (ConnectedComponents.mk y) := by
  classical
  let wx : WallComplement W :=
    ⟨x.val, fun i hi => x.property.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩
  let wy : WallComplement W :=
    ⟨y.val, fun i hi => y.property.2 (mem_iUnion.mpr ⟨i, hi⟩)⟩
  have e : WallComplement.AdmissibleSegment wx wy := ⟨fun i _ => htrans i, hreg⟩
  let T := (e.finite_crossings.image Prod.snd).toFinset
  have hT : ∀ t ∈ Icc (0 : ℝ) 1,
      AffineMap.lineMap x.val y.val t ∉ U \ ⋃ i, W i → t ∈ T := by
    intro t ht hbad
    have hex : ∃ i, AffineMap.lineMap x.val y.val t ∈ W i := by
      by_contra hno
      apply hbad
      refine ⟨hconv.lineMap_mem x.property.1 y.property.1 ht, ?_⟩
      simpa only [mem_iUnion, not_exists] using hno
    obtain ⟨i, hi⟩ := hex
    dsimp only [T]
    rw [(e.finite_crossings.image Prod.snd).mem_toFinset]
    exact ⟨(i, t), (WallComplement.mem_crossings wx wy i t).mpr ⟨ht, hi⟩, rfl⟩
  have hwalk := componentAdjacencyGraph_reachable_of_finite_exceptions
    (s := U \ ⋃ i, W i) (R := U \ singularSupport W)
    (f := fun t : ℝ => AffineMap.lineMap x.val y.val t) T
    AffineMap.lineMap_continuous.continuousOn (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [AffineMap.lineMap_apply_zero] using x.property)
    (by simpa only [AffineMap.lineMap_apply_one] using y.property)
    (fun t ht _ => ⟨hconv.lineMap_mem x.property.1 y.property.1 ht, hreg t ht⟩) hT
  simpa only [chamberGraph, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using hwalk

/-- Any two allowed points of an open convex region have chambers joined by
a finite adjacency walk, with each edge witnessed by a regular closure point
inside the region. No connectivity of the wall complement is assumed. -/
theorem chamberGraph_reachable {U : Set V} (hconv : Convex ℝ U)
    [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (hU : IsOpen U) (x y : ↥(U \ ⋃ i, W i)) :
    (chamberGraph W U).Reachable (ConnectedComponents.mk x) (ConnectedComponents.mk y) := by
  have hx : ∀ i, x.val ∉ W i := fun i hi => x.property.2 (mem_iUnion.mpr ⟨i, hi⟩)
  have hy : ∀ i, y.val ∉ W i := fun i hi => y.property.2 (mem_iUnion.mpr ⟨i, hi⟩)
  obtain ⟨p, hpU, hp, htrans, hreg⟩ := exists_mem_open_two_transverse_lineMaps
    W hpoly hdim hx hy hU ⟨x.val, x.property.1⟩
  let z : ↥(U \ ⋃ i, W i) := ⟨p, hpU, by simpa only [mem_iUnion, not_exists] using hp⟩
  have hleft := lineMap_reachable hconv x z (fun i => (htrans i).1)
    (fun t _ => (hreg t).1)
  have hright := lineMap_reachable hconv y z (fun i => (htrans i).2)
    (fun t _ => (hreg t).2)
  exact hleft.trans hright.symm

/-- The chamber graph of an open convex region is preconnected, including
the empty region and empty wall family. -/
theorem chamberGraph_preconnected {U : Set V} (hconv : Convex ℝ U)
    [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (hU : IsOpen U) : (chamberGraph W U).Preconnected := by
  intro c d
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  exact hconv.chamberGraph_reachable W hpoly hdim hU x y

/-- In a nonempty open convex region the actual chamber graph is connected.
Nonemptiness is not assumed separately for the complement or for any chamber. -/
theorem chamberGraph_connected {U : Set V} (hconv : Convex ℝ U)
    [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (hU : IsOpen U) (hne : U.Nonempty) :
    (chamberGraph W U).Connected := by
  obtain ⟨x, hxU, hx⟩ := AffineSubspace.exists_mem_open_genericLocus
    (fun i => affineSpan ℝ (W i))
    (fun i => (affineSpan ℝ (W i)).ne_top_of_finrank_direction_add_one_eq (hdim i)) hU hne
  have hxW : x ∉ ⋃ i, W i := by
    intro hxW
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxW
    exact hx i (subset_affineSpan ℝ (W i) hxi)
  let _ : Nonempty (ConnectedComponents ↥(U \ ⋃ i, W i)) :=
    ⟨ConnectedComponents.mk (⟨x, hxU, hxW⟩ : ↥(U \ ⋃ i, W i))⟩
  exact ⟨hconv.chamberGraph_preconnected W hpoly hdim hU⟩

end Convex

namespace Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The chambers in any positive-radius ball are connected under adjacency
through nonsingular closure points inside the ball. -/
theorem chamberGraph_ball_connected [FiniteDimensional ℝ V] [Finite ι]
    (W : ι → Set V) (hpoly : ∀ i, TauCeti.IsConvexPolyhedron (W i))
    (hdim : ∀ i, Module.finrank ℝ (affineSpan ℝ (W i)).direction + 1 = Module.finrank ℝ V)
    (c : V) {r : ℝ} (hr : 0 < r) : (chamberGraph W (Metric.ball c r)).Connected :=
  (convex_ball c r).chamberGraph_connected W hpoly hdim Metric.isOpen_ball
    (Metric.nonempty_ball.mpr hr)

end Mei.Convex
