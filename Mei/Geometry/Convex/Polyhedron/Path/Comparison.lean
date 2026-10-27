/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product

/-!
# Comparing transport from simultaneous crossing products

Two finite wall families have equal segment transport if their simultaneous
crossing products agree at every parameter in the unit interval. Their crossing
times may differ: insert the union of the two time lists, with identity factors
where no crossing occurs. A comparison on segments with the same ambient
endpoints then gives a comparison on polygonal paths with the same vertices.

These results turn local combined-label comparisons into equality of transport,
without matching individual indexed walls or imposing commutativity between
successive crossing events. They use
`WallComplement.segmentPathProduct_eq_prod_of_crossingTimes`. The polygonal
comparison, extracted from `Quiver.Path.wallPathProduct_eq_of_refines`, uses
`Quiver.Path.weight_eq_of_map_vertices_eq` with weights in the opposite group.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.Convex.WallComplement

variable {V ι κ G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Finite κ] [Group G] {W : ι → Set V} {W' : κ → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
  (ν' : κ → V →ₗ[ℝ] ℝ) (label' : κ → G)
  (hcomm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) → Commute (label' i) (label' j))

/-- Equality of simultaneous crossing products determines segment transport,
allowing distinct crossing-time sets and cancelling coincident labels. -/
theorem segmentPathProduct_eq_of_crossingEventProduct_eq
    {x y : WallComplement W} {x' y' : WallComplement W'} (e : x ⟶ y) (e' : x' ⟶ y')
    (hevent : ∀ t ∈ Icc (0 : ℝ) 1,
      crossingEventProduct ν label hcomm e t = crossingEventProduct ν' label' hcomm' e' t) :
    segmentPathProduct ν label hcomm e = segmentPathProduct ν' label' hcomm' e' := by
  classical
  let T := (orderedCrossingTimes e).toFinset ∪ (orderedCrossingTimes e').toFinset
  have hT : T.sort.Pairwise (· < ·) := (Finset.sortedLT_sort T).pairwise
  have hleft : ∀ t ∈ orderedCrossingTimes e, t ∈ T.sort := by
    intro t ht
    simpa only [T, Finset.mem_sort, Finset.mem_union, List.mem_toFinset] using Or.inl ht
  have hright : ∀ t ∈ orderedCrossingTimes e', t ∈ T.sort := by
    intro t ht
    simpa only [T, Finset.mem_sort, Finset.mem_union, List.mem_toFinset] using Or.inr ht
  rw [segmentPathProduct_eq_prod_of_crossingTimes ν label hcomm e T.sort hT hleft,
    segmentPathProduct_eq_prod_of_crossingTimes ν' label' hcomm' e' T.sort hT hright]
  congr 1
  apply List.map_congr_left
  intro t ht
  apply hevent t
  have ht : t ∈ orderedCrossingTimes e ∨ t ∈ orderedCrossingTimes e' := by
    simpa only [T, List.mem_reverse, Finset.mem_sort, Finset.mem_union, List.mem_toFinset] using ht
  exact ht.elim (fun ht => Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e ht))
    (fun ht => Ioo_subset_Icc_self (mem_Ioo_of_mem_orderedCrossingTimes e' ht))

end Mei.Convex.WallComplement

namespace Quiver.Path

variable {V ι κ G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Finite κ] [Group G] {W : ι → Set V} {W' : κ → Set V}

/-- A transport comparison on common segments extends to common polygonal
vertex lists, even when the two families have different indexed walls. -/
theorem wallPathProduct_eq_of_segmentPathProduct_eq
    (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
    (ν' : κ → V →ₗ[ℝ] ℝ) (label' : κ → G)
    (hcomm' : ∀ i j, affineSpan ℝ (W' i) = affineSpan ℝ (W' j) → Commute (label' i) (label' j))
    (hsegment : ∀ {x y : WallComplement W} {x' y' : WallComplement W'}
      (e : x ⟶ y) (e' : x' ⟶ y'), x.val = x'.val → y.val = y'.val →
        segmentPathProduct ν label hcomm e = segmentPathProduct ν' label' hcomm' e')
    {x y : WallComplement W} {x' y' : WallComplement W'}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath x' y')
    (hpq : p.vertices.map WallComplement.val = q.vertices.map WallComplement.val) :
    p.wallPathProduct ν label hcomm = q.wallPathProduct ν' label' hcomm' := by
  rw [wallPathProduct_eq_unop_weight, wallPathProduct_eq_unop_weight]
  apply congrArg MulOpposite.unop
  exact p.weight_eq_of_map_vertices_eq q WallComplement.val WallComplement.val _ _
    (fun e e' hx hy => congrArg MulOpposite.op (hsegment e e' hx hy)) hpq

end Quiver.Path
