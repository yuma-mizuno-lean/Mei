/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product
import Mei.Data.List.Filter

/-!
# Segment transport along sorted enumerations of crossed walls

Segment transport multiplies the simultaneous crossing events in reverse time order.
Equivalently, list the crossed walls once each, sorted by crossing time, and multiply
their signed labels in reverse order. Walls crossed at the same time may appear in any
order, since their labels commute.

This avoids grouping crossings into events when comparing transports of different
segments whose crossed walls are matched individually. The proof groups the sorted list
by crossing time using `List.flatten_map_filter_eq_of_pairwise` and evaluates each
group with `WallComplement.crossingEventProduct_eq_prod`.
-/

public section

noncomputable section

open Set

namespace Mei.Convex.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι] [Group G]
  {W : ι → Set V} (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) → Commute (label i) (label j))
  {x y : WallComplement W}

/-- Segment transport is the reverse-order product of the signed labels along any
enumeration of the crossed walls sorted by crossing time, with the first crossing
rightmost. Simultaneously crossed walls may be listed in any order. -/
theorem segmentPathProduct_eq_prod_of_pairwise (e : x ⟶ y) (l : List ι) (hl : l.Nodup)
    (hmem : ∀ j, j ∈ l ↔ ∃ t, (j, t) ∈ crossings x y)
    (hsort : l.Pairwise fun j k =>
      ∀ s t, (j, s) ∈ crossings x y → (k, t) ∈ crossings x y → s ≤ t) :
    segmentPathProduct ν label hcomm e =
      (l.reverse.map fun j =>
        label j ^ (if 0 < ν j (y.val - x.val) then -1 else 1 : ℤ)).prod := by
  classical
  set sgn : ι → ℤ := fun j => if 0 < ν j (y.val - x.val) then -1 else 1 with hsgn
  set g : ι → G := fun j => label j ^ sgn j with hg
  -- The unique crossing time of each listed wall.
  let τ : ι → ℝ := fun j => if h : ∃ t, (j, t) ∈ crossings x y then h.choose else 0
  have hτ (j : ι) (hj : j ∈ l) : (j, τ j) ∈ crossings x y := by
    have h := (hmem j).mp hj
    simpa only [τ, h, dite_true] using h.choose_spec
  have hcross (j : ι) (t : ℝ) : (j, t) ∈ crossings x y ↔ j ∈ l ∧ t = τ j := by
    constructor
    · intro ht
      have hj := (hmem j).mpr ⟨t, ht⟩
      exact ⟨hj, e.down.subsingleton_crossing j ((mem_crossings _ _ _ _).mp ht)
        ((mem_crossings _ _ _ _).mp (hτ j hj))⟩
    · rintro ⟨hj, rfl⟩
      exact hτ j hj
  -- Each simultaneous event is the product over the walls listed at its time.
  have hevent (t : ℝ) : crossingEventProduct ν label hcomm e t =
      (((l.filter fun j => τ j = t).reverse).map g).prod := by
    rw [crossingEventProduct_eq_prod ν label hcomm e t
      (((l.filter fun j => τ j = t).reverse).map fun j => (j, sgn j))]
    · simp only [List.map_map, Function.comp_def, hg]
    · exact (List.nodup_reverse.mpr (hl.filter _)).map fun j k h => (Prod.mk.inj h).1
    · rintro ⟨j, s⟩
      simp only [List.mem_map, List.mem_reverse, List.mem_filter, decide_eq_true_eq,
        Prod.mk.injEq, mem_signedCrossingEvent, hcross, hsgn]
      constructor
      · rintro ⟨k, ⟨hk, rfl⟩, rfl, rfl⟩
        exact ⟨⟨hk, rfl⟩, rfl⟩
      · rintro ⟨⟨hj, rfl⟩, rfl⟩
        exact ⟨j, ⟨hj, rfl⟩, rfl, rfl⟩
  -- The sorted list is the concatenation of its crossing-time groups.
  have hflat := List.flatten_map_filter_eq_of_pairwise (τ := τ)
    (pairwise_orderedCrossingTimes e)
    (hsort.imp_of_mem fun {j k} hj hk h => h _ _ (hτ j hj) (hτ k hk))
    (fun j hj => (mem_orderedCrossingTimes e _).mpr ⟨j, hτ j hj⟩)
  rw [segmentPathProduct_def]
  calc
    ((orderedCrossingTimes e).reverse.map (crossingEventProduct ν label hcomm e)).prod =
        ((orderedCrossingTimes e).reverse.map fun t =>
          (((l.filter fun j => τ j = t).reverse).map g).prod).prod :=
      congrArg List.prod (List.map_congr_left fun t _ => hevent t)
    _ = (l.reverse.map g).prod := by
      conv_rhs => rw [← hflat]
      simp only [List.reverse_flatten, List.map_reverse, List.map_map, List.map_flatten,
        List.prod_flatten, Function.comp_def]

end Mei.Convex.WallComplement
