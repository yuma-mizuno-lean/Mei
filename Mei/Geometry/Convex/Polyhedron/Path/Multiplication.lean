/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.LocalCrossing

/-!
# Replacement of wall labels inside simultaneous products

Multiplying two label families pointwise multiplies their simultaneous crossing
products, provided all factors within each event commute. If two families give
the same transport on every segment, multiplying both by a third such family
preserves that agreement. Commutation between distinct crossing events is unnecessary.
This permits replacement of part of a wall presentation while retaining other walls.

The replacement uses `WallComplement.crossingEventProduct_mul` and isolates
each event with `WallComplement.exists_segmentCrossingEvents_eq_singleton`.
-/

public section

noncomputable section

open Set Mei.Convex WallComplement

namespace Mei.Convex.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Group G] {W : ι → Set V}

/-- Agreement on every segment survives pointwise multiplication by the same
locally commuting family. Closed supports and finite dimension allow isolation
of the events; no global commutativity or consistency is assumed. -/
theorem segmentPathProduct_mul_congr [FiniteDimensional ℝ V]
    (hclosed : ∀ j, IsClosed (W j)) (ν : ι → V →ₗ[ℝ] ℝ) (a b c : ι → G)
    (ha : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (a j) (a k))
    (hb : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (b j) (b k))
    (hc : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (c j) (c k))
    (hac : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (a j) (c k))
    (hbc : ∀ j k, affineSpan ℝ (W j) = affineSpan ℝ (W k) → Commute (b j) (c k))
    (hab : ∀ {u v : WallComplement W} (e : u ⟶ v),
      segmentPathProduct ν a ha e = segmentPathProduct ν b hb e)
    {x y : WallComplement W} (e : x ⟶ y) :
    segmentPathProduct ν (fun j => a j * c j)
        (fun j k hjk => ((ha j k hjk).mul_right (hac j k hjk)).mul_left
          (((hac k j hjk.symm).symm).mul_right (hc j k hjk))) e =
      segmentPathProduct ν (fun j => b j * c j)
        (fun j k hjk => ((hb j k hjk).mul_right (hbc j k hjk)).mul_left
          (((hbc k j hjk.symm).symm).mul_right (hc j k hjk))) e := by
  have hevent (t : ℝ) (ht : t ∈ orderedCrossingTimes e) :
      crossingEventProduct ν a ha e t = crossingEventProduct ν b hb e t := by
    obtain ⟨u, v, q, hq⟩ := exists_segmentCrossingEvents_eq_singleton hclosed ν e ht
    have hp (label : ι → G) (comm) :
        segmentPathProduct ν label comm q = crossingEventProduct ν label comm e t := by
      rw [← Quiver.Path.wallPathProduct_toPath ν label comm,
        Quiver.Path.wallPathProduct_eq_prod_signedCrossingEvents, Quiver.Hom.toPath,
        Quiver.Path.signedCrossingEvents_cons, Quiver.Path.signedCrossingEvents_nil,
        List.nil_append, hq]
      simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton]
      exact (crossingEventProduct_eq_prod ν label comm e t _
        (Finset.nodup_toList _) (fun _ => Finset.mem_toList)).symm
    exact (hp a ha).symm.trans ((hab q).trans (hp b hb))
  simp only [segmentPathProduct_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [crossingEventProduct_mul ν a c ha hc hac,
    crossingEventProduct_mul ν b c hb hc hbc, hevent t (List.mem_reverse.mp ht)]

end Mei.Convex.WallComplement
