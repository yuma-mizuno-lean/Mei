/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Subdivision
public import Mei.Geometry.Convex.Polyhedron.Path.Product
public import Mei.Data.List.Filter

/-!
# Transport immediately before a crossing

Restricting an admissible segment at an allowed interior point retains precisely
the earlier simultaneous crossing events. Immediately before its `j`-th event
in reverse time order, its transport is the suffix product after that event.
This identifies algebraic partial products with geometric incoming segments,
including when several indexed walls are crossed at once.

The construction uses `orderedCrossingTimes_subdivide`, the signed event products
of `WallComplement`, and Mathlib's finite intersection of eventual properties.
No consistency, closedness, convexity or dimension assumption is required.
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] {W : ι → Set V} (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) →
    Commute (label i) (label j)) {x y z : WallComplement W}

/-- The product on an initial subsegment consists exactly of the events before
its allowed final parameter, in the original multiplication order. -/
theorem segmentPathProduct_subdivide_left_eq_filter (e : x ⟶ y) (e₁ : x ⟶ z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z.val = AffineMap.lineMap x.val y.val t) :
    segmentPathProduct ν label hcomm e₁ =
      (((orderedCrossingTimes e).reverse.filter (fun s => decide (s < t))).map
        (crossingEventProduct ν label hcomm e)).prod := by
  let e₂ : z ⟶ y := ⟨e.down.subdivide_right ⟨ht.1.le, ht.2⟩ hz⟩
  have htimes := congrArg List.reverse (orderedCrossingTimes_subdivide e e₁ e₂ ht hz)
  simp only [List.reverse_append, ← List.map_reverse] at htimes
  have hright : ((orderedCrossingTimes e₂).reverse.map
      (fun s => 1 - (1 - s) * (1 - t))).filter (fun s => decide (s < t)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro s hs
    obtain ⟨s, hs₀, rfl⟩ := List.mem_map.mp hs
    have hs := mem_Ioo_of_mem_orderedCrossingTimes e₂ (List.mem_reverse.mp hs₀)
    simp only [decide_eq_true_eq]
    nlinarith [mul_pos hs.1 (sub_pos.mpr ht.2)]
  have hleft : ((orderedCrossingTimes e₁).reverse.map (fun s => s * t)).filter
      (fun s => decide (s < t)) = (orderedCrossingTimes e₁).reverse.map (fun s => s * t) := by
    apply List.filter_eq_self.mpr
    intro s hs
    obtain ⟨s, hs₀, rfl⟩ := List.mem_map.mp hs
    have hs := mem_Ioo_of_mem_orderedCrossingTimes e₁ (List.mem_reverse.mp hs₀)
    simpa only [decide_eq_true_eq] using mul_lt_of_lt_one_left ht.1 hs.2
  rw [htimes, List.filter_append, hright, hleft, List.nil_append,
    List.map_map, Function.comp_def, segmentPathProduct_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro s hs
  have hs := mem_Ioo_of_mem_orderedCrossingTimes e₁ (List.mem_reverse.mp hs)
  have hevent := signedCrossingEvent_subdivide_left ν hz ⟨ht.1, ht.2.le⟩ hs.2.le
  rw [crossingEventProduct_eq_noncommProd ν label hcomm e₁ s
    (signedCrossingEvent_pairwise ν label hcomm e₁ s),
    crossingEventProduct_eq_noncommProd ν label hcomm e (s * t)
      (signedCrossingEvent_pairwise ν label hcomm e (s * t))]
  exact Finset.noncommProd_congr hevent.symm (fun _ _ => rfl) _

/-- Just before an event, the incoming subsegment realizes exactly the suffix
of the full event product preceding that crossing. This holds for every
sufficiently small positive parameter displacement. -/
theorem eventually_exists_segmentPathProduct_eq_drop (e : x ⟶ y)
    (j : Fin (orderedCrossingTimes e).reverse.length) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ (z : WallComplement W) (e₁ : x ⟶ z),
      z.val = AffineMap.lineMap x.val y.val ((orderedCrossingTimes e).reverse[j.val] - ε) ∧
      segmentPathProduct ν label hcomm e₁ =
        (((orderedCrossingTimes e).reverse.drop (j.val + 1)).map
          (crossingEventProduct ν label hcomm e)).prod := by
  classical
  let T := (orderedCrossingTimes e).reverse
  have ht := mem_Ioo_of_mem_orderedCrossingTimes e
    (List.mem_reverse.mp (List.getElem_mem j.isLt))
  have hgap : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ s ∈ T,
      (s < T[j.val] - ε ↔ s < T[j.val]) ∧ s ≠ T[j.val] - ε := by
    apply (List.finite_toSet T).eventually_all.mpr
    intro s _
    by_cases hs : s < T[j.val]
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hs)] with ε hε
      exact ⟨by constructor <;> intro _ <;> linarith [hε.2], by linarith [hε.2]⟩
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε : 0 < ε := hε
      exact ⟨by constructor <;> intro h <;> linarith, by linarith⟩
  filter_upwards [hgap, Ioo_mem_nhdsGT ht.1] with ε hgap hε
  have hu : T[j.val] - ε ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hε.2], by linarith [ht.2, hε.1]⟩
  let z : WallComplement W := ⟨AffineMap.lineMap x.val y.val (T[j.val] - ε), fun a ha => by
    have hm : T[j.val] - ε ∈ T := List.mem_reverse.mpr
      ((mem_orderedCrossingTimes e _).mpr ⟨a, (mem_crossings x y a _).mpr
        ⟨Ioo_subset_Icc_self hu, ha⟩⟩)
    exact (hgap _ hm).2 rfl⟩
  let e₁ : x ⟶ z := ⟨e.down.subdivide_left ⟨hu.1, hu.2.le⟩ rfl⟩
  refine ⟨z, e₁, rfl, ?_⟩
  rw [segmentPathProduct_subdivide_left_eq_filter ν label hcomm e e₁ hu rfl]
  have hf : T.filter (fun s => decide (s < T[j.val] - ε)) =
      T.filter (fun s => decide (s < T[j.val])) :=
    List.filter_congr fun s hs => by simp only [(hgap s hs).1]
  rw [hf, (pairwise_orderedCrossingTimes e).reverse.filter_lt_getElem_eq_drop j]

end Mei.Convex.WallComplement
