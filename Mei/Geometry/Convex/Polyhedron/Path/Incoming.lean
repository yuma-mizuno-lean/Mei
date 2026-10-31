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
# Incoming pieces of a segment at its crossing events

Immediately before each crossing of an admissible segment, its initial piece
has precisely the earlier simultaneous events. Its transport is the suffix
product preceding that event in multiplication order. The endpoint of this
piece can approach the crossing arbitrarily closely from the incoming side.

The formulas retain all coincident wall indices and need no commutation between
different events. They use the crossing rescaling formulas of
`WallComplement.AdmissibleSegment.subdivide_left` and the existing ordered
crossing-time and simultaneous-product APIs.
-/

public noncomputable section

open Set Filter Topology

namespace Mei.Convex.WallComplement

variable {V ι G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y z : WallComplement W}

/-- Rescaling an initial piece gives exactly the original crossing times before
its allowed endpoint. -/
theorem orderedCrossingTimes_subdivide_left (e : x ⟶ y) (a : x ⟶ z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z.val = AffineMap.lineMap x.val y.val t) :
    (orderedCrossingTimes a).map (fun s => s * t) =
      (orderedCrossingTimes e).filter (fun s => decide (s < t)) := by
  apply (List.pairwise_map.mpr ((pairwise_orderedCrossingTimes a).imp
    (fun h => mul_lt_mul_of_pos_right h ht.1))).eq_of_mem_iff
      ((pairwise_orderedCrossingTimes e).filter _)
  intro s
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes a u).mp hu
    have hcross := ((mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩ i u).mp hi).1
    exact ⟨(mem_orderedCrossingTimes e _).mpr ⟨i, hcross⟩,
      mul_lt_of_lt_one_left ht.1 (mem_Ioo_of_mem_orderedCrossingTimes a hu).2⟩
  · rintro ⟨hs, hst⟩
    obtain ⟨i, hi⟩ := (mem_orderedCrossingTimes e s).mp hs
    refine ⟨s / t, (mem_orderedCrossingTimes a _).mpr ⟨i, ?_⟩,
      div_mul_cancel₀ _ ht.1.ne'⟩
    rw [mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩]
    exact ⟨by simpa only [div_mul_cancel₀ _ ht.1.ne'] using hi,
      (div_le_one ht.1).mpr hst.le⟩

variable [Group G] (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (comm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) →
    Commute (label i) (label j))

/-- The transport of an initial piece is the reverse-time product of the
original events preceding its endpoint. -/
theorem segmentPathProduct_subdivide_left (e : x ⟶ y) (a : x ⟶ z)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z.val = AffineMap.lineMap x.val y.val t) :
    segmentPathProduct ν label comm a =
      (((orderedCrossingTimes e).filter (fun s => decide (s < t))).reverse.map
        (crossingEventProduct ν label comm e)).prod := by
  have hevent (s : ℝ) (hs : s ∈ orderedCrossingTimes a) :
      signedCrossingEvent ν x z s = signedCrossingEvent ν x y (s * t) := by
    ext ⟨i, r⟩
    have hv : z.val - x.val = t • (y.val - x.val) := by
      rw [hz, AffineMap.lineMap_apply_module', add_sub_cancel_right]
    simp only [mem_signedCrossingEvent, mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩,
      (mem_Ioo_of_mem_orderedCrossingTimes a hs).2.le, and_true,
      hv, map_smul, smul_eq_mul, mul_pos_iff_of_pos_left ht.1]
  rw [segmentPathProduct_def, ← orderedCrossingTimes_subdivide_left e a ht hz,
    ← List.map_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro s hs
  simp only [Function.comp_apply]
  rw [crossingEventProduct_eq_noncommProd ν label comm a s
      (signedCrossingEvent_pairwise ν label comm a s),
    crossingEventProduct_eq_noncommProd ν label comm e (s * t)
      (signedCrossingEvent_pairwise ν label comm e (s * t))]
  exact Finset.noncommProd_congr (hevent s (List.mem_reverse.mp hs)) (fun _ _ => rfl) _

/-- Immediately before a selected crossing, the initial segment computes the
suffix of the full event-label list preceding that crossing in multiplication
order. Its endpoint can be arbitrarily close to the crossing from below. -/
theorem eventually_exists_segmentPathProduct_eq_drop (e : x ⟶ y)
    (j : Fin (orderedCrossingTimes e).length) :
    let T := (orderedCrossingTimes e).reverse
    let g := T.map (crossingEventProduct ν label comm e)
    ∀ᶠ t : ℝ in 𝓝[<] T[j.val]'(by simpa only [T, List.length_reverse] using j.isLt),
      t ∈ Ioo (0 : ℝ) 1 ∧
      ∃ (z : WallComplement W) (a : x ⟶ z),
        z.val = AffineMap.lineMap x.val y.val t ∧
        segmentPathProduct ν label comm a = (g.drop (j.val + 1)).prod := by
  dsimp only
  let T := (orderedCrossingTimes e).reverse
  have hj : j.val < T.length := by simpa only [T, List.length_reverse] using j.isLt
  have hτ : T[j.val] ∈ orderedCrossingTimes e :=
    List.mem_reverse.mp (List.getElem_mem hj)
  have hτI := mem_Ioo_of_mem_orderedCrossingTimes e hτ
  have hgap : ∀ᶠ t : ℝ in 𝓝[<] T[j.val],
      ∀ s ∈ orderedCrossingTimes e, s < T[j.val] → s < t := by
    apply ((orderedCrossingTimes e).finite_toSet.eventually_all).mpr
    intro s hs
    by_cases hst : s < T[j.val]
    · exact ((eventually_gt_nhds hst).filter_mono nhdsWithin_le_nhds).mono
        (fun _ ht _ => ht)
    · exact Filter.Eventually.of_forall (fun _ h => (hst h).elim)
  filter_upwards [hgap, (eventually_gt_nhds hτI.1).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[<] T[j.val], t < T[j.val])] with t hgap ht₀ htτ
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ht₀, lt_trans htτ hτI.2⟩
  have heq (s : ℝ) (hs : s ∈ orderedCrossingTimes e) :
      s < t ↔ s < T[j.val] := ⟨fun h => h.trans htτ, hgap s hs⟩
  have htmiss : ∀ i, AffineMap.lineMap x.val y.val t ∉ W i := by
    intro i hi
    have hm := (mem_orderedCrossingTimes e t).mpr
      ⟨i, (mem_crossings x y i t).mpr ⟨⟨ht.1.le, ht.2.le⟩, hi⟩⟩
    exact (lt_irrefl t) ((heq t hm).mpr htτ)
  let z : WallComplement W := ⟨AffineMap.lineMap x.val y.val t, htmiss⟩
  let a : x ⟶ z := ⟨e.down.subdivide_left ⟨ht.1, ht.2.le⟩ rfl⟩
  refine ⟨ht, z, a, rfl, ?_⟩
  rw [segmentPathProduct_subdivide_left ν label comm e a ht rfl]
  have hf : (orderedCrossingTimes e).filter (fun s => decide (s < t)) =
      (orderedCrossingTimes e).filter (fun s => decide (s < T[j.val])) :=
    List.filter_congr fun s hs => by simp only [heq s hs]
  rw [hf, ← List.filter_reverse]
  have hp : T.Pairwise (· > ·) := (pairwise_orderedCrossingTimes e).reverse
  rw [hp.filter_lt_getElem_eq_drop j.val hj, ← List.map_drop]

end Mei.Convex.WallComplement
