/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.SegmentSubdivision
public import Mei.Geometry.Convex.Polyhedron.CrossingEvents

/-!
# Subdivision at simultaneous crossing events

An admissible path through a finite indexed wall family can be subdivided, without
moving its vertices, so that each segment has at most one crossing time. Several
coincident walls may occur at that time: the subdivision retains their complete
signed event, and preserves the ordered event list of the whole path. Thus local
formulas for combined wall germs can be applied successively along a path, even
when the wall presentation has repeated or overlapping supports.

The construction generalizes the single-wall subdivision argument in
`FinitePolyhedralComplex.exists_segment_subdivision_subsingleton_crossings`:
split between the first two distinct crossing times and induct on their number.
It uses the existing `WallComplement` crossing events and segment rescaling API.
No closedness, convexity, lattice, or dimension hypothesis is needed in addition
to the given admissibility of the path.
-/

public noncomputable section

open Set Mei.Convex

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y z : WallComplement W} {t : ℝ}

/-- The distinct crossing times split at an allowed interior vertex, rescaled
back to the original segment. Simultaneous wall indices remain one time. -/
theorem orderedCrossingTimes_subdivide (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    orderedCrossingTimes e =
      ((orderedCrossingTimes e₁).map fun s => s * t) ++
      ((orderedCrossingTimes e₂).map fun s => 1 - (1 - s) * (1 - t)) := by
  have hp : (((orderedCrossingTimes e₁).map fun s => s * t) ++
      ((orderedCrossingTimes e₂).map fun s => 1 - (1 - s) * (1 - t))).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_map.mpr ((pairwise_orderedCrossingTimes e₁).imp ?_),
      List.pairwise_map.mpr ((pairwise_orderedCrossingTimes e₂).imp ?_), ?_⟩
    · intro a b hab
      exact mul_lt_mul_of_pos_right hab ht.1
    · intro a b hab
      nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2)]
    · intro a ha b hb
      obtain ⟨a, ha₀, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, hb₀, rfl⟩ := List.mem_map.mp hb
      have ha' := mem_Ioo_of_mem_orderedCrossingTimes e₁ ha₀
      have hb' := mem_Ioo_of_mem_orderedCrossingTimes e₂ hb₀
      nlinarith [mul_pos (sub_pos.mpr ha'.2) ht.1,
        mul_pos hb'.1 (sub_pos.mpr ht.2)]
  apply (pairwise_orderedCrossingTimes e).eq_of_mem_iff hp
  intro s
  simp only [mem_orderedCrossingTimes, crossings_subdivide hz ht, mem_union, mem_image,
    Prod.exists, Prod.mk.injEq, List.mem_append, List.mem_map]
  aesop

/-- The first subsegment retains each signed event after rescaling its parameter
to the original segment. Positive rescaling preserves the crossing exponents. -/
theorem signedCrossingEvent_subdivide_left (ν : ι → V →ₗ[ℝ] ℝ)
    (hz : z.val = AffineMap.lineMap x.val y.val t) (ht : t ∈ Ioc (0 : ℝ) 1)
    {s : ℝ} (hs : s ≤ 1) :
    signedCrossingEvent ν x y (s * t) = signedCrossingEvent ν x z s := by
  ext ⟨j, r⟩
  simp only [mem_signedCrossingEvent, mem_crossings_subdivide_left hz ht,
    hs, and_true, hz, AffineMap.lineMap_apply_module', add_sub_cancel_right,
    map_smul, smul_eq_mul, mul_pos_iff_of_pos_left ht.1]

/-- Subdivision retains exactly the ordered signed simultaneous events. -/
theorem segmentCrossingEvents_subdivide (ν : ι → V →ₗ[ℝ] ℝ)
    (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    segmentCrossingEvents ν e = segmentCrossingEvents ν e₁ ++ segmentCrossingEvents ν e₂ := by
  have hleft (s : ℝ) (hs : s ∈ orderedCrossingTimes e₁) :
      signedCrossingEvent ν x y (s * t) = signedCrossingEvent ν x z s := by
    exact signedCrossingEvent_subdivide_left ν hz ⟨ht.1, ht.2.le⟩
      (mem_Ioo_of_mem_orderedCrossingTimes e₁ hs).2.le
  have hright (s : ℝ) (hs : s ∈ orderedCrossingTimes e₂) :
      signedCrossingEvent ν x y (1 - (1 - s) * (1 - t)) = signedCrossingEvent ν z y s := by
    have hs' := mem_Ioo_of_mem_orderedCrossingTimes e₂ hs
    have hv : y.val - z.val = (1 - t) • (y.val - x.val) := by
      rw [hz]
      exact AffineMap.right_vsub_lineMap x.val y.val t
    ext ⟨j, r⟩
    simp only [mem_signedCrossingEvent, mem_crossings_subdivide_right hz ⟨ht.1.le, ht.2⟩,
      hs'.1.le, and_true, hv, map_smul, smul_eq_mul,
      mul_pos_iff_of_pos_left (sub_pos.mpr ht.2)]
  simp only [segmentCrossingEvents_def, orderedCrossingTimes_subdivide e e₁ e₂ ht hz,
    List.map_append, List.map_map]
  exact congrArg₂ List.append (List.map_congr_left hleft) (List.map_congr_left hright)

private theorem exists_split_first_event {x y : WallComplement W} (e : x ⟶ y)
    (a b : ℝ) (l : List ℝ) (hl : orderedCrossingTimes e = a :: b :: l) :
    ∃ (z : WallComplement W) (_ : x ⟶ z) (e₂ : z ⟶ y) (t : ℝ),
      t ∈ Ioo (0 : ℝ) 1 ∧ z.val = AffineMap.lineMap x.val y.val t ∧
      (Prod.snd '' crossings x z).Subsingleton ∧
      (orderedCrossingTimes e₂).length < (orderedCrossingTimes e).length := by
  have ha := mem_Ioo_of_mem_orderedCrossingTimes e (by simp [hl] : a ∈ orderedCrossingTimes e)
  have hb := mem_Ioo_of_mem_orderedCrossingTimes e (by simp [hl] : b ∈ orderedCrossingTimes e)
  have hpair := pairwise_orderedCrossingTimes e
  rw [hl, List.pairwise_cons] at hpair
  obtain ⟨t, hat, htb⟩ := exists_between (hpair.1 b (by simp))
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans hat, htb.trans hb.2⟩
  have hgap {s : ℝ} (hs : s ∈ orderedCrossingTimes e) (hst : s ≤ t) : s = a := by
    simp only [hl, List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · rfl
    · exact (not_le_of_gt htb hst).elim
    · have hbs := (List.pairwise_cons.mp hpair.2).1 s hs
      exact (not_lt_of_ge (hst.trans htb.le) hbs).elim
  let z : WallComplement W := ⟨AffineMap.lineMap x.val y.val t, fun j hj => by
    have he := hgap ((mem_orderedCrossingTimes e t).mpr
      ⟨j, (mem_crossings x y j t).mpr ⟨⟨ht.1.le, ht.2.le⟩, hj⟩⟩) le_rfl
    exact (ne_of_gt hat) he⟩
  have hz : z.val = AffineMap.lineMap x.val y.val t := rfl
  let e₁ : x ⟶ z := ⟨e.down.subdivide_left ⟨ht.1, ht.2.le⟩ hz⟩
  let e₂ : z ⟶ y := ⟨e.down.subdivide_right ⟨ht.1.le, ht.2⟩ hz⟩
  have hfirst {j : ι} {s : ℝ} (hs : (j, s) ∈ crossings x z) : s * t = a := by
    obtain ⟨hs', hsle⟩ := (mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩ j s).mp hs
    exact hgap ((mem_orderedCrossingTimes e _).mpr ⟨j, hs'⟩)
      (mul_le_of_le_one_left ht.1.le hsle)
  have hsingle : (Prod.snd '' crossings x z).Subsingleton := by
    rintro s ⟨⟨j, s⟩, hs, rfl⟩ u ⟨⟨j', u⟩, hu, rfl⟩
    exact mul_right_cancel₀ ht.1.ne' ((hfirst hs).trans (hfirst hu).symm)
  obtain ⟨j, hj⟩ := (mem_orderedCrossingTimes e a).mp (by simp [hl])
  have hnonempty : (orderedCrossingTimes e₁) ≠ [] := by
    have ham : (j, a / t) ∈ crossings x z := by
      rw [mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩]
      exact ⟨by simpa only [div_mul_cancel₀ _ ht.1.ne'] using hj,
        (div_le_one ht.1).mpr hat.le⟩
    exact List.ne_nil_of_mem ((mem_orderedCrossingTimes e₁ _).mpr ⟨j, ham⟩)
  have hlen := congrArg List.length (orderedCrossingTimes_subdivide e e₁ e₂ ht hz)
  simp only [List.length_append, List.length_map] at hlen
  have hpos := List.length_pos_iff.mpr hnonempty
  exact ⟨z, e₁, e₂, t, ht, hz, hsingle, by omega⟩

/-- Subdivide an admissible segment so that each piece has at most one crossing
time. Every indexed wall at a simultaneous crossing stays in the same piece. -/
theorem exists_segment_subdivision_subsingleton_crossingTimes (e : x ⟶ y) :
    ∃ q : AdmissiblePLPath x y, e.toPath.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (Prod.snd '' crossings u v).Subsingleton) := by
  generalize hn : (orderedCrossingTimes e).length = n
  induction n using Nat.strong_induction_on generalizing x y with
  | h n ih =>
    rcases hl : orderedCrossingTimes e with _ | ⟨a, _ | ⟨b, l⟩⟩
    · refine ⟨e.toPath, .refl _, ?_⟩
      simp only [Quiver.Path.vertices_toPath, List.isChain_pair]
      rintro s ⟨⟨j, s⟩, hs, rfl⟩
      have := (mem_orderedCrossingTimes e s).mpr ⟨j, hs⟩
      simp [hl] at this
    · refine ⟨e.toPath, .refl _, ?_⟩
      simp only [Quiver.Path.vertices_toPath, List.isChain_pair]
      rintro s ⟨⟨j, s⟩, hs, rfl⟩ u ⟨⟨j', u⟩, hu, rfl⟩
      have hs' := (mem_orderedCrossingTimes e s).mpr ⟨j, hs⟩
      have hu' := (mem_orderedCrossingTimes e u).mpr ⟨j', hu⟩
      simp only [hl, List.mem_singleton] at hs' hu'
      exact hs'.trans hu'.symm
    · obtain ⟨z, e₁, e₂, t, ht, hz, hsingle, hlt⟩ := exists_split_first_event e a b l hl
      obtain ⟨q, hq, hqsmall⟩ := ih _ (hn ▸ hlt) e₂ rfl
      refine ⟨e₁.toPath.comp q,
        (Quiver.Path.IsSubdivision.split e e₁ e₂ ht hz).trans (.comp (.refl _) hq), ?_⟩
      exact (Quiver.Path.isChain_vertices_comp _ _ _).mpr
        ⟨by simpa only [Quiver.Path.vertices_toPath, List.isChain_pair] using hsingle, hqsmall⟩

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  {W : ι → Set V} {x y : WallComplement W}

/-- Finite subdivision preserves the entire ordered signed event list, including
all simultaneous indices, rather than only a product of their labels. -/
theorem IsSubdivision.signedCrossingEvents_eq {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) (ν : ι → V →ₗ[ℝ] ℝ) :
    q.signedCrossingEvents ν = p.signedCrossingEvents ν := by
  induction hpq with
  | refl => rfl
  | split e e₁ e₂ ht hz =>
    simpa only [signedCrossingEvents_comp, Quiver.Hom.toPath, signedCrossingEvents_cons,
      signedCrossingEvents_nil, List.nil_append] using
      (segmentCrossingEvents_subdivide ν e e₁ e₂ ht hz).symm
  | comp hp hq ihp ihq => simp only [signedCrossingEvents_comp, ihp, ihq]
  | trans hpq hqr ihpq ihqr => exact ihqr.trans ihpq

/-- Every admissible polygonal path has a subdivision into single-event
segments. This retains its geometry, endpoints and all signed crossings. -/
theorem exists_subdivision_subsingleton_crossingTimes (p : AdmissiblePLPath x y) :
    ∃ q : AdmissiblePLPath x y, p.IsSubdivision q ∧
      q.vertices.IsChain (fun u v => (Prod.snd '' crossings u v).Subsingleton) := by
  induction p with
  | nil => exact ⟨.nil, .refl _, by simp⟩
  | cons p e ih =>
    obtain ⟨q, hq, hsmall⟩ := ih
    obtain ⟨r, hr, hrsmall⟩ := exists_segment_subdivision_subsingleton_crossingTimes e
    exact ⟨q.comp r, .comp hq hr,
      (isChain_vertices_comp _ _ _).mpr ⟨hsmall, hrsmall⟩⟩

end Quiver.Path
