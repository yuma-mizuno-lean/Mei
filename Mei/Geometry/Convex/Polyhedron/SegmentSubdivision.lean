/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.AdmissiblePath

/-!
# Subdividing admissible segments

Inserting an allowed vertex inside an admissible segment gives two admissible
segments. `Quiver.Path.IsSubdivision` records finite repetitions and concatenations
of these insertions. Their crossing parameters rescale to the original parameter interval.
These formulas retain the wall indices, including simultaneous crossings in an
arbitrary wall family, and allow ordered crossing lists to be compared after subdivision.

The affine parameter calculations use Mathlib's `AffineMap.lineMap_lineMap_right`
and `AffineMap.lineMap_lineMap_left`.
-/

public section

open Set

namespace Mei.Convex.WallComplement

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V} {x y z : WallComplement W} {t : ℝ}

/-- Restricting an admissible segment to its first, nonconstant parameter interval
preserves admissibility, provided the new vertex lies off all walls. -/
theorem AdmissibleSegment.subdivide_left (e : AdmissibleSegment x y)
    (ht : t ∈ Ioc (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    AdmissibleSegment x z where
  transverse i hi := by
    obtain ⟨s, hs, hi⟩ := hi
    have he := e.transverse i ⟨s * t,
      ⟨mul_nonneg hs.1 ht.1.le, by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) ht.1.le, ht.2]⟩,
      by simpa only [hz, AffineMap.lineMap_lineMap_right] using hi⟩
    intro hd
    apply he
    rw [hz, AffineMap.lineMap_apply_module', add_sub_cancel_right] at hd
    exact (Submodule.smul_mem_iff _ ht.1.ne').mp hd
  regular s hs := by
    simpa only [hz, AffineMap.lineMap_lineMap_right] using
      e.regular (s * t) ⟨mul_nonneg hs.1 ht.1.le, by
        nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) ht.1.le, ht.2]⟩

/-- Restricting an admissible segment to its last, nonconstant parameter interval
preserves admissibility. -/
theorem AdmissibleSegment.subdivide_right (e : AdmissibleSegment x y)
    (ht : t ∈ Ico (0 : ℝ) 1) (hz : z.val = AffineMap.lineMap x.val y.val t) :
    AdmissibleSegment z y := by
  have hz' : z.val = AffineMap.lineMap y.val x.val (1 - t) := by
    rw [AffineMap.lineMap_apply_one_sub, hz]
  exact (e.symm.subdivide_left ⟨by linarith [ht.2], by linarith [ht.1]⟩ hz').symm

/-- The first subsegment's parameter `s` corresponds to the original parameter `s * t`. -/
theorem mem_crossings_subdivide_left (hz : z.val = AffineMap.lineMap x.val y.val t)
    (ht : t ∈ Ioc (0 : ℝ) 1) (i : ι) (s : ℝ) :
    (i, s) ∈ crossings x z ↔ (i, s * t) ∈ crossings x y ∧ s ≤ 1 := by
  simp only [mem_crossings, hz, AffineMap.lineMap_lineMap_right, mem_Icc]
  constructor
  · rintro ⟨⟨hs₀, hs₁⟩, hi⟩
    exact ⟨⟨⟨mul_nonneg hs₀ ht.1.le, by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs₁) ht.1.le, ht.2]⟩, hi⟩, hs₁⟩
  · rintro ⟨⟨⟨hs₀, -⟩, hi⟩, hs₁⟩
    exact ⟨⟨by nlinarith [ht.1], hs₁⟩, hi⟩

/-- The last subsegment's parameter `s` corresponds to `1 - (1 - s) * (1 - t)`. -/
theorem mem_crossings_subdivide_right (hz : z.val = AffineMap.lineMap x.val y.val t)
    (ht : t ∈ Ico (0 : ℝ) 1) (i : ι) (s : ℝ) :
    (i, s) ∈ crossings z y ↔
      (i, 1 - (1 - s) * (1 - t)) ∈ crossings x y ∧ 0 ≤ s := by
  rw [mem_crossings_swap y z, mem_crossings_subdivide_left (x := y) (y := x)
    (by simpa only [AffineMap.lineMap_apply_one_sub] using hz)
    (⟨by linarith [ht.2], by linarith [ht.1]⟩ :
      1 - t ∈ Ioc (0 : ℝ) 1),
    mem_crossings_swap x y]
  constructor <;> rintro ⟨hi, hs⟩ <;> exact ⟨hi, by linarith⟩

/-- Rescaling the two subsegments recovers exactly the original indexed crossings. -/
theorem crossings_subdivide (hz : z.val = AffineMap.lineMap x.val y.val t)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    crossings x y =
      (fun a : ι × ℝ => (a.1, a.2 * t)) '' crossings x z ∪
      (fun a : ι × ℝ => (a.1, 1 - (1 - a.2) * (1 - t))) '' crossings z y := by
  ext ⟨i, s⟩
  constructor
  · intro hs
    by_cases hst : s ≤ t
    · left
      refine ⟨(i, s / t), ?_, by simp [ht.1.ne']⟩
      rw [mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩]
      exact ⟨by simpa only [div_mul_cancel₀ _ ht.1.ne'] using hs,
        (div_le_one ht.1).mpr hst⟩
    · right
      have he : 1 - (1 - (s - t) / (1 - t)) * (1 - t) = s := by
        field_simp [show 1 - t ≠ 0 by linarith [ht.2]]
        ring
      refine ⟨(i, (s - t) / (1 - t)), ?_, Prod.ext rfl he⟩
      rw [mem_crossings_subdivide_right hz ⟨ht.1.le, ht.2⟩, he]
      exact ⟨hs, div_nonneg (by linarith) (by linarith [ht.2])⟩
  · rintro (⟨⟨j, r⟩, hr, he⟩ | ⟨⟨j, r⟩, hr, he⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ((mem_crossings_subdivide_left hz ⟨ht.1, ht.2.le⟩ j r).mp hr).1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ((mem_crossings_subdivide_right hz ⟨ht.1.le, ht.2⟩ j r).mp hr).1

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {W : ι → Set V}

/-- Finite subdivision of an admissible polygonal path by allowed interior vertices.
The relation is generated by splitting a segment, concatenating subdivisions,
and repeating these operations. The first path is the original, the second the refinement. -/
inductive IsSubdivision : {x y : WallComplement W} →
    AdmissiblePLPath x y → AdmissiblePLPath x y → Prop
  /-- Every path subdivides itself. -/
  | refl {x y} (p : AdmissiblePLPath x y) : IsSubdivision p p
  /-- Inserting an allowed interior vertex splits one segment into two. -/
  | split {x y z : WallComplement W} (e : x ⟶ y) (e₁ : x ⟶ z) (e₂ : z ⟶ y)
      {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
      (hz : z.val = AffineMap.lineMap x.val y.val t) :
      IsSubdivision e.toPath (e₁.toPath.comp e₂.toPath)
  /-- Subdivisions can be performed on either side of a concatenation. -/
  | comp {x y z} {p p' : AdmissiblePLPath x y} {q q' : AdmissiblePLPath y z}
      (hp : IsSubdivision p p') (hq : IsSubdivision q q') :
      IsSubdivision (p.comp q) (p'.comp q')
  /-- A subdivision of a subdivision is a subdivision of the original path. -/
  | trans {x y} {p q r : AdmissiblePLPath x y}
      (hpq : IsSubdivision p q) (hqr : IsSubdivision q r) : IsSubdivision p r

end Quiver.Path
