/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Crossing
public import Mei.Geometry.Convex.Polyhedron.SegmentSubdivision
public import Mathlib.Analysis.Convex.Between

/-!
# Subdivision of one-dimensional intersection tests

Splitting a transverse segment at a point outside a wall preserves its intersection
index and hence its coefficient-valued pairing. The new parameter face must miss the
wall: otherwise the two closed subsegments would count the same intersection twice.
The conclusion allows stationary segments missing the wall, real offsets, unbounded
cells and lineality.

Finite subdivisions of admissible polygonal paths therefore preserve the sum of
their segment pairings. This permits an intersection test along a meridian edge to
be evaluated on smaller crossing neighborhoods without changing its value.
Path subdivision uses the existing `Quiver.Path.IsSubdivision` relation.
-/

/-
The proof uses `OrientedCell.IsTransverse.subsingleton_convexHull_inter_affineSpan`
to isolate the intersection, Mathlib's `openSegment_subset_union` and betweenness
transitivity to partition the parameter interval, and `Module.Ray.evalSign_smul`
for the orientation under positive parameter rescaling.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Restricting a transverse segment to a nontrivial parameter interval preserves
transversality. The parameters may occur in either order, and disjoint stationary
tests are allowed. -/
theorem IsTransverse.subsegment {σ : OrientedCell h 1} {x y a b : V}
    (hv : σ.IsTransverse ![x, y]) {s u : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (hsu : s ≠ u)
    (ha : a = AffineMap.lineMap x y s) (hb : b = AffineMap.lineMap x y u) :
    σ.IsTransverse ![a, b] := by
  have hseg : segment ℝ a b ⊆ segment ℝ x y := by
    apply (convex_segment x y).segment_subset
    · rw [ha, segment_eq_image_lineMap]
      exact ⟨s, hs, rfl⟩
    · rw [hb, segment_eq_image_lineMap]
      exact ⟨u, hu, rfl⟩
  have hhull : convexHull ℝ (range ![a, b]) ⊆ convexHull ℝ (range ![x, y]) := by
    simpa only [Matrix.range_cons_cons_empty, convexHull_pair] using hseg
  have hdiff : b - a = (u - s) • (y - x) := by
    rw [ha, hb, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    module
  refine ⟨hv.disjoint_intrinsicFrontier.mono_left hhull, fun hm => ?_⟩
  have hlin := hv.linearIndependent (hm.mono (inter_subset_inter_left _ hhull))
  rw [linearIndependent_unique_iff] at hlin ⊢
  simp only [Function.comp_apply, Fin.default_eq_zero, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_zero] at hlin ⊢
  rw [hdiff, map_smul, smul_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr hsu.symm, hlin⟩

/-- Inserting an interior parameter vertex outside the cell adds the two
subsegment intersection indices. The original segment may be degenerate if it
misses the cell. No nondegeneracy condition is imposed on disjoint tests. -/
theorem intersectionIndex_subdivide (σ : OrientedCell h 1) {x y z : V} {t : ℝ}
    (hv : σ.IsTransverse ![x, y]) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hz : z = AffineMap.lineMap x y t) (hzσ : z ∉ σ.carrier) :
    σ.intersectionIndex ![x, y] =
      σ.intersectionIndex ![x, z] + σ.intersectionIndex ![z, y] := by
  classical
  -- Partition the test image into the two closed subsegments.
  have hzseg : z ∈ segment ℝ x y := by
    rw [hz, segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  have hleft : segment ℝ x z ⊆ segment ℝ x y :=
    (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hzseg
  have hright : segment ℝ z y ⊆ segment ℝ x y :=
    (convex_segment x y).segment_subset hzseg (right_mem_segment ℝ x y)
  have hcover : segment ℝ x y ⊆ segment ℝ x z ∪ segment ℝ z y := by
    intro p hp
    rw [← insert_endpoints_openSegment] at hp
    rcases hp with rfl | rfl | hp
    · exact Or.inl (left_mem_segment ℝ _ _)
    · exact Or.inr (right_mem_segment ℝ _ _)
    · rcases openSegment_subset_union x y ⟨t, hz.symm⟩ hp with rfl | hp | hp
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inl (openSegment_subset_segment ℝ _ _ hp)
      · exact Or.inr (openSegment_subset_segment ℝ _ _ hp)
  have hmeet : (segment ℝ x y ∩ σ.carrier).Nonempty ↔
      (segment ℝ x z ∩ σ.carrier).Nonempty ∨
        (segment ℝ z y ∩ σ.carrier).Nonempty := by
    constructor
    · rintro ⟨p, hp, hpσ⟩
      rcases hcover hp with hp | hp
      · exact Or.inl ⟨p, hp, hpσ⟩
      · exact Or.inr ⟨p, hp, hpσ⟩
    · rintro (⟨p, hp, hpσ⟩ | ⟨p, hp, hpσ⟩)
      · exact ⟨p, hleft hp, hpσ⟩
      · exact ⟨p, hright hp, hpσ⟩
  -- Uniqueness of the transverse intersection prevents counting it on both sides.
  have hexclusive : ¬((segment ℝ x z ∩ σ.carrier).Nonempty ∧
      (segment ℝ z y ∩ σ.carrier).Nonempty) := by
    rintro ⟨⟨p, hp, hpσ⟩, ⟨q, hq, hqσ⟩⟩
    have hm : (convexHull ℝ (range ![x, y]) ∩ σ.carrier).Nonempty := by
      rw [Matrix.range_cons_cons_empty, convexHull_pair]
      exact ⟨p, hleft hp, hpσ⟩
    have hsub := hv.subsingleton_convexHull_inter_affineSpan hm
    rw [Matrix.range_cons_cons_empty, convexHull_pair] at hsub
    have hpq := hsub ⟨hleft hp, subset_affineSpan ℝ _ hpσ⟩
      ⟨hright hq, subset_affineSpan ℝ _ hqσ⟩
    subst q
    have hpz : p = z :=
      ((wbtw_swap_left_iff ℝ y).mp ⟨(mem_segment_iff_wbtw.mp hzseg).trans_left_right
        (mem_segment_iff_wbtw.mp hp), mem_segment_iff_wbtw.mp hq⟩)
    exact hzσ (hpz ▸ hpσ)
  -- Both parameter changes have positive slope, so their orientation signs agree.
  have hsignleft : σ.orientation.evalSign (fun _ : Fin 1 => z - x) =
      σ.orientation.evalSign (fun _ : Fin 1 => y - x) := by
    rw [hz, AffineMap.lineMap_apply_module', add_sub_cancel_right]
    simp only [Module.Ray.evalSign_smul, Fin.prod_univ_one, sign_pos ht.1, one_mul]
  have hsignright : σ.orientation.evalSign (fun _ : Fin 1 => y - z) =
      σ.orientation.evalSign (fun _ : Fin 1 => y - x) := by
    have hdiff : y - z = (1 - t) • (y - x) := by
      rw [hz, AffineMap.lineMap_apply_module']
      module
    rw [hdiff]
    simpa only [Fin.prod_univ_one, sign_pos (sub_pos.mpr ht.2), one_mul]
      using (Module.Ray.evalSign_smul σ.orientation (fun _ : Fin 1 => y - x)
        (fun _ => 1 - t))
  rw [intersectionIndex_pair, intersectionIndex_pair, intersectionIndex_pair,
    hsignleft, hsignright, hmeet]
  aesop

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Subdividing a segment at a point outside every cell with nonzero coefficient
preserves its pairing with a finite presentation. Cells with zero coefficient
impose no transversality or avoidance conditions. -/
theorem intersectionPairing_subdivide (f : OrientedCell h 1 →₀ E) {x y z : V} {t : ℝ}
    (hv : ∀ σ ∈ f.support, σ.IsTransverse ![x, y])
    (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z = AffineMap.lineMap x y t)
    (hzf : ∀ σ ∈ f.support, z ∉ σ.carrier) :
    intersectionPairing (R := R) ![x, y] f =
      intersectionPairing (R := R) ![x, z] f + intersectionPairing (R := R) ![z, y] f := by
  simp only [intersectionPairing_apply, Finsupp.sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [σ.intersectionIndex_subdivide (hv σ hσ) ht hz (hzf σ hσ), add_zsmul]

end Mei.OrientedCell

namespace Quiver.Path

open Mei Mei.Convex.WallComplement

variable {N V ι : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {σ : ι → OrientedCell h 1} {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]
  {x y : WallComplement (fun j => (σ j).carrier)}

/-- Finite subdivision by allowed vertices preserves the sum of segment
intersection pairings. The wall family may have repeated cells and simultaneous
coplanar crossings; no choice of coorientations or labels is needed. -/
theorem IsSubdivision.addWeightOfEPs_intersectionPairing_eq
    {p q : AdmissiblePLPath x y} (hpq : p.IsSubdivision q)
    (f : OrientedCell h 1 →₀ E) (hf : ∀ τ ∈ f.support, ∃ j, τ = σ j) :
    q.addWeightOfEPs (fun a b => OrientedCell.intersectionPairing (R := R) ![a.val, b.val] f) =
      p.addWeightOfEPs
        (fun a b => OrientedCell.intersectionPairing (R := R) ![a.val, b.val] f) := by
  induction hpq with
  | refl p => rfl
  | @split a b c e e₁ e₂ t ht hz =>
    simp only [addWeightOfEPs_comp, Quiver.Hom.toPath, addWeightOfEPs_cons,
      addWeightOfEPs_nil, zero_add]
    symm
    refine OrientedCell.intersectionPairing_subdivide f ?_ ht hz ?_
    · intro τ hτ
      obtain ⟨j, rfl⟩ := hf τ hτ
      exact e.down.isTransverse_orientedCell j
    · intro τ hτ
      obtain ⟨j, rfl⟩ := hf τ hτ
      exact c.notMem j
  | comp hp hq ihp ihq => simp only [addWeightOfEPs_comp, ihp, ihq]
  | trans hpq hqr ihpq ihqr => exact ihqr.trans ihpq

end Quiver.Path
