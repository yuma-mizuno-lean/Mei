/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Pairing
public import Mei.Geometry.Convex.Polyhedron.SegmentSubdivision
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Subdivision of one-dimensional intersection tests

Splitting a segment at a point outside a wall preserves its intersection
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
The proof uses cell convexity and Mathlib's betweenness transitivity to keep
intersections on at most one side of the split vertex, `openSegment_subset_union`
to partition the parameter interval, and `Module.Ray.evalSign_smul`
for the orientation under positive parameter rescaling.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Inserting an interior parameter vertex outside the cell adds the two
subsegment intersection indices. The original segment may be degenerate if it
misses the cell. No transversality condition is imposed. -/
theorem intersectionIndex_subdivide (σ : OrientedCell h 1) {x y z : V} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1)
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
  -- If both sides meet the convex cell, the split vertex lies in the cell too.
  have hexclusive : ¬((segment ℝ x z ∩ σ.carrier).Nonempty ∧
      (segment ℝ z y ∩ σ.carrier).Nonempty) := by
    rintro ⟨⟨p, hp, hpσ⟩, ⟨q, hq, hqσ⟩⟩
    have hzp : Wbtw ℝ p z y :=
      (mem_segment_iff_wbtw.mp hzseg).trans_left_right (mem_segment_iff_wbtw.mp hp)
    have hzpq : z ∈ segment ℝ p q :=
      mem_segment_iff_wbtw.mpr (hzp.trans_right_left (mem_segment_iff_wbtw.mp hq))
    obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    have hconv : Convex ℝ σ.carrier := hP ▸ P.convex
    exact hzσ (hconv.segment_subset hpσ hqσ hzpq)
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
impose no avoidance conditions. No transversality condition is needed. -/
theorem intersectionPairing_subdivide (f : OrientedCell h 1 →₀ E) {x y z : V} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hz : z = AffineMap.lineMap x y t)
    (hzf : ∀ σ ∈ f.support, z ∉ σ.carrier) :
    intersectionPairing (R := R) ![x, y] f =
      intersectionPairing (R := R) ![x, z] f + intersectionPairing (R := R) ![z, y] f := by
  simp only [intersectionPairing_apply, Finsupp.sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [σ.intersectionIndex_subdivide ht hz (hzf σ hσ), add_zsmul]

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
    refine OrientedCell.intersectionPairing_subdivide f ht hz ?_
    intro τ hτ
    obtain ⟨j, rfl⟩ := hf τ hτ
    exact c.notMem j
  | comp hp hq ihp ihq => simp only [addWeightOfEPs_comp, ihp, ihq]
  | trans hpq hqr ihpq ihqr => exact ihqr.trans ihpq

end Quiver.Path
