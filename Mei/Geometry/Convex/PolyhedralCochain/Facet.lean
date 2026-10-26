/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Face
public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import Mei.Analysis.Convex.Exposed.Orientation

/-!
# Oriented facets of polyhedral cells

Every exposed facet of an oriented rational-normal polyhedron is an oriented
cell of one higher codimension. The orientation uses the outward conormal
and the coboundary sign: contraction along an outward tangent vector gives
the negative parent orientation. This is the generator operation for the
polyhedral coboundary, including for lower-dimensional unbounded cells with
lineality.

The construction uses `IsExposed.facetOrientation` and the rational-normal
face theorem `IsExtreme.isRationalNormalPolyhedron`.
-/

public section

noncomputable section

namespace Mei.OrientedCell

open Module

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- An exposed facet with its induced conormal orientation and coboundary sign. -/
def facet (σ : OrientedCell h k) {F : Set V} (hF : IsPolyhedralFace σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    OrientedCell h (k + 1) := by
  have := h.finiteDimensional
  obtain ⟨hne, hex⟩ := isPolyhedralFace_iff.mp hF
  have ho : σ.orientation.IsConormal (vectorSpan ℝ σ.carrier) := by
    simpa only [direction_affineSpan] using σ.isConormal
  have hconv : Convex ℝ σ.carrier := by
    obtain ⟨Q, hQ⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
    exact hQ ▸ Q.convex
  refine
    { carrier := F
      rational := hex.isExtreme.isRationalNormalPolyhedron σ.rational
        (hex.convex hconv)
      nonempty := hne
      finrank_direction_add := ?_
      orientation := hex.facetOrientation hne hdim σ.orientation ho
      isConormal := ?_ }
  · have hσ := σ.finrank_direction_add
    rw [direction_affineSpan] at hσ ⊢
    omega
  · simpa only [direction_affineSpan] using
      hex.isConormal_facetOrientation hne hdim σ.orientation ho

/-- The induced facet has the original facet as its support. -/
@[simp]
theorem facet_carrier (σ : OrientedCell h k) {F : Set V} (hF : IsPolyhedralFace σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    (σ.facet hF hdim).carrier = F := (rfl)

/-- The facet orientation is the canonical signed extension of the parent orientation. -/
@[simp]
theorem facet_orientation (σ : OrientedCell h k) {F : Set V}
    (hF : IsPolyhedralFace σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    letI := h.finiteDimensional
    (σ.facet hF hdim).orientation =
      (isPolyhedralFace_iff.mp hF).2.facetOrientation (isPolyhedralFace_iff.mp hF).1 hdim
        σ.orientation (by simpa only [direction_affineSpan] using σ.isConormal) := (rfl)

/-- Reversing a cell reverses each of its induced facets. -/
@[simp]
theorem facet_reverse (σ : OrientedCell h k) {F : Set V}
    (hF : IsPolyhedralFace σ.carrier F)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ σ.carrier)) :
    σ.reverse.facet (F := F) (by simpa only [reverse_carrier] using hF)
      (by rw [reverse_carrier σ]; exact hdim) =
      (σ.facet hF hdim).reverse := by
  have := h.finiteDimensional
  ext1
  · simp
  · simp only [facet_orientation, reverse_orientation, reverse_carrier]
    exact (isPolyhedralFace_iff.mp hF).2.facetOrientation_neg _ _ _ _

end Mei.OrientedCell
