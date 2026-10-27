/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.Exposed
public import Mei.Analysis.Convex.Separation

/-!
# Opposite exposing functionals at a common facet

Two convex sets spanning the same affine subspace and meeting exactly in a common
facet lie on opposite sides of that facet. There is a single continuous linear
functional exposing the facet in one set whose negative exposes it in the other.
This identifies the opposite outward conormals of adjacent cells, including cells
in a proper affine subspace and unbounded cells with lineality.

The proof applies Mathlib's `geometric_hahn_banach_of_nonempty_interior` inside the
common affine span and extends its separating functional to the ambient space.
`IsExposed.eq_of_finrank_vectorSpan_eq` identifies the separating faces with the
prescribed facet.
-/

public section

open Set Module

namespace IsExposed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {P Q F : Set V}

/-- Convex sets with the same affine span meeting exactly in a common facet admit
opposite exposing functionals for that facet. No closedness or polyhedrality is needed. -/
theorem exists_opposite_exposing (hF : IsExposed ℝ P F) (hG : IsExposed ℝ Q F)
    (hP : Convex ℝ P) (hQ : Convex ℝ Q) (hne : F.Nonempty)
    (hdim : finrank ℝ (vectorSpan ℝ F) + 1 = finrank ℝ (vectorSpan ℝ P))
    (hspan : affineSpan ℝ P = affineSpan ℝ Q) (hinter : P ∩ Q = F) :
    ∃ l : V →L[ℝ] ℝ, F = l.toExposed P ∧ F = (-l).toExposed Q := by
  classical
  obtain ⟨q, hq⟩ := hne
  have hPne : P.Nonempty := ⟨q, hF.subset hq⟩
  have hQne : Q.Nonempty := ⟨q, hG.subset hq⟩
  have hdisj : Disjoint (intrinsicInterior ℝ P) Q := by
    apply Set.disjoint_left.mpr
    intro x hxP hxQ
    have hxF : x ∈ F := hinter ▸ ⟨intrinsicInterior_subset hxP, hxQ⟩
    have he := hF.eq_of_mem_intrinsicInterior hxF hxP
    rw [he] at hdim
    omega
  obtain ⟨l, c, hcomp, hPsep, hQsep⟩ :=
    hP.exists_separating_of_disjoint_intrinsicInterior hQ hPne hQne
      (by rw [hspan]; exact subset_affineSpan ℝ Q) hdisj
  have hc : c = l q := le_antisymm (hQsep q (hG.subset hq)) (hPsep q (hF.subset hq))
  have hleP (x : V) (hx : x ∈ P) : l x ≤ l q := hc ▸ hPsep x hx
  have hleQ (x : V) (hx : x ∈ Q) : l q ≤ l x := hc ▸ hQsep x hx
  have hsubP : F ⊆ l.toExposed P := by
    intro x hx
    have he : l x = l q := le_antisymm (hleP x (hF.subset hx)) (hleQ x (hG.subset hx))
    exact ⟨hF.subset hx, fun y hy => (hleP y hy).trans he.ge⟩
  have hsubQ : F ⊆ (-l).toExposed Q := by
    intro x hx
    have he : l x = l q := le_antisymm (hleP x (hF.subset hx)) (hleQ x (hG.subset hx))
    exact ⟨hG.subset hx, fun y hy => by
      simpa only [neg_apply, neg_le_neg_iff, he] using hleQ y hy⟩
  have hproperP : l.toExposed P ≠ P := by
    intro he
    apply hcomp
    ext v
    have hker := l.vectorSpan_toExposed_le_ker P
    rw [he] at hker
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      ContinuousLinearMap.coe_coe, LinearMap.mem_ker] using hker v.property
  have hdir : vectorSpan ℝ P = vectorSpan ℝ Q := by
    simpa only [direction_affineSpan] using congrArg AffineSubspace.direction hspan
  have hproperQ : (-l).toExposed Q ≠ Q := by
    intro he
    apply hcomp
    ext v
    have hv : (v : V) ∈ vectorSpan ℝ Q := hdir ▸ v.property
    have hker := (-l).vectorSpan_toExposed_le_ker Q
    rw [he] at hker
    have hz := hker hv
    simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      neg_apply, neg_eq_zero, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.zero_apply] using hz
  exact ⟨l, hF.eq_of_subset_of_finrank_add_one ⟨q, hq⟩ hdim
    ContinuousLinearMap.toExposed.isExposed hsubP hproperP,
    hG.eq_of_subset_of_finrank_add_one ⟨q, hq⟩ (by rw [← hdir]; exact hdim)
      ContinuousLinearMap.toExposed.isExposed hsubQ hproperQ⟩

end IsExposed
