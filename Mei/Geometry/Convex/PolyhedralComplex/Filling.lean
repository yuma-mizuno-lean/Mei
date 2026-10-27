/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Triangle.Filling
public import Mei.Geometry.Affine.Triangle.Transverse
public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# Cone fillings avoiding the higher skeleton

A family of segments missing the codimension-at-least-three skeleton admits a
common cone vertex whose entire filled triangles still miss that skeleton.
The original segments are fixed. The vertex can lie in any prescribed
nonempty open set and avoid additional proper affine subspaces.

This isolates the higher-codimension avoidance needed when decomposing a
polygonal filling into local wall and joint contributions. A second choice theorem makes
each filling plane complementary to every joint it meets, simultaneously with
avoidance of the higher skeleton.
The constructions apply `Mei.exists_mem_open_triangle_fillings_avoid` and
`Mei.exists_mem_open_triangle_fillings_transverse` to the actual cell supports;
the segments need not avoid their affine spans.
-/

public section

open Set Module

namespace Mei.FinitePolyhedralComplex

variable {N V ι μ : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} [Countable ι] [Countable μ]

/-- Choose one apex so that the filled triangles over fixed segments avoid the
entire higher skeleton. No purity, boundedness or lineality restriction on the
complex is needed. Arbitrary proper affine exceptions may also be avoided by
the apex. -/
theorem exists_mem_open_triangle_fillings_disjoint_codimensionAtLeast_three
    (C : FinitePolyhedralComplex h) (x y : ι → V)
    (hbase : ∀ a, Disjoint (segment ℝ (x a) (y a)) (C.codimensionAtLeast 3).support)
    (A : μ → AffineSubspace ℝ V) (hA : ∀ j, A j ≠ ⊤)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ j, z ∉ A j) ∧
      ∀ a, Disjoint (convexHull ℝ {z, x a, y a}) (C.codimensionAtLeast 3).support := by
  have := h.finiteDimensional
  obtain ⟨z, hzU, hzA, hz⟩ := Mei.exists_mem_open_triangle_fillings_avoid x y
    (fun Q : (C.codimensionAtLeast 3).cells => (Q : Set V))
    (fun Q => by
      have hd := ((C.mem_codimensionAtLeast_cells 3 Q).mp Q.property).2
      omega)
    (fun a Q => (hbase a).mono_right
      (fun w hw => mem_support.mpr ⟨Q, Q.property, hw⟩))
    A hA hU hne
  refine ⟨z, hzU, hzA, fun a => disjoint_left.mpr fun w hw hws => ?_⟩
  obtain ⟨Q, hQ, hwQ⟩ := mem_support.mp hws
  exact disjoint_left.mp (hz a ⟨Q, hQ⟩) hw hwQ

/-- A common apex gives fillings avoiding the higher skeleton and complementary
to every joint they meet. All base segments remain fixed, including segments
tangent to a joint direction; their fillings miss that joint instead. Additional
proper affine exceptions may be imposed on the apex. -/
theorem exists_mem_open_triangle_fillings_transverse_joints
    (C : FinitePolyhedralComplex h) (x y : ι → V)
    (hbase : ∀ a, Disjoint (segment ℝ (x a) (y a)) (C.codimensionAtLeast 2).support)
    (A : μ → AffineSubspace ℝ V) (hA : ∀ j, A j ≠ ⊤)
    {U : Set V} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, (∀ j, z ∉ A j) ∧
      (∀ a, Disjoint (convexHull ℝ {z, x a, y a}) (C.codimensionAtLeast 3).support) ∧
      ∀ a, ∀ J ∈ C.joints, (convexHull ℝ {z, x a, y a} ∩ J).Nonempty →
        IsCompl (affineSpan ℝ J).direction (vectorSpan ℝ {z, x a, y a}) := by
  have := h.finiteDimensional
  let B : (ι × (C.codimensionAtLeast 3).cells) ⊕ μ → AffineSubspace ℝ V :=
    Sum.elim (fun a => affineSpan ℝ ({x a.1, y a.1} ∪ (a.2 : Set V))) A
  have hB : ∀ a, B a ≠ ⊤ := by
    rintro (⟨a, Q⟩ | j)
    · have he : affineSpan ℝ ({x a, y a} ∪ (Q : Set V)) =
          affineSpan ℝ ({x a, y a} ∪ (affineSpan ℝ (Q : Set V) : Set V)) := by
        simp only [AffineSubspace.span_union, AffineSubspace.affineSpan_coe]
      dsimp only [B, Sum.elim_inl]
      rw [he]
      apply (affineSpan ℝ (Q : Set V)).affineSpan_pair_union_ne_top_of_finrank
      have hd := ((C.mem_codimensionAtLeast_cells 3 Q).mp Q.property).2
      omega
    · exact hA j
  obtain ⟨z, hzU, hzB, hz⟩ := Mei.exists_mem_open_triangle_fillings_transverse x y
    (fun J : C.joints => (J : Set V))
    (fun J => ((C.mem_cellsOfCodimension 2 J).mp J.property).2)
    (fun a J => (hbase a).mono_right (fun w hw => mem_support.mpr
      ⟨J, C.cellsOfCodimension_subset_codimensionAtLeast_cells 2 J.property, hw⟩))
    B hB hU hne
  refine ⟨z, hzU, fun j => hzB (.inr j), fun a => ?_, fun a J hJ hne => ?_⟩
  · apply disjoint_left.mpr
    rintro w hw hws
    obtain ⟨Q, hQ, hwQ⟩ := mem_support.mp hws
    have hQ₂ : Q ∈ (C.codimensionAtLeast 2).cells := by
      obtain ⟨hQC, hd⟩ := (C.mem_codimensionAtLeast_cells 3 Q).mp hQ
      exact (C.mem_codimensionAtLeast_cells 2 Q).mpr ⟨hQC, by omega⟩
    have hb := (hbase a).mono_right (fun u hu => mem_support.mpr ⟨Q, hQ₂, hu⟩)
    have hb' : Disjoint (convexHull ℝ {x a, y a}) Q := by
      simpa only [convexHull_pair] using hb
    have ht := hb'.convexHull_insert_of_notMem_affineSpan (hzB (.inl (a, ⟨Q, hQ⟩)))
    exact disjoint_left.mp ht hw hwQ
  · exact (hz a ⟨J, hJ⟩).resolve_left (not_disjoint_iff_nonempty_inter.mpr hne)

end Mei.FinitePolyhedralComplex
