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
The constructions use `Mei.exists_mem_open_triangle_fillings_avoid` for higher
strata and `Mei.exists_affineSubspace_triangle_filling_transverse` for joint
exceptions; the segments need not avoid their affine spans.
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
  choose B hB htrans using fun aj : ι × C.joints =>
    Mei.exists_affineSubspace_triangle_filling_transverse
      (x aj.1) (y aj.1) (aj.2 : Set V)
      ((C.mem_cellsOfCodimension 2 aj.2).mp aj.2.property).2
      ((hbase aj.1).mono_right (fun w hw => mem_support.mpr
        ⟨aj.2, C.cellsOfCodimension_subset_codimensionAtLeast_cells 2 aj.2.property, hw⟩))
  obtain ⟨z, hzU, hz, havoid⟩ :=
    C.exists_mem_open_triangle_fillings_disjoint_codimensionAtLeast_three x y
      (fun a => (hbase a).mono_right (fun w hw => by
        obtain ⟨Q, hQ, hwQ⟩ := mem_support.mp hw
        exact mem_support.mpr
          ⟨Q, C.codimensionAtLeast_cells_antitone (by decide : 2 ≤ 3) hQ, hwQ⟩))
      (Sum.elim B A) (by
        rintro (aj | j)
        · exact hB aj
        · exact hA j) hU hne
  refine ⟨z, hzU, fun j => hz (.inr j), havoid, fun a J hJ hne => ?_⟩
  exact (htrans (a, ⟨J, hJ⟩) z (hz (.inl (a, ⟨J, hJ⟩)))).resolve_left
    (not_disjoint_iff_nonempty_inter.mpr hne)

end Mei.FinitePolyhedralComplex
