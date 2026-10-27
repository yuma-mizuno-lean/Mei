/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.Triangle.Filling
public import Mei.Geometry.Convex.PolyhedralComplex.Strata

/-!
# Cone fillings avoiding the higher skeleton

A family of segments missing the codimension-at-least-three skeleton admits a
common cone vertex whose entire filled triangles still miss that skeleton.
The original segments are fixed. The vertex can lie in any prescribed
nonempty open set and avoid additional proper affine subspaces.

This isolates the higher-codimension avoidance needed when decomposing a
polygonal filling into local wall and joint contributions. Intersections with
joints and transversality of the triangles remain separate geometric conditions.
The construction applies `Mei.exists_mem_open_triangle_fillings_avoid` to the
actual cell supports; it does not require the segments to avoid their affine spans.
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

end Mei.FinitePolyhedralComplex
