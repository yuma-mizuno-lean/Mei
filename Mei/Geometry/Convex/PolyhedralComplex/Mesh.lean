/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Analysis.Convex.SquareMesh
public import Mei.Geometry.Convex.PolyhedralComplex.Slice
public import Mei.Geometry.Convex.PolyhedralComplex.RegularTransport

/-!
# Meshes in regular and isolating joint neighborhoods

A continuous square in an affine slice, transverse to the joints it meets and
avoiding higher strata, admits a finite uniform mesh subordinate to regular
crossing-word neighborhoods and isolating joint neighborhoods. There is a common
positive tolerance for moving all vertex images: the convex hull of the perturbed
images in each cell remains in its assigned neighborhood.

In a regular neighborhood all admissible paths with the same endpoints have
the same crossing word. A joint neighborhood meets the sliced singular skeleton
only at its center, and every cell meeting it contains the supporting joint.
These are the two local regions needed to decompose a filled polygonal loop.
The result supplies geometric containment; it does not identify the boundary
word of a joint region with a chosen meridian.

The construction uses `FinitePolyhedralComplex.exists_ball_crossingWord_eq`,
`FinitePolyhedralComplex.exists_ball_inter_slice_support_eq_singleton`, and
`Mei.exists_square_mesh_convexHull_ball_subset`. Unbounded cells, lineality,
nonembedded fillings and degenerate parameter cells are allowed.
-/

public section

open Set Metric Mei.Convex

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A transverse slice away from higher strata has, at each point, either a
regular crossing-word neighborhood or a neighborhood isolating one joint.
The joint case also controls all cells meeting the ball, not only the slice. -/
theorem exists_ball_crossingWord_eq_or_isolating_joint (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (A : AffineSubspace ℝ V) {x : V} (hxA : x ∈ A)
    (hnext : x ∉ (C.codimensionAtLeast 3).support)
    (htrans : ∀ J ∈ C.joints, x ∈ J →
      Disjoint A.direction (affineSpan ℝ J).direction) :
    ∃ r > 0,
      (∀ (y z : WallComplement (fun P : C.walls => (P : Set V)))
        (p q : AdmissiblePLPath y z),
        (∀ w ∈ p.vertices, w.val ∈ ball x r) →
        (∀ w ∈ q.vertices, w.val ∈ ball x r) → p.crossingWord ν = q.crossingWord ν) ∨
      ∃ J ∈ C.joints, x ∈ intrinsicInterior ℝ J ∧
        ball x r ∩ ((A : Set V) ∩ (C.codimensionAtLeast 2).support) = {x} ∧
        ∀ Q ∈ C.cells, (ball x r ∩ Q).Nonempty → J ⊆ Q := by
  by_cases hx : x ∈ (C.codimensionAtLeast 2).support
  · obtain ⟨J, ⟨hJ, hxJ⟩, _⟩ :=
      C.existsUnique_mem_cellsOfCodimension_of_notMem_succ hx hnext
    obtain ⟨r, hr, hisolate, hincident⟩ := C.exists_ball_inter_slice_support_eq_singleton
      A hJ hxJ hxA (htrans J hJ (intrinsicInterior_subset hxJ))
    exact ⟨r, hr, Or.inr ⟨J, hJ, hxJ, hisolate, hincident⟩⟩
  · obtain ⟨r, hr, hword⟩ := C.exists_ball_crossingWord_eq ν hν
      (fun hs => hx (C.singularSupport_walls_subset_support_codimensionAtLeast hs))
    exact ⟨r, hr, Or.inl hword⟩

/-- Subdivide a continuous square into finitely many uniform cells contained
in regular or isolating joint balls. The same positive tolerance works for
perturbing all image points and for convex interpolation within every cell.
Transversality is required only at joints actually met by the filling. -/
theorem exists_square_mesh_regular_or_isolating_joint (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (H : ℝ × ℝ → V)
    (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (A : AffineSubspace ℝ V)
    (hA : H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ⊆ A)
    (hnext : Disjoint (H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
      (C.codimensionAtLeast 3).support)
    (htrans : ∀ J ∈ C.joints,
      (H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ J).Nonempty →
        Disjoint A.direction (affineSpan ℝ J).direction) :
    ∃ n : ℕ, 0 < n ∧ ∃ ε > 0, ∀ a b : Fin n,
      ∃ x ∈ H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1), ∃ r > 0,
        convexHull ℝ (⋃ z ∈
          (Icc ((a : ℝ) / n) (((a : ℝ) + 1) / n) ×ˢ
            Icc ((b : ℝ) / n) (((b : ℝ) + 1) / n)), ball (H z) ε) ⊆ ball x r ∧
        ((∀ (y z : WallComplement (fun P : C.walls => (P : Set V)))
          (p q : AdmissiblePLPath y z),
          (∀ w ∈ p.vertices, w.val ∈ ball x r) →
          (∀ w ∈ q.vertices, w.val ∈ ball x r) → p.crossingWord ν = q.crossingWord ν) ∨
        ∃ J ∈ C.joints, x ∈ intrinsicInterior ℝ J ∧
          ball x r ∩ ((A : Set V) ∩ (C.codimensionAtLeast 2).support) = {x} ∧
          ∀ Q ∈ C.cells, (ball x r ∩ Q).Nonempty → J ⊆ Q) := by
  classical
  let S := H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  choose r hr hlocal using fun x : S =>
    C.exists_ball_crossingWord_eq_or_isolating_joint ν hν A (hA x.property)
      (hnext.notMem_of_mem_left x.property)
      (fun J hJ hxJ => htrans J hJ ⟨x, x.property, hxJ⟩)
  obtain ⟨n, hn, ε, hε, hmesh⟩ := Mei.exists_square_mesh_convexHull_ball_subset H hH
    (fun x : S => ball x.val (r x)) (fun _ => isOpen_ball) (fun x => convex_ball x.val (r x))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  refine ⟨n, hn, ε, hε, fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hmesh a b
  exact ⟨x, x.property, r x, hr x, hx, hlocal x⟩

end Mei.FinitePolyhedralComplex
