/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.ContinuousMap.Subdivision
public import Mei.Geometry.Convex.PolyhedralComplex.RegularTransport
public import Mei.Geometry.Convex.PolyhedralComplex.Slice

/-!
# Filling grids with regular and isolated joint patches

A continuous square filling in an affine slice, transverse to the joints it
meets and missing the higher skeleton, admits a finite grid subordinate to
regular and isolating joint balls. In a regular ball crossing words depend only
on endpoints. In a joint ball the slice meets the codimension-two skeleton only
at its center, and all cells encountered contain the center's supporting joint.

Each original parameter patch and the convex hull of its four perturbed vertex
images lie in the same ball. The uniform positive perturbation margin permits
later choices of admissible mesh edges while preserving these local alternatives.
The theorem constructs the subdivision control; it does not identify joint
boundary words with meridians or impose admissibility on the mesh edges.

This combines `ContinuousMap.exists_grid_subdivision_convexHull`,
`FinitePolyhedralComplex.exists_ball_crossingWord_eq`, and
`FinitePolyhedralComplex.exists_ball_inter_slice_support_eq_singleton`.
-/

public section

open Set Mei.Convex
open scoped unitInterval

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- A joint-transverse filling missing the higher skeleton has a finite grid
of regular or isolating joint patches, stable under uniformly small perturbations
of all vertex images. The original patches remain covered as well. Fillings may
be noninjective or degenerate; only joints actually met require transversality. -/
theorem exists_subordinate_filling_grid (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (A : AffineSubspace ℝ V) (f : C(↥unitInterval × ↥unitInterval, V))
    (hA : range f ⊆ A)
    (hnext : Disjoint (range f) (C.codimensionAtLeast 3).support)
    (htrans : ∀ J ∈ C.joints, (range f ∩ J).Nonempty →
        Disjoint A.direction (affineSpan ℝ J).direction) :
    ∃ (n : ℕ) (t : ℕ → unitInterval), 0 < n ∧ t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      ∃ ε > 0, ∀ a b : Fin n,
      ∃ θ ∈ range f, ∃ r > 0,
        MapsTo f (Icc (t a) (t (a + 1)) ×ˢ Icc (t b) (t (b + 1))) (Metric.ball θ r) ∧
        (∀ v : Fin 2 × Fin 2 → V,
          (∀ e, dist (v e)
            (f (t (a + e.1.val), t (b + e.2.val))) < ε) →
          convexHull ℝ (range v) ⊆ Metric.ball θ r) ∧
        ((∀ (x y : WallComplement (fun P : C.walls => (P : Set V)))
            (p q : AdmissiblePLPath x y),
            (∀ z ∈ p.vertices, z.val ∈ Metric.ball θ r) →
            (∀ z ∈ q.vertices, z.val ∈ Metric.ball θ r) →
              p.crossingWord ν = q.crossingWord ν) ∨
          ∃ J ∈ C.joints, θ ∈ intrinsicInterior ℝ J ∧
            Metric.ball θ r ∩ ((A : Set V) ∩ (C.codimensionAtLeast 2).support) = {θ} ∧
            ∀ Q ∈ C.cells, (Metric.ball θ r ∩ Q).Nonempty → J ⊆ Q) := by
  classical
  let S := range f
  -- At every image point choose one of the two local geometric models.
  have hlocal (θ : S) : ∃ r > 0,
      (∀ (x y : WallComplement (fun P : C.walls => (P : Set V)))
        (p q : AdmissiblePLPath x y),
        (∀ z ∈ p.vertices, z.val ∈ Metric.ball θ.val r) →
        (∀ z ∈ q.vertices, z.val ∈ Metric.ball θ.val r) →
          p.crossingWord ν = q.crossingWord ν) ∨
      ∃ J ∈ C.joints, θ.val ∈ intrinsicInterior ℝ J ∧
        Metric.ball θ.val r ∩ ((A : Set V) ∩ (C.codimensionAtLeast 2).support) = {θ.val} ∧
        ∀ Q ∈ C.cells, (Metric.ball θ.val r ∩ Q).Nonempty → J ⊆ Q := by
    by_cases hθ : θ.val ∈ (C.codimensionAtLeast 2).support
    · obtain ⟨J, hJ, _⟩ := C.existsUnique_mem_cellsOfCodimension_of_notMem_succ hθ
        (hnext.notMem_of_mem_left θ.property)
      obtain ⟨r, hr, heq, hinc⟩ := C.exists_ball_inter_slice_support_eq_singleton A
        hJ.1 hJ.2 (hA θ.property)
        (htrans J hJ.1 ⟨θ.val, θ.property, intrinsicInterior_subset hJ.2⟩)
      exact ⟨r, hr, Or.inr ⟨J, hJ.1, hJ.2, heq, hinc⟩⟩
    · obtain ⟨r, hr, hword⟩ := C.exists_ball_crossingWord_eq ν hν
        (fun hs => hθ (C.singularSupport_walls_subset_support_codimensionAtLeast hs))
      exact ⟨r, hr, Or.inl hword⟩
  choose r hr hmodel using hlocal
  -- A Lebesgue number selects one model per grid cell, with room to perturb.
  obtain ⟨n, t, hn, ht0, hmono, ht1, -, ε, hε, hgrid⟩ :=
    f.exists_grid_subdivision_convexHull
    (fun θ : S => Metric.ball θ.val (r θ)) (fun _ => Metric.isOpen_ball)
    (fun x => ⟨⟨f x, mem_range_self x⟩, Metric.mem_ball_self (hr ⟨f x, mem_range_self x⟩)⟩)
      ∅ countable_empty (notMem_empty _) (notMem_empty _)
  refine ⟨n, t, hn, ht0, hmono, ht1, ε, hε, fun a b => ?_⟩
  obtain ⟨θ, hpatch, hperturb⟩ := hgrid a b
  exact ⟨θ.val, θ.property, r θ, hr θ, hpatch, hperturb, hmodel θ⟩

end Mei.FinitePolyhedralComplex
