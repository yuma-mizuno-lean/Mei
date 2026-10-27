/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Facet

/-!
# The signed facet sum of a polyhedral cell

`OrientedCell.cellCoboundary` sends a coefficient to the finite sum of all signed boundary
facets of a cell. The signs are those of `OrientedCell.boundaryFacet`: contraction by an
outward tangent vector gives the negative parent orientation. Thus every geometric facet
appears once, independently of the inequalities used to present the polyhedron. Unbounded
cells and lineality are allowed.

The construction is linear in coefficients, changes sign under orientation reversal, and
commutes with coefficient maps. `PolyhedralCochain.coboundaryOfFinsupp` applies this formula
to finite presentations, and `PolyhedralCochain.coboundaryPresentation` records the same
signed facet sum as a finite presentation, so that it can be fed back into the formula.
This is the generator formula only: descent through subdivision relations requires
additional geometric cancellation results. In particular, no coboundary on the quotient of
source presentations is defined here.

The finite assembly uses `TauCeti.IsConvexPolyhedron.finite_exposed_sets`,
`OrientedCell.boundaryFacet` and its reversal law, and Mathlib's `Finsupp.lsum`.
-/

public section

noncomputable section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E E' : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] {k : ℕ}

namespace OrientedCell

/-- The signed facet sum of a cell, linear in its coefficient. This gives the generator
formula for the polyhedral coboundary, with values in codimension one higher. -/
def cellCoboundary (σ : OrientedCell h k) : E →ₗ[R] PolyhedralCochain R h E (k + 1) :=
  ∑ τ ∈ σ.boundaryFacets, PolyhedralCochain.mk τ

/-- Evaluate a cell's coboundary by summing its signed facets, each with the same coefficient. -/
theorem cellCoboundary_apply (σ : OrientedCell h k) (c : E) :
    σ.cellCoboundary (R := R) c = ∑ τ ∈ σ.boundaryFacets, PolyhedralCochain.mk τ c := by
  simp only [cellCoboundary, LinearMap.sum_apply]

/-- Orientation reversal negates the entire signed facet sum. -/
@[simp]
theorem cellCoboundary_reverse (σ : OrientedCell h k) :
    σ.reverse.cellCoboundary (R := R) (E := E) = -σ.cellCoboundary := by
  classical
  ext c
  rw [LinearMap.neg_apply, cellCoboundary_apply, boundaryFacets_reverse,
    Finset.sum_image (fun _ _ _ _ heq => reverse_involutive.injective heq)]
  simp only [PolyhedralCochain.mk_reverse, Finset.sum_neg_distrib, cellCoboundary_apply]

/-- Changing coefficients commutes with the signed facet sum. -/
@[simp]
theorem map_cellCoboundary (f : E →ₗ[R] E') (σ : OrientedCell h k) (c : E) :
    PolyhedralCochain.map f (σ.cellCoboundary c) = σ.cellCoboundary (f c) := by
  simp only [cellCoboundary_apply, map_sum, PolyhedralCochain.map_mk]

/-- There are no facets beyond top codimension, so a point cell has zero coboundary. -/
@[simp]
theorem cellCoboundary_eq_zero_of_finrank_eq (σ : OrientedCell h k)
    (hk : k = Module.finrank ℝ V) : σ.cellCoboundary (R := R) (E := E) = 0 := by
  rw [cellCoboundary, σ.boundaryFacets_eq_empty_of_finrank_eq hk, Finset.sum_empty]

end OrientedCell

namespace PolyhedralCochain

/-- Apply the signed facet formula to a finite formal sum of cells. The source retains its
presentation; compatibility with subdivision is needed to descend this map to cochains. -/
def coboundaryOfFinsupp : (OrientedCell h k →₀ E) →ₗ[R] PolyhedralCochain R h E (k + 1) :=
  Finsupp.lsum ℕ OrientedCell.cellCoboundary

/-- The finite-presentation map has the specified signed facet sum on generators. -/
@[simp]
theorem coboundaryOfFinsupp_single (σ : OrientedCell h k) (c : E) :
    coboundaryOfFinsupp (R := R) (Finsupp.single σ c) = σ.cellCoboundary c :=
  Finsupp.lsum_single (S := ℕ) OrientedCell.cellCoboundary σ c

/-- Coefficient maps commute with the coboundary on arbitrary finite presentations. -/
@[simp]
theorem map_coboundaryOfFinsupp (f : E →ₗ[R] E') (x : OrientedCell h k →₀ E) :
    map f (coboundaryOfFinsupp x) =
      coboundaryOfFinsupp (Finsupp.mapRange.linearMap f x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ c => simp

/-- The signed facet sum of a finite presentation, retained as a finite presentation of
codimension one higher. Every cell is replaced by its signed boundary facets, each carrying
the cell's coefficient; repeated facets of different cells are added. -/
def coboundaryPresentation :
    (OrientedCell h k →₀ E) →ₗ[R] (OrientedCell h (k + 1) →₀ E) :=
  Finsupp.lsum ℕ fun σ => ∑ τ ∈ σ.boundaryFacets, Finsupp.lsingle τ

/-- A generator is sent to the formal sum of its signed boundary facets. -/
theorem coboundaryPresentation_single (σ : OrientedCell h k) (c : E) :
    coboundaryPresentation (R := R) (Finsupp.single σ c) =
      ∑ τ ∈ σ.boundaryFacets, Finsupp.single τ c := by
  simp only [coboundaryPresentation, Finsupp.lsum_single, LinearMap.sum_apply,
    Finsupp.lsingle_apply]

open Classical in
/-- Every cell with nonzero coefficient in a signed boundary presentation is
an actual boundary facet of a cell with nonzero source coefficient. -/
theorem support_coboundaryPresentation_subset (f : OrientedCell h k →₀ E) :
    (coboundaryPresentation (R := R) f).support ⊆
      f.support.biUnion OrientedCell.boundaryFacets := by
  classical
  intro τ hτ
  rw [← Finsupp.sum_single f] at hτ
  simp only [Finsupp.sum, map_sum, coboundaryPresentation_single] at hτ
  obtain ⟨σ, hσ, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
  obtain ⟨υ, hυ, hτ⟩ := Finsupp.mem_support_finsetSum τ hτ
  obtain ⟨rfl, _⟩ := (Finsupp.mem_support_single _ _ _).mp hτ
  exact Finset.mem_biUnion.mpr ⟨σ, hσ, hυ⟩

/-- The presentation-level signed facet sum represents the coboundary of the source
presentation. -/
@[simp]
theorem ofFinsupp_coboundaryPresentation (x : OrientedCell h k →₀ E) :
    ofFinsupp (R := R) (coboundaryPresentation (R := R) x) = coboundaryOfFinsupp x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single σ c => simp [coboundaryPresentation_single, OrientedCell.cellCoboundary_apply]

/-- Additive coefficient maps commute with the presentation-level signed facet sum. -/
@[simp]
theorem mapRange_coboundaryPresentation {F : Type*} [FunLike F E E'] [AddMonoidHomClass F E E']
    (f : F) (x : OrientedCell h k →₀ E) :
    Finsupp.mapRange f (map_zero f) (coboundaryPresentation (R := R) x) =
      coboundaryPresentation (R := R) (Finsupp.mapRange f (map_zero f) x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.mapRange_add (map_add f), hx, hy]
  | single σ c => simp [coboundaryPresentation_single, Finsupp.mapRange_finsetSum f]

end PolyhedralCochain

end Mei
