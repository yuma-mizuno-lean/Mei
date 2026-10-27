/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Ridge

/-!
# The signed boundary of a signed boundary

The sum of the coboundaries of all signed boundary facets of an oriented
polyhedral cell is zero. Each ridge occurs twice, through distinct parent
facets, with opposite induced conormal orientations. Counting parent-ridge
incidences retains both occurrences even when their geometric supports agree.
This is the square-zero calculation on generators; it does not require a
coboundary descended through subdivision relations.

The geometric input is `OrientedCell.existsUnique_reverse_mem_boundaryFacets`,
which combines the second-facet construction with uniqueness and the opposite
ridge-orientation theorem. The finite assembly uses
`PolyhedralCochain.sum_mk_eq_zero_of_existsUnique_reverse`, shared with
`OrientedCell.IsOrientedSubdivision.sum_internal_boundaryFacets_eq_zero`.
This pairing was extracted from the latter's finite-incidence argument and uses
Mathlib's `Finset.sum_involution` and `PolyhedralCochain.mk_reverse`.
The result allows arbitrary codimension, unbounded cells, lineality and
coefficients in modules over arbitrary associative rings.
-/

public section

noncomputable section

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

open Classical in
/-- The iterated signed facet sum vanishes: every ridge contribution cancels
with its occurrence through the unique other incident facet. No subdivision
or cancellation hypothesis is required. -/
@[simp]
theorem sum_cellCoboundary_boundaryFacets (σ : OrientedCell h k) (c : E) :
    (∑ τ ∈ σ.boundaryFacets, τ.cellCoboundary (R := R) c) = 0 := by
  classical
  let S := σ.boundaryFacets.sigma fun τ => τ.boundaryFacets
  have hS (x : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1 + 1)) :
      x ∈ S ↔ x.1 ∈ σ.boundaryFacets ∧ x.2 ∈ x.1.boundaryFacets := by
    simp only [S, Finset.mem_sigma]
  simp_rw [cellCoboundary_apply]
  rw [Finset.sum_sigma' σ.boundaryFacets]
  apply PolyhedralCochain.sum_mk_eq_zero_of_existsUnique_reverse (S := S)
  intro x hx
  obtain ⟨υ, ⟨hυ, hne, hr⟩, huniq⟩ :=
    σ.existsUnique_reverse_mem_boundaryFacets ((hS x).mp hx).1 ((hS x).mp hx).2
  refine ⟨υ, ⟨hne, (hS _).mpr ⟨hυ, hr⟩⟩, ?_⟩
  rintro η ⟨hηne, hη⟩
  exact huniq η ⟨((hS _).mp hη).1, hηne, ((hS _).mp hη).2⟩

end Mei.OrientedCell
