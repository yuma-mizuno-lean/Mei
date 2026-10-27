/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Ridge
public import Mei.Algebra.BigOperators.Group.Finset.Involution

/-!
# The signed boundary of a cell's signed boundary vanishes

Every ridge occurrence in the boundary of a boundary facet has a unique
oppositely oriented occurrence through the other incident facet. Pairing these
occurrences proves that the iterated signed facet sum is zero. Parent indices
are retained throughout, so coincident ridge supports have their actual
incidence multiplicities. Unbounded cells and lineality are allowed.

`OrientedCell.sum_boundaryFacets_boundaryFacets_eq_zero` works for any
abelian-group-valued function negated by orientation reversal.
`OrientedCell.sum_cellCoboundary_boundaryFacets_eq_zero` applies it to the
cochain generators. This is the square-zero identity on cells; descending
the coboundary through subdivision remains a separate requirement.

The geometric inputs are `OrientedCell.exists_reverse_mem_boundaryFacets`
and `OrientedCell.eq_of_ridge_subset_of_ne`. The incidence pairing follows
the same finite-sum construction as
`IsOrientedSubdivision.sum_internal_boundaryFacets_eq_zero`. Both use
`Finset.sum_sum_eq_zero_of_unique_partner`, extracted from that construction
using Mathlib's `Finset.sum_involution`. In particular, no cancellation of
multiplication by two is used, so coefficients may have torsion.
-/

public section

noncomputable section

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

open Classical in
/-- The iterated signed facet sum vanishes for every abelian-group-valued
function that changes sign under orientation reversal. -/
theorem sum_boundaryFacets_boundaryFacets_eq_zero (σ : OrientedCell h k)
    {A : Type*} [AddCommGroup A] (f : OrientedCell h (k + 1 + 1) → A)
    (hf : ∀ r, f r.reverse = -f r) :
    (∑ τ ∈ σ.boundaryFacets, ∑ r ∈ τ.boundaryFacets, f r) = 0 := by
  classical
  exact σ.boundaryFacets.sum_sum_eq_zero_of_unique_partner
    (fun τ => τ.boundaryFacets) reverse reverse_reverse
    (fun _ hτ _ hr => σ.existsUnique_reverse_mem_boundaryFacets hτ hr)
    f (fun r => by rw [hf, add_neg_cancel])

/-- The signed coboundaries of all signed boundary facets sum to zero.
This is the square-zero identity for the generator formula, with arbitrary
module coefficients. -/
@[simp]
theorem sum_cellCoboundary_boundaryFacets_eq_zero (σ : OrientedCell h k)
    {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] (c : E) :
    (∑ τ ∈ σ.boundaryFacets, τ.cellCoboundary (R := R) c) = 0 := by
  simp only [cellCoboundary_apply]
  exact σ.sum_boundaryFacets_boundaryFacets_eq_zero
    (fun r => PolyhedralCochain.mk r c) (fun r => PolyhedralCochain.mk_reverse r c)

end Mei.OrientedCell
