/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Ridge

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
`IsOrientedSubdivision.sum_internal_boundaryFacets_eq_zero`, using Mathlib's
`Finset.sum_involution`. In particular, no cancellation of multiplication by
two is used, so coefficients may have torsion.
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
  let S := σ.boundaryFacets.sigma fun τ => τ.boundaryFacets
  have hS (x : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1 + 1)) :
      x ∈ S ↔ x.1 ∈ σ.boundaryFacets ∧ x.2 ∈ x.1.boundaryFacets := by
    simp only [S, Finset.mem_sigma]
  have hex (x) (hx : x ∈ S) :
      ∃! υ : OrientedCell h (k + 1),
        υ ∈ σ.boundaryFacets ∧ υ ≠ x.1 ∧ x.2.reverse ∈ υ.boundaryFacets :=
    σ.existsUnique_reverse_mem_boundaryFacets ((hS x).mp hx).1 ((hS x).mp hx).2
  let g (x) (hx : x ∈ S) : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1 + 1) :=
    ⟨(hex x hx).choose, x.2.reverse⟩
  have hgmem (x) (hx : x ∈ S) : g x hx ∈ S :=
    (hS _).mpr ⟨(hex x hx).choose_spec.1.1, (hex x hx).choose_spec.1.2.2⟩
  have hgg (x) (hx : x ∈ S) : g (g x hx) (hgmem x hx) = x := by
    have hp := (hex x hx).choose_spec.1
    have hfirst : (hex (g x hx) (hgmem x hx)).choose = x.1 :=
      ((hex (g x hx) (hgmem x hx)).choose_spec.2 x.1
        ⟨((hS x).mp hx).1, Ne.symm hp.2.1, by
          simpa only [g, reverse_reverse] using ((hS x).mp hx).2⟩).symm
    exact Sigma.ext hfirst (heq_of_eq (reverse_reverse x.2))
  rw [Finset.sum_sigma' σ.boundaryFacets]
  refine Finset.sum_involution g ?_ ?_ hgmem hgg
  · intro x hx
    simp only [g, hf, add_neg_cancel]
  · intro x hx _ he
    exact (hex x hx).choose_spec.1.2.1 (congrArg Sigma.fst he)

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
