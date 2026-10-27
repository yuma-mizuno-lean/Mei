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
ridge-orientation theorem. The finite assembly uses Mathlib's
`Finset.sum_involution` and the relation `PolyhedralCochain.mk_reverse`.
The incidence pairing follows the finite-sum argument of
`OrientedCell.IsOrientedSubdivision.sum_internal_boundaryFacets_eq_zero`.
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
  have hex (x) (hx : x ∈ S) :
      ∃! υ : OrientedCell h (k + 1),
        υ ∈ σ.boundaryFacets ∧ υ ≠ x.1 ∧ x.2.reverse ∈ υ.boundaryFacets :=
    σ.existsUnique_reverse_mem_boundaryFacets ((hS x).mp hx).1 ((hS x).mp hx).2
  -- Pair a parent-ridge incidence with the reversed ridge in its other parent.
  let g (x) (hx : x ∈ S) : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1 + 1) :=
    ⟨(hex x hx).choose, x.2.reverse⟩
  have hgmem (x) (hx : x ∈ S) : g x hx ∈ S := by
    obtain ⟨hυ, _, hr⟩ := (hex x hx).choose_spec.1
    exact (hS _).mpr ⟨hυ, hr⟩
  have hgg (x) (hx : x ∈ S) : g (g x hx) (hgmem x hx) = x := by
    have hp := (hex x hx).choose_spec.1
    have hfirst : (hex (g x hx) (hgmem x hx)).choose = x.1 :=
      ((hex (g x hx) (hgmem x hx)).choose_spec.2 x.1
        ⟨((hS x).mp hx).1, Ne.symm hp.2.1, by
          simpa only [g, reverse_reverse] using ((hS x).mp hx).2⟩).symm
    exact Sigma.ext hfirst (heq_of_eq (reverse_reverse x.2))
  simp_rw [cellCoboundary_apply]
  rw [Finset.sum_sigma' σ.boundaryFacets]
  refine Finset.sum_involution g ?_ ?_ hgmem hgg
  · intro x hx
    simp only [g, PolyhedralCochain.mk_reverse, add_neg_cancel]
  · intro x hx _ he
    exact (hex x hx).choose_spec.1.2.1 (congrArg Sigma.fst he)

end Mei.OrientedCell
