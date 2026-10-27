/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Ridge

/-!
# The square-zero identity for signed facet sums

Applying the signed facet sum twice to an oriented cell gives zero in polyhedral cochains.
Every iterated incidence `(τ, r)`, with `τ` a signed boundary facet of the cell and `r` a
signed boundary facet of `τ`, is matched with the incidence `(υ, r.reverse)` through the
unique other facet `υ` containing the ridge `r`
(`OrientedCell.existsUnique_reverse_mem_boundaryFacets`). The two contributions cancel by
the reversal relation of polyhedral cochains. The matching is a fixed-point-free involution
on iterated incidences, so the cancellation holds for every coefficient module, including
modules with `2`-torsion.

Consequently, the presentation-level signed facet sum
`PolyhedralCochain.coboundaryPresentation` of any finite presentation is a presentation
whose own signed facet sum vanishes. This identity holds for the source presentation itself;
it does not require the coboundary to descend through subdivision relations.

Arbitrary codimension, unbounded cells and lineality are allowed. The finite cancellation
uses Mathlib's `Finset.sum_involution` on iterated incidences.
-/

public section

noncomputable section

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

namespace OrientedCell

/-- The signed facet sums of the signed boundary facets of a cell cancel: the polyhedral
coboundary squares to zero on generators. -/
@[simp]
theorem sum_cellCoboundary_boundaryFacets_eq_zero (σ : OrientedCell h k) (c : E) :
    ∑ τ ∈ σ.boundaryFacets, τ.cellCoboundary (R := R) c = 0 := by
  classical
  let S := σ.boundaryFacets.sigma fun τ : OrientedCell h (k + 1) => τ.boundaryFacets
  have hex (x) (hx : x ∈ S) : ∃! υ : OrientedCell h (k + 1),
      υ ∈ σ.boundaryFacets ∧ υ ≠ x.1 ∧ x.2.reverse ∈ υ.boundaryFacets :=
    σ.existsUnique_reverse_mem_boundaryFacets (Finset.mem_sigma.mp hx).1
      (Finset.mem_sigma.mp hx).2
  -- Send an iterated incidence to the reversed ridge in the other facet containing it.
  let g (x) (hx : x ∈ S) : Σ _ : OrientedCell h (k + 1), OrientedCell h (k + 1 + 1) :=
    ⟨(hex x hx).choose, x.2.reverse⟩
  have hgmem (x) (hx : x ∈ S) : g x hx ∈ S :=
    Finset.mem_sigma.mpr ⟨(hex x hx).choose_spec.1.1, (hex x hx).choose_spec.1.2.2⟩
  have hgg (x) (hx : x ∈ S) : g (g x hx) (hgmem x hx) = x := by
    have hfirst : (hex (g x hx) (hgmem x hx)).choose = x.1 :=
      ((hex (g x hx) (hgmem x hx)).choose_spec.2 x.1
        ⟨(Finset.mem_sigma.mp hx).1, Ne.symm (hex x hx).choose_spec.1.2.1, by
          simpa only [g, reverse_reverse] using (Finset.mem_sigma.mp hx).2⟩).symm
    exact Sigma.ext hfirst (heq_of_eq (reverse_reverse x.2))
  simp_rw [cellCoboundary_apply]
  rw [Finset.sum_sigma' σ.boundaryFacets]
  refine Finset.sum_involution g ?_ ?_ hgmem hgg
  · intro x hx
    simp only [g, PolyhedralCochain.mk_reverse, add_neg_cancel]
  · intro x hx _ he
    exact (hex x hx).choose_spec.1.2.1 (congrArg Sigma.fst he)

end OrientedCell

namespace PolyhedralCochain

/-- The signed facet sum of the presentation-level signed facet sum vanishes: every finite
presentation of a coboundary obtained by `coboundaryPresentation` is closed. -/
@[simp]
theorem coboundaryOfFinsupp_coboundaryPresentation (x : OrientedCell h k →₀ E) :
    coboundaryOfFinsupp (R := R) (coboundaryPresentation (R := R) x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single σ c => simp

end PolyhedralCochain

end Mei
