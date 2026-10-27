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
modules with `2`-torsion. The involution argument is
`PolyhedralCochain.sum_mk_eq_zero_of_existsUnique_reverse`, factored out of
`OrientedCell.IsOrientedSubdivision.sum_internal_boundaryFacets_eq_zero`.

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
  simp_rw [cellCoboundary_apply]
  rw [Finset.sum_sigma' σ.boundaryFacets]
  refine PolyhedralCochain.sum_mk_eq_zero_of_existsUnique_reverse (fun x hx => ?_) c
  obtain ⟨hτ, hr⟩ := Finset.mem_sigma.mp hx
  obtain ⟨υ, ⟨hυ, hne, hrυ⟩, huniq⟩ := σ.existsUnique_reverse_mem_boundaryFacets hτ hr
  exact ⟨υ, ⟨Finset.mem_sigma.mpr ⟨hυ, hrυ⟩, hne⟩, fun η ⟨hη, hηne⟩ =>
    huniq η ⟨(Finset.mem_sigma.mp hη).1, hηne, (Finset.mem_sigma.mp hη).2⟩⟩

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
  | single σ c => simp [coboundaryPresentation_single]

end PolyhedralCochain

end Mei
