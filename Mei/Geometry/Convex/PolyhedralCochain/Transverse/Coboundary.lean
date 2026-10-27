/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Transverse.Basic

/-!
# Transverse signed boundaries

The signed boundary of a transverse cell, and the signed boundary of a finite
presentation by transverse cells, are transverse cochains. This follows because
each boundary facet has direction contained in that of its parent cell.
-/

public section

noncomputable section

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- The signed facet sum of a transverse cell is a transverse cochain. -/
theorem cellCoboundary_mem_transverseSubmodule (σ : OrientedCell h k) (v : V)
    (hv : v ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    σ.cellCoboundary (R := R) c ∈ PolyhedralCochain.transverseSubmodule v := by
  rw [cellCoboundary_apply]
  exact Submodule.sum_mem _ fun τ hτ => PolyhedralCochain.mk_mem_transverseSubmodule v τ
    (σ.notMem_direction_of_mem_boundaryFacets hτ hv) c

end Mei.OrientedCell

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

/-- The signed facet sum of a finite transverse presentation is transverse.
The transversality condition is imposed only on cells with nonzero coefficient. -/
theorem coboundaryOfFinsupp_mem_transverseSubmodule (v : V)
    (f : OrientedCell h k →₀ E)
    (hf : ∀ σ ∈ f.support, v ∉ (affineSpan ℝ σ.carrier).direction) :
    coboundaryOfFinsupp (R := R) f ∈ transverseSubmodule v := by
  classical
  rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, coboundaryOfFinsupp_single]
  exact Submodule.sum_mem _ fun σ hσ =>
    σ.cellCoboundary_mem_transverseSubmodule v (hf σ hσ) (f σ)

end Mei.PolyhedralCochain
