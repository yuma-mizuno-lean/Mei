/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Coboundary
public import Mei.Geometry.Convex.PolyhedralCochain.Pairing

/-!
# Pairing of coboundary presentations

Any finite presentation of the coboundary of a single cell `σ` with coefficient `c` pairs with a
test that is transverse to the presentation's cells and to the boundary facets of `σ` exactly as
the signed boundary presentation `coboundaryPresentation (single σ c)` does.
-/

public section

namespace Mei.PolyhedralCochain

open OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}
  {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

open Classical in
/-- A finite presentation `y` of the coboundary of the cell `σ` with coefficient `c` pairs with a
test transverse to its cells and to the boundary facets of `σ` as the signed boundary
presentation does. -/
theorem intersectionPairing_eq_coboundaryPresentation_of_ofFinsupp_eq {σ : OrientedCell h k}
    (c : E) {v : Fin (k + 1 + 1) → V} {y : OrientedCell h (k + 1) →₀ E}
    (hy : ofFinsupp (R := R) y = coboundaryOfFinsupp (Finsupp.single σ c))
    (hσ : ∀ τ ∈ σ.boundaryFacets, τ.IsTransverse v)
    (hT : ∀ τ ∈ y.support, τ.IsTransverse v) :
    intersectionPairing (R := R) v y =
      intersectionPairing (R := R) v (coboundaryPresentation (R := R) (Finsupp.single σ c)) := by
  refine intersectionPairing_eq_of_ofFinsupp_eq
    (by rw [hy, ofFinsupp_coboundaryPresentation]) hT fun τ hτ => ?_
  obtain ⟨σ', hσ', hτσ⟩ := Finset.mem_biUnion.mp
    (support_coboundaryPresentation_subset (R := R) (Finsupp.single σ c) hτ)
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hσ')] at hτσ
  exact hσ τ hτσ

end Mei.PolyhedralCochain
