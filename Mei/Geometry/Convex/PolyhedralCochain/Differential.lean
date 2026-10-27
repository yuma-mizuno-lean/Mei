/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Refinement
public import Mei.Geometry.Convex.PolyhedralCochain.SquareZero

/-!
# The coboundary of polyhedral cochains

The signed facet formula descends to a linear coboundary on polyhedral cochains,
independent of the chosen finite presentation. It squares to zero and commutes
with coefficient maps. Thus the coboundary of any cochain is closed, even when
its presentation overlaps or is changed by subdivision.

The descent uses `PolyhedralCochain.lift` and
`OrientedCell.cellCoboundary_eq_sum_of_isOrientedSubdivision`. Square-zero is
`OrientedCell.sum_cellCoboundary_boundaryFacets_eq_zero`, which pairs the two
oppositely oriented incidences at each ridge. No division by two is used, so
coefficients may have torsion. Real offsets, unbounded cells and lineality are
allowed; the coefficient ring may be noncommutative.
-/

public section

noncomputable section

namespace Mei.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E E' : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E'] {k : ℕ}

/-- The polyhedral coboundary, obtained by taking the signed boundary facets of
any finite presentation. It raises codimension by one. -/
def coboundary : PolyhedralCochain R h E k →ₗ[R] PolyhedralCochain R h E (k + 1) :=
  lift OrientedCell.cellCoboundary OrientedCell.cellCoboundary_reverse
    (fun σ Q hQ => by
      ext c
      simp only [LinearMap.sum_apply]
      exact σ.cellCoboundary_eq_sum_of_isOrientedSubdivision hQ c)

/-- On a generator, the coboundary is its signed facet sum. -/
@[simp]
theorem coboundary_mk (σ : OrientedCell h k) (c : E) :
    coboundary (mk (R := R) σ c) = σ.cellCoboundary c :=
  lift_mk _ _ _ σ c

/-- Compute the coboundary using any finite presentation of the cochain. -/
@[simp]
theorem coboundary_ofFinsupp (f : OrientedCell h k →₀ E) :
    coboundary (ofFinsupp (R := R) f) = coboundaryOfFinsupp f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single σ c => simp

/-- The polyhedral coboundary squares to zero. In particular every coboundary
is closed, independently of its presentation. -/
@[simp]
theorem coboundary_coboundary (x : PolyhedralCochain R h E k) :
    coboundary (coboundary x) = 0 := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | mk σ c =>
    rw [coboundary_mk, OrientedCell.cellCoboundary_apply, map_sum]
    simp only [coboundary_mk]
    exact σ.sum_cellCoboundary_boundaryFacets_eq_zero (R := R) c

/-- Changing coefficients commutes with the polyhedral coboundary. -/
@[simp]
theorem map_coboundary (f : E →ₗ[R] E') (x : PolyhedralCochain R h E k) :
    map f (coboundary x) = coboundary (map f x) := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | mk σ c => simp

end Mei.PolyhedralCochain
