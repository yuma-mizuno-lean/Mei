/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import TauCeti.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Cone
import Mei.Algebra.BigOperators.Group.Finset.Involution

/-!
# Closure, reversal, and cancellation of polyhedral cochains

The carrier of an oriented cell is closed. Reversal is an involution, and indexed
cochain generators with uniquely paired opposite orientations cancel.
-/

public section

open TauCeti (OrientedCell PolyhedralCochain isRationalNormalPolyhedron_iff)

namespace TauCeti

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i} {k : ℕ}

namespace OrientedCell

/-- The support of a cell is closed. -/
theorem isClosed_carrier (σ : OrientedCell h k) : IsClosed σ.carrier := by
  obtain ⟨P, hP⟩ := isRationalNormalPolyhedron_iff.mp σ.rational
  exact hP ▸ P.isClosed

/-- Reversal is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse : OrientedCell h k → OrientedCell h k) :=
  reverse_reverse

namespace IsOrientedSubdivision

/-- A cell is an oriented subdivision of itself. -/
theorem singleton (σ : OrientedCell h k) : IsOrientedSubdivision σ {σ} where
  biUnion_carrier := by simp
  pairwiseDisjoint := by simp
  orientation_eq := by simp

end IsOrientedSubdivision

end OrientedCell

namespace PolyhedralCochain

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- Indexed generators cancel when every occurrence `(j, σ)` is matched with a unique
occurrence `(j', σ.reverse)` with `j' ≠ j`. The matching is a fixed-point-free involution
(`Finset.sum_involution`), so no division by `2` is needed. -/
theorem sum_mk_eq_zero_of_existsUnique_reverse {ι : Type*}
    {S : Finset (Σ _ : ι, OrientedCell h k)}
    (hS : ∀ x ∈ S, ∃! j : ι, ⟨j, x.2.reverse⟩ ∈ S ∧ j ≠ x.1) (c : E) :
    ∑ x ∈ S, mk (R := R) x.2 c = 0 := by
  exact S.sum_eq_zero_of_unique_partner OrientedCell.reverse
    OrientedCell.reverse_reverse hS (fun σ => mk (R := R) σ c)
    (fun σ => by rw [mk_reverse, add_neg_cancel])

end PolyhedralCochain

end TauCeti
