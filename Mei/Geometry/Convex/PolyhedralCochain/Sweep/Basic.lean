/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralCochain.Basic
public import Mei.Geometry.Convex.Polyhedron.Rational.Sweep
public import Mei.Geometry.Convex.Sweep
public import Mei.Geometry.Convex.Recession
public import Mei.LinearAlgebra.Alternating.Contraction

/-!
# Transverse sweeps of oriented cells

An oriented cell transverse to a lattice vector sweeps to an oriented cell of
one lower codimension. Its orientation is the contraction of the original
conormal orientation, with the sweeping vector inserted first. The swept cell
is strictly outgoing, and reversal of the original orientation reverses the
swept orientation. These are the generator operations for sweeping polyhedral
cochains.

The support and dimension calculations use `Mei.Convex.sweep` and
`Mei.Convex.finrank_sweep`. Rationality uses the Fourier–Motzkin construction
`IsRationalNormalPolyhedron.negRay`; the orientation uses
`Module.Ray.contract`. This file concerns generators; descent through
subdivision relations is a further step.
-/

public section

open Module

noncomputable section

namespace Mei.OrientedCell

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i} {k : ℕ}

/-- Sweep an oriented cell along a transverse lattice vector. Contract its
conormal orientation by the positive sweeping vector, although its support
extends in the negative direction. -/
def sweep (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) : OrientedCell h k := by
  have := h.finiteDimensional
  refine
    { carrier := Convex.sweep σ.carrier (i n)
      rational := σ.rational.sweep n
      nonempty := Convex.sweep_nonempty σ.nonempty (i n)
      finrank_direction_add := ?_
      orientation := σ.orientation.contract σ.isConormal σ.finrank_quotient_direction (i n) hn
      isConormal := ?_ }
  · rw [direction_affineSpan, Convex.finrank_sweep σ.nonempty
      (by simpa [direction_affineSpan] using hn)]
    have := σ.finrank_direction_add
    rw [direction_affineSpan] at this
    omega
  · simpa only [direction_affineSpan, Convex.vectorSpan_sweep σ.nonempty] using
      σ.orientation.isConormal_contract σ.isConormal σ.finrank_quotient_direction (i n) hn

/-- The support of an oriented sweep is the negative-ray sweep of its support. -/
@[simp]
theorem sweep_carrier (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    (σ.sweep n hn).carrier = Convex.sweep σ.carrier (i n) := (rfl)

/-- The orientation of the swept cell is obtained by conormal contraction. -/
@[simp]
theorem sweep_orientation (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    (σ.sweep n hn).orientation =
      σ.orientation.contract σ.isConormal σ.finrank_quotient_direction (i n) hn := (rfl)

/-- The positive sweeping vector is not a recession direction of the swept cell. -/
theorem sweep_strictlyOutgoing (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    i n ∉ Set.recessionCone (σ.sweep n hn).carrier := by
  rw [sweep_carrier, Set.mem_recessionCone]
  exact Convex.sweep_strictlyOutgoing σ.nonempty (by simpa [direction_affineSpan] using hn)

/-- Reversing the input orientation reverses the swept cell. -/
@[simp]
theorem sweep_reverse (σ : OrientedCell h (k + 1)) (n : N)
    (hn : i n ∉ (affineSpan ℝ σ.carrier).direction) :
    σ.reverse.sweep n (by simpa using hn) = (σ.sweep n hn).reverse := by
  ext1
  · simp
  · simp only [sweep_orientation, reverse_orientation, reverse_carrier]
    exact Module.Ray.contract_neg σ.orientation σ.isConormal
      σ.finrank_quotient_direction (i n) hn

end Mei.OrientedCell
