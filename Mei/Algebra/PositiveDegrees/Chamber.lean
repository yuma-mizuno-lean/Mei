/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.Geometry.Convex.Cone.Chamber
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Distinguished points of positive-degree chambers

An integral lattice identifies an integral degree functional with a point of its real
dual. Strict positivity of the degree puts this point in the positive chamber and its
negative in the negative chamber. Thus both chambers are nonempty and, under finite
generation, contain open neighborhoods of these distinguished points. These points avoid
every hyperplane indexed by a nonzero allowed degree, simultaneously at every cutoff.

The distinguished point is the continuous form of
`TauCeti.Toric.IsIntegralLattice.realCharacter`. Finite dimensionality is supplied by the
lattice itself.
-/

public section

namespace Mei.PositiveDegrees

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} (d : PositiveDegrees N) (h : TauCeti.Toric.IsIntegralLattice i)

/-- The real dual point determined by the integral degree functional. -/
noncomputable def degreePoint : V →L[ℝ] ℝ :=
  haveI := h.finiteDimensional
  (h.realCharacter d.degree).toContinuousLinearMap

/-- The degree point evaluates on lattice vectors as the original degree. -/
@[simp]
theorem degreePoint_apply (n : N) : d.degreePoint h (i n) = (d.degree n : ℝ) := by
  simp [degreePoint]

/-- The positive degree functional lies in the positive chamber. -/
theorem degreePoint_mem_positiveChamber : d.degreePoint h ∈ d.monoid.positiveChamber i := by
  rw [AddSubmonoid.mem_positiveChamber]
  intro n hn hn0
  simpa using (Int.cast_pos.mpr (d.degree_pos hn hn0) : (0 : ℝ) < d.degree n)

/-- The negative degree functional lies in the negative chamber. -/
theorem neg_degreePoint_mem_negativeChamber :
    -d.degreePoint h ∈ d.monoid.negativeChamber i := by
  simpa using d.degreePoint_mem_positiveChamber h

include h in
/-- The positive chamber is nonempty, whether or not the monoid is finitely generated. -/
theorem positiveChamber_nonempty : (d.monoid.positiveChamber i).Nonempty :=
  ⟨d.degreePoint h, d.degreePoint_mem_positiveChamber h⟩

include h in
/-- The negative chamber is nonempty, whether or not the monoid is finitely generated. -/
theorem negativeChamber_nonempty : (d.monoid.negativeChamber i).Nonempty :=
  ⟨-d.degreePoint h, d.neg_degreePoint_mem_negativeChamber h⟩

end Mei.PositiveDegrees
