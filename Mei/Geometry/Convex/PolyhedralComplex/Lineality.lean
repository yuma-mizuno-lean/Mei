/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.Basic
public import Mei.Geometry.Convex.Homogenization.Face

/-!
# Lineality of meeting cells

Cells of a finite polyhedral complex which meet have the same lineality
space. Here the lineality space of a cell is the largest vector subspace of
its recession cone, using Mathlib's `PointedCone.lineal`. The common face
inherits the lineality of each cell, so unbounded cells with nonzero
lineality are included.
-/

public section

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Meeting cells have the same lineality space. No salience, boundedness,
or finite-dimensionality assumption is required. -/
theorem lineal_recessionCone_eq_of_inter_nonempty (C : FinitePolyhedralComplex h)
    {P Q : Set V} (hP : P ∈ C.cells) (hQ : Q ∈ C.cells)
    (hne : (P ∩ Q).Nonempty) :
    (Set.recessionCone P).lineal = (Set.recessionCone Q).lineal := by
  have hpolyP := C.isConvexPolyhedron hP
  have hpolyQ := C.isConvexPolyhedron hQ
  have hfaceP := C.inter_face P hP Q hQ hne
  have hneQP : (Q ∩ P).Nonempty := by simpa only [Set.inter_comm] using hne
  have hfaceQ := C.inter_face Q hQ P hP hneQP
  exact (hfaceP.lineal_recessionCone_eq hpolyP.convex hpolyP.isClosed hne).symm.trans
    (by simpa only [Set.inter_comm] using
      hfaceQ.lineal_recessionCone_eq hpolyQ.convex hpolyQ.isClosed hneQP)

end Mei.FinitePolyhedralComplex
