/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Cone
public import Mei.Geometry.Convex.Polyhedron.Rational

/-!
# Zero-offset presentations of rational-normal polyhedral cones

A cone given by rational-normal affine inequalities admits a presentation by
integral characters with zero offsets.
-/

public section

namespace TauCeti.IsRationalNormalPolyhedron

open Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : IsIntegralLattice i} {C : PointedCone ℝ V}

/-- A rational-normal polyhedral cone has a presentation with zero offsets. -/
theorem exists_presentation_map_zero (hC : IsRationalNormalPolyhedron h (C : Set V)) :
    ∃ P : RationalAffinePolyhedron h, P.carrier = C ∧ ∀ j, P.inequality j 0 = 0 :=
  hC.isLatticeRational.exists_rationalAffinePolyhedron_offset_zero h

end TauCeti.IsRationalNormalPolyhedron
