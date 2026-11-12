/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Face
public import Mei.Geometry.Convex.Polyhedron.Rational

/-!
# Offsets and exposedness of active rational presentations

Adding the negatives of active constraints preserves rational offsets and
gives an exposed face of the original carrier.
-/

public section

open TauCeti (RationalAffinePolyhedron)

namespace TauCeti.RationalAffinePolyhedron

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- Active constraints preserve rational affine offsets because added rows are
negatives of existing rows. -/
theorem HasRationalOffsets.activeFace {P : RationalAffinePolyhedron h}
    (hP : P.HasRationalOffsets) (I : Finset (Fin P.numConstraints)) :
    (P.activeFace I).HasRationalOffsets :=
  (hasRationalOffsets_activeFace_iff I).mpr hP

/-- An active presentation is an exposed subset of the original carrier. The
empty subset is included according to Mathlib's exposed-set convention. -/
theorem isExposed_activeFace (P : RationalAffinePolyhedron h)
    (I : Finset (Fin P.numConstraints)) :
    IsExposed ℝ P.carrier (P.activeFace I).carrier := by
  have hcarrier : P.carrier = {x : V | ∀ j, P.inequality j x ≤ 0} :=
    Set.ext fun _ => mem_carrier
  rw [carrier_activeFace, hcarrier]
  exact TauCeti.isExposed_setOf_active P.inequality I

end TauCeti.RationalAffinePolyhedron
