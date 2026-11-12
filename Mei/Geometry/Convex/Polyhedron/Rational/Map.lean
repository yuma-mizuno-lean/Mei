/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Rational.Map
public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Toric.Algebraic.IntegralAffine

/-!
# Inverse transport of rational polyhedra

Transport along an integral affine equivalence and then its inverse recovers
the original carrier.
-/

public section

open TauCeti (RationalAffinePolyhedron)

namespace TauCeti.RationalAffinePolyhedron

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : Toric.IsIntegralLattice i} {h' : Toric.IsIntegralLattice i'}

/-- Transporting a carrier and then transporting it back recovers it. -/
theorem carrier_image_symm (P : RationalAffinePolyhedron h)
    (e : TauCeti.Toric.IntegralAffineEquiv h h') :
    ((P.image e).image e.symm).carrier = P.carrier := by
  rw [carrier_image, carrier_image, Set.image_image]
  simp

end TauCeti.RationalAffinePolyhedron
