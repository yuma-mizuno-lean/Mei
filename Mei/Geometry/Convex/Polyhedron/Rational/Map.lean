/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational
public import Mei.Geometry.Toric.Algebraic.IntegralAffine

/-!
# Integral affine transport of rational-normal polyhedra

Integral affine equivalences preserve rational normals. Their translation vectors
may be arbitrary, so this result concerns rational-normal polyhedra with real
offsets; it does not assert preservation of rational offsets.
-/

public section

namespace Mei

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

namespace RationalAffinePolyhedron

/-- Transport a rational-normal presentation by pulling back along the inverse
integral affine equivalence. -/
def image (P : RationalAffinePolyhedron h) (e : Toric.IntegralAffineEquiv h h') :
    RationalAffinePolyhedron h' :=
  P.preimage e.symm.toContinuousAffineMap e.symm.isRational_toContinuousAffineMap

/-- The transported presentation has the exact image of the original carrier. -/
@[simp]
theorem carrier_image (P : RationalAffinePolyhedron h) (e : Toric.IntegralAffineEquiv h h') :
    (P.image e).carrier = e '' P.carrier := by
  rw [image, carrier_preimage]
  ext y
  simp only [Set.mem_preimage, Toric.IntegralAffineEquiv.toContinuousAffineMap_apply]
  constructor
  · intro hy
    exact ⟨e.symm y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- Transporting a carrier and then transporting it back recovers it. -/
theorem carrier_image_symm (P : RationalAffinePolyhedron h)
    (e : Toric.IntegralAffineEquiv h h') :
    ((P.image e).image e.symm).carrier = P.carrier := by
  rw [carrier_image, carrier_image, Set.image_image]
  simp

end RationalAffinePolyhedron

/-- Rational-normal polyhedrality is invariant under integral affine transport. -/
theorem IsRationalNormalPolyhedron.image {P : Set V}
    (hP : IsRationalNormalPolyhedron h P) (e : Toric.IntegralAffineEquiv h h') :
    IsRationalNormalPolyhedron h' (e '' P) := by
  rw [isRationalNormalPolyhedron_iff] at hP ⊢
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨Q.image e, Q.carrier_image e⟩

end Mei
