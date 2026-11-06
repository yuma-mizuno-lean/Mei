/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Cone

/-!
# Rational affine equalizers

The locus where two affine maps with rational linear parts agree is a closed
rational-normal polyhedron. Real offsets and noninjective maps are allowed.
These equalizers impose the matching equation in a pullback of semilinear families.
-/

public section

open Mei

namespace AffineMap

variable {N N' V W : Type*} [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℝ V] [NormedSpace ℝ W]
  {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- The equalizer of rational affine maps is a rational-normal polyhedron,
including when it is empty or either map has a kernel. -/
theorem isRationalNormalPolyhedron_equalizer (f g : V →ᵃ[ℝ] W)
    (hf : Toric.IsRationalLinearMap h h' f.linear)
    (hg : Toric.IsRationalLinearMap h h' g.linear) :
    IsRationalNormalPolyhedron h {x | f x = g x} := by
  have := h.finiteDimensional
  let δ : V →ᴬ[ℝ] W :=
    ⟨f - g, AffineMap.continuous_linear_iff.mp
      (f - g).linear.continuous_of_finiteDimensional⟩
  have hδ : Toric.IsRationalLinearMap h h' δ.toAffineMap.linear := by
    rw [Toric.isRationalLinearMap_iff]
    intro ℓ hℓ
    simpa only [δ, AffineMap.sub_linear, LinearMap.comp_sub] using
      (hf.map_functional hℓ).sub (hg.map_functional hℓ)
  have he : δ ⁻¹' {0} = {x | f x = g x} := by
    ext x
    exact sub_eq_zero
  rw [← he]
  exact (isRationalNormalPolyhedron_singleton h' (0 : W)).preimage δ hδ

end AffineMap
