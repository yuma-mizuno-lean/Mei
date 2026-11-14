/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Geometry.Convex.Polyhedron.Rational.Equalizer
public import Mei.Geometry.Convex.Polyhedron.Rational.Sweep
public import Mei.LinearAlgebra.Span.Pointwise

/-!
# Images of rational-normal polyhedra under rational affine maps

Let `V` and `W` be finite-dimensional real normed spaces with integral lattices `i : N → V` and
`i' : N' → W`. This file proves:

* `Mei.IsRationalNormalPolyhedron.add_span`: for a rational-normal polyhedron `P ⊆ V` and any
  set `s` of lattice vectors, `P + span ℝ (i '' s)` is a rational-normal polyhedron; in
  particular `P + ℝ ∙ i n` is one (`add_span_singleton`);
* `Mei.IsRationalPolyhedron.add_span` and `Mei.IsRationalPolyhedron.add_span_singleton`: the
  same for polyhedra with rational normals and rational offsets;
* `Mei.IsRationalNormalPolyhedron.image_snd`: the image of a rational-normal polyhedron in
  `V × W` (for the product lattice) under the second projection is rational-normal;
* `Mei.IsRationalNormalPolyhedron.graphOn`: the graph over `P` of an affine map `V → W` with
  rational linear part is rational-normal for the product lattice;
* `Mei.IsRationalNormalPolyhedron.affine_image`: the image of a rational-normal polyhedron under
  an affine map with rational linear part is a rational-normal polyhedron.

In the last statement the map need not be injective on `P`, and its translation part and the
offsets of `P` are arbitrary real numbers. It contains the images under integral affine
equivalences (`Mei.IsRationalNormalPolyhedron.image`). For rational-normal polyhedra it drops
the injectivity hypothesis of `Mei.IsLocallyClosedPolyhedron.image_of_injOn` and concludes that
the image is closed. Images of locally closed polyhedra under noninjective maps, and rational
offsets of images, are not treated here.

Adding the line through a lattice vector `i n` is the negative-ray sweep along `i n` followed by
the one along `-i n` (`Mei.IsRationalNormalPolyhedron.negRay`); these sweeps are explicit
Fourier–Motzkin eliminations. The image under `g` is the projection of the graph of `g` over
`P`, and the projection is the slice at `0 ∈ V` of the sum of the graph with `V × {0}`, which is
spanned by the lattice vectors `(i n, 0)`.
-/

public section

open scoped Pointwise

namespace Mei

variable {N V N' W : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup N'] [NormedAddCommGroup W] [NormedSpace ℝ W] {i : N →+ V} {i' : N' →+ W}
  {h : TauCeti.Toric.IsIntegralLattice i} {h' : TauCeti.Toric.IsIntegralLattice i'}
  {P : Set V}

namespace IsRationalNormalPolyhedron

/-- Adding the line through a lattice vector to a rational-normal polyhedron gives a
rational-normal polyhedron. -/
theorem add_span_singleton (hP : IsRationalNormalPolyhedron h P) (n : N) :
    IsRationalNormalPolyhedron h (P + ((ℝ ∙ i n : Submodule ℝ V) : Set V)) := by
  rw [Submodule.add_span_singleton_eq_setOf_exists_nonneg]
  simpa only [map_neg] using (hP.negRay n).negRay (-n)

/-- Adding the real span of any set of lattice vectors to a rational-normal polyhedron gives a
rational-normal polyhedron. -/
theorem add_span (hP : IsRationalNormalPolyhedron h P) (s : Set N) :
    IsRationalNormalPolyhedron h (P + (Submodule.span ℝ (i '' s) : Set V)) := by
  have := h.finiteDimensional
  refine Submodule.add_span_induction (p := IsRationalNormalPolyhedron h)
    (IsNoetherian.noetherian _) ?_ hP
  rintro Q hQ _ ⟨n, -, rfl⟩
  exact hQ.add_span_singleton n

/-- The image of a rational-normal polyhedron in `V × W`, for the product lattice, under the
second projection is a rational-normal polyhedron in `W`. The lattice proof `h` is explicit
because it cannot be inferred from the product lattice proof `h.prod h'`. -/
theorem image_snd (h : TauCeti.Toric.IsIntegralLattice i) {G : Set (V × W)}
    (hG : IsRationalNormalPolyhedron (h.prod h') G) :
    IsRationalNormalPolyhedron h' (Prod.snd '' G) := by
  -- The kernel of the second projection is spanned by the lattice vectors `(i n, 0)`.
  have hK : LinearMap.ker (LinearMap.snd ℝ V W) =
      Submodule.span ℝ ((i.prodMap i') '' Set.range (AddMonoidHom.inl N N')) := by
    rw [LinearMap.ker_snd, LinearMap.range_eq_map, ← h.span_range_eq_top, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp]
    congr 2
    ext n <;> simp
  have hinr : Toric.IsRationalLinearMap h' (h.prod h') (LinearMap.inr ℝ V W) :=
    Toric.IsRationalLinearMap.of_integral_compatible h' (h.prod h') (AddMonoidHom.inr N N') _
      fun n => by simp
  rw [← LinearMap.preimage_inr_add_ker_snd ℝ, hK]
  exact (hG.add_span _).preimage (ContinuousLinearMap.inr ℝ V W).toContinuousAffineMap hinr

/-- The graph over a rational-normal polyhedron `P` of an affine map `g : V → W` with rational
linear part is a rational-normal polyhedron for the product lattice. -/
theorem graphOn (hP : IsRationalNormalPolyhedron h P) (g : V →ᵃ[ℝ] W)
    (hg : Toric.IsRationalLinearMap h h' g.linear) :
    IsRationalNormalPolyhedron (h.prod h') (P.graphOn g) := by
  have he : P.graphOn g = Prod.fst ⁻¹' P ∩ {p : V × W | g p.1 = AffineMap.id ℝ W p.2} := by
    ext p
    simp
  rw [he]
  exact (hP.preimage (ContinuousLinearMap.fst ℝ V W).toContinuousAffineMap
    (Toric.IsRationalLinearMap.fst h h')).inter
    (AffineMap.isRationalNormalPolyhedron_pullback_matching g (AffineMap.id ℝ W) hg
      (Toric.IsRationalLinearMap.id h'))

/-- The image of a rational-normal polyhedron under an affine map with rational linear part is
a rational-normal polyhedron. The map need not be injective, and its translation part is an
arbitrary real vector. -/
theorem affine_image (hP : IsRationalNormalPolyhedron h P) (g : V →ᵃ[ℝ] W)
    (hg : Toric.IsRationalLinearMap h h' g.linear) :
    IsRationalNormalPolyhedron h' (g '' P) := by
  rw [← Set.image_snd_graphOn]
  exact (hP.graphOn g hg).image_snd h

end IsRationalNormalPolyhedron

namespace IsRationalPolyhedron

/-- Adding the line through a lattice vector to a polyhedron with rational normals and rational
offsets gives such a polyhedron. -/
theorem add_span_singleton (hP : IsRationalPolyhedron h P) (n : N) :
    IsRationalPolyhedron h (P + ((ℝ ∙ i n : Submodule ℝ V) : Set V)) := by
  rw [Submodule.add_span_singleton_eq_setOf_exists_nonneg]
  simpa only [map_neg] using (hP.negRay n).negRay (-n)

/-- Adding the real span of any set of lattice vectors to a polyhedron with rational normals and
rational offsets gives such a polyhedron. -/
theorem add_span (hP : IsRationalPolyhedron h P) (s : Set N) :
    IsRationalPolyhedron h (P + (Submodule.span ℝ (i '' s) : Set V)) := by
  have := h.finiteDimensional
  refine Submodule.add_span_induction (p := IsRationalPolyhedron h)
    (IsNoetherian.noetherian _) ?_ hP
  rintro Q hQ _ ⟨n, -, rfl⟩
  exact hQ.add_span_singleton n

end IsRationalPolyhedron

end Mei
