/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Analysis.Convex.Polyhedron.Projection
public import Mei.LinearAlgebra.Span.Pointwise
public import TauCeti.Analysis.Convex.Polyhedron.Pi.Basic

/-!
# Images of convex polyhedra under affine maps

Let `V` and `W` be real topological vector spaces. This file proves:

* `TauCeti.IsConvexPolyhedron.add_span_singleton`: for a convex polyhedron `P ⊆ V` and any
  `v : V`, the sum `P + ℝ ∙ v` is a convex polyhedron;
* `TauCeti.IsConvexPolyhedron.add_submodule`: `P + K` is a convex polyhedron for every finitely
  generated submodule `K` of `V`;
* `TauCeti.isConvexPolyhedron_singleton`: points of a finite-dimensional Hausdorff `W` are convex
  polyhedra;
* `TauCeti.IsConvexPolyhedron.graphOn`: the graph over `P` of a continuous affine map `V → W`
  is a convex polyhedron when `W` is finite-dimensional and Hausdorff;
* `TauCeti.IsConvexPolyhedron.image_snd`: the image of a convex polyhedron `G ⊆ V × W` under
  the second projection is a convex polyhedron when `V` is finite-dimensional;
* `TauCeti.IsConvexPolyhedron.affine_image`: the image of a convex polyhedron under a continuous
  affine map `V → W` is a convex polyhedron when `V` is finite-dimensional and `W` is
  finite-dimensional and Hausdorff. The map need not be injective; linear maps are included
  through `ContinuousLinearMap.toContinuousAffineMap`.

Adding a line is Fourier–Motzkin elimination of a nonnegative parameter twice, once in each
direction of the line (`Mei.Convex.isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem`). The
image under `g` is the projection of the graph of `g` over `P` to `W`, and this projection is the
slice at `0 ∈ V` of the sum of the graph with `V × {0}`.
-/

public section

open scoped Pointwise

namespace TauCeti

section Sum

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {P : Set V}

/-- Adding the line `ℝ ∙ v` to a convex polyhedron gives a convex polyhedron, for any `v`. -/
theorem IsConvexPolyhedron.add_span_singleton (hP : IsConvexPolyhedron P) (v : V) :
    IsConvexPolyhedron (P + ((ℝ ∙ v : Submodule ℝ V) : Set V)) := by
  rw [Submodule.add_span_singleton_eq_setOf_exists_nonneg]
  exact Mei.Convex.isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem
    (Mei.Convex.isConvexPolyhedron_setOf_exists_nonneg_add_smul_mem hP v) (-v)

/-- Adding a finitely generated submodule to a convex polyhedron gives a convex polyhedron. -/
theorem IsConvexPolyhedron.add_submodule (hP : IsConvexPolyhedron P) {K : Submodule ℝ V}
    (hK : K.FG) : IsConvexPolyhedron (P + (K : Set V)) := by
  have hadd := Submodule.add_span_induction (p := IsConvexPolyhedron) (s := (K : Set V))
    (by rwa [Submodule.span_eq]) (fun Q hQ v _ => hQ.add_span_singleton v) hP
  rwa [Submodule.span_eq] at hadd

end Sum

section Image

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

/-- In a finite-dimensional Hausdorff real topological vector space, a point is a convex
polyhedron. -/
theorem isConvexPolyhedron_singleton [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    [T2Space W] [FiniteDimensional ℝ W] (x : W) : IsConvexPolyhedron ({x} : Set W) := by
  -- Pull back the degenerate box `{e x}` along the coordinates `e` of a basis.
  let e := (Module.finBasis ℝ W).equivFun.toContinuousLinearEquiv
  convert (isConvexPolyhedron_pi_Icc (e x) (e x)).preimage
    e.toContinuousLinearMap.toContinuousAffineMap using 1
  ext y
  simp [Set.Icc_self, ← funext_iff]

/-- The graph over a convex polyhedron `P ⊆ V` of a continuous affine map `g : V → W` to a
finite-dimensional Hausdorff space is a convex polyhedron in `V × W`. -/
theorem IsConvexPolyhedron.graphOn [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [T2Space W]
    [FiniteDimensional ℝ W] {P : Set V} (hP : IsConvexPolyhedron P) (g : V →ᴬ[ℝ] W) :
    IsConvexPolyhedron (P.graphOn g) := by
  let fst : V × W →ᴬ[ℝ] V := (ContinuousLinearMap.fst ℝ V W).toContinuousAffineMap
  let δ : V × W →ᴬ[ℝ] W :=
    g.comp fst - (ContinuousLinearMap.snd ℝ V W).toContinuousAffineMap
  have he : P.graphOn g = fst ⁻¹' P ∩ δ ⁻¹' {0} := by
    ext p
    simp [fst, δ, sub_eq_zero]
  rw [he]
  exact (hP.preimage fst).inter ((isConvexPolyhedron_singleton 0).preimage δ)

/-- If `V` is finite-dimensional, the image of a convex polyhedron `G ⊆ V × W` under the second
projection is a convex polyhedron. -/
theorem IsConvexPolyhedron.image_snd [Module.Finite ℝ V] {G : Set (V × W)}
    (hG : IsConvexPolyhedron G) : IsConvexPolyhedron (Prod.snd '' G) := by
  have hK : (LinearMap.ker (LinearMap.snd ℝ V W)).FG := by
    rw [LinearMap.ker_snd, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  rw [← LinearMap.preimage_inr_add_ker_snd ℝ]
  exact (hG.add_submodule hK).preimage (ContinuousLinearMap.inr ℝ V W).toContinuousAffineMap

/-- The image of a convex polyhedron under a continuous affine map `g : V → W` is a convex
polyhedron, if `V` is finite-dimensional and `W` is finite-dimensional and Hausdorff. The map
`g` need not be injective. -/
theorem IsConvexPolyhedron.affine_image [Module.Finite ℝ V] [IsTopologicalAddGroup W]
    [ContinuousSMul ℝ W] [T2Space W] [FiniteDimensional ℝ W] {P : Set V}
    (hP : IsConvexPolyhedron P) (g : V →ᴬ[ℝ] W) : IsConvexPolyhedron (g '' P) := by
  rw [← Set.image_snd_graphOn]
  exact (hP.graphOn g).image_snd

end Image

end TauCeti
