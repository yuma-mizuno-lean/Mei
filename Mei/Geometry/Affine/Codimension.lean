/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.AffineSpace.Codimension
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dimension bounds for intersections of affine subspaces

Affine subspaces with equal-dimensional but different directions have an
intersection of strictly smaller direction dimension. In particular, distinct
hyperplane directions give intersections of codimension at least two. The
statements include empty intersections and require no topology or ordering of
the scalar division ring. An affine subspace cannot contain the image of an
affine map whose linear image has larger dimension; only the subspace direction
needs to be finite-dimensional.

A nonzero functional vanishing on a codimension-one set has its affine
direction as kernel, by Mathlib's `Module.Dual.finrank_ker_add_one_of_ne_zero`.
-/

public section

namespace LinearMap

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A nonzero functional vanishing on a codimension-one set has its direction as kernel. -/
theorem ker_eq_direction_affineSpan (f : V →ₗ[K] K) (hf : f ≠ 0) {P : Set V}
    (hP : ∀ x ∈ P, f x = 0)
    (hdim : Module.finrank K (affineSpan K P).direction + 1 = Module.finrank K V) :
    f.ker = (affineSpan K P).direction := by
  have hle : (affineSpan K P).direction ≤ f.ker := by
    have ha : affineSpan K P ≤ f.ker.toAffineSubspace :=
      affineSpan_le.mpr fun x hx => LinearMap.mem_ker.mpr (hP x hx)
    simpa using AffineSubspace.direction_le ha
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end LinearMap
