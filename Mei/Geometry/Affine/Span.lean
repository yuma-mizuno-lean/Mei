/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Directions of affine spans under affine maps

The direction of the affine span of an image is the linear image of the original
direction. This formula supports transport of transversality and codimension
without requiring an invertible map or a nonempty set.
A linear map whose kernel contains the direction of a set is constant on it.
Adding unrestricted coordinates preserves and reflects equality of affine spans.
For nonempty sets it also preserves and reflects equality of their directions.
-/

public section

namespace LinearMap

/-- A linear map whose kernel contains the direction of a set is constant on that set. -/
theorem apply_eq_of_direction_le_ker {K V W : Type*} [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) {P : Set V}
    (hf : (affineSpan K P).direction ≤ f.ker) {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    f x = f y := by
  have hd := hf (AffineSubspace.vsub_mem_direction (subset_affineSpan K P hx)
    (subset_affineSpan K P hy))
  rwa [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at hd

end LinearMap

namespace AffineMap

variable {k V V' P P' : Type*} [Ring k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup V'] [Module k V'] [AddTorsor V' P']

/-- Affine maps transport the direction of an affine span by their linear part. -/
theorem direction_affineSpan_image (f : P →ᵃ[k] P') (s : Set P) :
    (affineSpan k (f '' s)).direction = (affineSpan k s).direction.map f.linear := by
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]

end AffineMap

namespace Mei

section Prod

variable {k V E P Q : Type*} [Ring k]
  [AddCommGroup V] [Module k V] [AddTorsor V P]
  [AddCommGroup E] [Module k E] [AddTorsor E Q]

/-- Adding an unrestricted factor preserves and reflects equality of affine spans,
including for empty sets. -/
theorem affineSpan_prod_univ_eq_iff (s t : Set P) :
    affineSpan k (s ×ˢ (Set.univ : Set Q)) = affineSpan k (t ×ˢ (Set.univ : Set Q)) ↔
      affineSpan k s = affineSpan k t := by
  classical
  let q₀ : Q := Classical.arbitrary Q
  rw [affineSpan_prod_eq, affineSpan_prod_eq, AffineSubspace.span_univ]
  constructor
  · intro h
    ext p
    have := congrArg (fun A : AffineSubspace k (P × Q) => (p, q₀) ∈ A) h
    simpa using this
  · exact fun h => congrArg (fun A : AffineSubspace k P => A.prod ⊤) h

/-- The direction of the affine span of a nonempty cylinder has an unrestricted
second factor. Nonemptiness is needed because the empty span has zero direction. -/
theorem direction_affineSpan_prod_univ {s : Set P} (hs : s.Nonempty) :
    (affineSpan k (s ×ˢ (Set.univ : Set Q))).direction =
      (affineSpan k s).direction.prod ⊤ := by
  rw [direction_affineSpan, vectorSpan_prod_eq hs Set.univ_nonempty]
  rw [← direction_affineSpan, ← direction_affineSpan, AffineSubspace.span_univ,
    AffineSubspace.direction_top]

/-- Adding unrestricted coordinates preserves and reflects equality of supporting
directions for nonempty sets. -/
theorem direction_affineSpan_prod_univ_eq_iff {s t : Set P}
    (hs : s.Nonempty) (ht : t.Nonempty) :
    (affineSpan k (s ×ˢ (Set.univ : Set Q))).direction =
      (affineSpan k (t ×ˢ (Set.univ : Set Q))).direction ↔
      (affineSpan k s).direction = (affineSpan k t).direction := by
  rw [direction_affineSpan_prod_univ hs, direction_affineSpan_prod_univ ht]
  constructor
  · intro h
    ext v
    have := congrArg (fun S : Submodule k (V × E) => (v, 0) ∈ S) h
    simpa using this
  · exact fun h => congrArg (fun S : Submodule k V => S.prod (⊤ : Submodule k E)) h

end Prod
end Mei
