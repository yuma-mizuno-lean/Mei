/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Directions of affine spans under affine maps

The direction of the affine span of an image is the linear image of the original
direction. This formula supports transport of transversality and codimension
without requiring an invertible map or a nonempty set.
Adding unrestricted coordinates preserves and reflects equality of affine spans.
For nonempty sets it also preserves and reflects equality of their directions.
An affine map whose linear image has larger dimension than an affine subspace
cannot have its image contained in that subspace.
-/

public section

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

namespace AffineSubspace

variable {k V W P Q : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [AddTorsor V P] [AddTorsor W Q]
  [FiniteDimensional k W]

/-- An affine subspace of dimension smaller than the image of an affine map
cannot contain that image. -/
theorem comap_ne_top_of_finrank_lt (S : AffineSubspace k Q) (f : P →ᵃ[k] Q)
    (hS : Module.finrank k S.direction < Module.finrank k (LinearMap.range f.linear)) :
    S.comap f ≠ ⊤ := by
  intro he
  have hle := direction_le (map_comap_le f S)
  rw [he, map_direction, direction_top, Submodule.map_top] at hle
  exact (not_le_of_gt hS) (Submodule.finrank_mono hle)

end AffineSubspace
