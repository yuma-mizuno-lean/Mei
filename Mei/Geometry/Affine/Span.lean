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
