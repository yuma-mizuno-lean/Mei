/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap

/-!
# Bounded images under continuous affine maps

A continuous affine map between normed spaces sends bounded sets to bounded sets, since it is a
translate of its continuous linear part.
-/

public section

open Set Pointwise

namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Continuous affine maps send bounded sets to bounded sets. -/
theorem isBounded_image (A : V →ᴬ[𝕜] W) {K : Set V} (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (A '' K) := by
  refine ((Bornology.isBounded_singleton (x := A 0)).add
    (A.contLinear.lipschitzWith.isBounded_image hK)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨A 0, mem_singleton _, A.contLinear x, mem_image_of_mem _ hx, ?_⟩
  simpa [add_comm] using (A.map_vadd 0 x).symm

end ContinuousAffineMap
