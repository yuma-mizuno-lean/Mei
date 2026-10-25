/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.DirectSum.Degree
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Degree tails under homogeneous embeddings

An injective linear map preserving homogeneous components reflects degree tails.
Thus truncating the target by degree does not kill additional low-degree elements
of the source. Homogeneous projection commutes with the map by
`DirectSum.map_decompose_shift`.
-/

public section

namespace LinearMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [DecidableEq ι]

/-- A homogeneous linear embedding identifies source degree tails with preimages of target tails. -/
theorem comap_degreeTail_eq_of_injective (f : M →ₗ[R] N)
    (ℳ : ι → Submodule R M) [DirectSum.Decomposition ℳ]
    (𝓝 : ι → Submodule R N) [DirectSum.Decomposition 𝓝]
    (hf : Function.Injective f) (hhom : ∀ i x, x ∈ ℳ i → f x ∈ 𝓝 i)
    (d : ι → ℤ) (k : ℕ) :
    (Mei.DirectSum.degreeTail 𝓝 d k).comap f = Mei.DirectSum.degreeTail ℳ d k := by
  ext x
  simp only [Submodule.mem_comap, Mei.DirectSum.mem_degreeTail_iff]
  have hproj (i : ι) : f (DirectSum.decompose ℳ x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N) :=
    DirectSum.map_decompose_shift ℳ 𝓝 f.toAddMonoidHom
      (fun i => i) Function.injective_id hhom i x
  constructor
  · intro hx i hi
    apply hf
    simpa only [map_zero] using (hproj i).trans (hx i hi)
  · intro hx i hi
    rw [← hproj i]
    simp only [hx i hi, map_zero]

end LinearMap
