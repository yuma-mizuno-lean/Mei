/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Homogeneous projections after scalar extension

Mathlib's `DirectSum.Decomposition.baseChange` gives the internal decomposition
of a scalar-extended module without a flatness assumption. Its homogeneous
projections commute with forming pure tensors. This formula allows computations
in the extended grading without unfolding its decomposition.
-/

public section

open scoped TensorProduct

namespace DirectSum

variable {R S M ι : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (ℳ : ι → Submodule R M) [Decomposition ℳ]

/-- Homogeneous projection of a pure tensor is the tensor of its homogeneous projection. -/
@[simp]
theorem coe_decompose_baseChange_tmul (s : S) (x : M) (i : ι) :
    (decompose (fun i => (ℳ i).baseChange S) (s ⊗ₜ[R] x) i : S ⊗[R] M) =
      s ⊗ₜ[R] (decompose ℳ x i : M) :=
  (map_decompose_shift ℳ (fun i => (ℳ i).baseChange S)
    (TensorProduct.mk R S M s).toAddMonoidHom id Function.injective_id
    (fun _ _ hx => Submodule.tmul_mem_baseChange_of_mem s hx) i x).symm

end DirectSum
