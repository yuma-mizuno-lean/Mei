/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Surjectivity on homogeneous pieces

A surjective graded ring homomorphism is surjective on each homogeneous piece:
project any preimage to the required degree. This applies in particular to
homogeneous quotient reductions, whose target may have zero pieces.

We use Mathlib's `GradedRingHom.gradedAddHom` and
`GradedRingHom.map_directSumDecompose`.
-/

public noncomputable section

namespace GradedRingHom

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B]
  [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ B] [AddSubmonoidClass τ B]
  [DecidableEq ι] [AddMonoid ι] {𝒜 : ι → σ} {ℬ : ι → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- A surjective graded ring homomorphism restricts to a surjection on every
homogeneous piece. -/
theorem gradedAddHom_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) (i : ι) :
    Function.Surjective (f.gradedAddHom i) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.val
  refine ⟨DirectSum.decompose 𝒜 x i, ?_⟩
  apply Subtype.ext
  rw [gradedAddHom_apply_coe, f.map_directSumDecompose, hx]
  exact DirectSum.decompose_of_mem_same _ y.property

end GradedRingHom
