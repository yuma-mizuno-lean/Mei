/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear maps into finite direct sums

For a finite index type, taking linear maps from an arbitrary module commutes with
the direct sum. No finite generation or projectivity of the source is needed.
The equivalence is assembled from Mathlib's `DirectSum.linearEquivFunOnFintype`
and `LinearEquiv.linearMapPi`. Its inverse reads each component pointwise.
-/

public noncomputable section

open scoped DirectSum

namespace DirectSum

variable {R H ι : Type*} [CommSemiring R] [AddCommMonoid H] [Module R H]
  [Fintype ι] (M : ι → Type*)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Linear maps from any module commute with a finite direct sum in their target. -/
def linearMapEquivOfFintype :
    (⨁ i, H →ₗ[R] M i) ≃ₗ[R] (H →ₗ[R] ⨁ i, M i) :=
  (linearEquivFunOnFintype R ι (fun i => H →ₗ[R] M i)).trans
    ((LinearEquiv.linearMapPi R).trans
      (LinearEquiv.congrRight (linearEquivFunOnFintype R ι M).symm))

/-- Evaluation of the assembled map reads the same homogeneous component. -/
@[simp]
theorem linearMapEquivOfFintype_apply (f : ⨁ i, H →ₗ[R] M i) (x : H) (i : ι) :
    linearMapEquivOfFintype M f x i = f i x := (rfl)

/-- Decomposition of a map reads its components pointwise. -/
@[simp]
theorem linearMapEquivOfFintype_symm_apply (f : H →ₗ[R] ⨁ i, M i) (i : ι) (x : H) :
    (linearMapEquivOfFintype M).symm f i x = f x i := (rfl)

end DirectSum
