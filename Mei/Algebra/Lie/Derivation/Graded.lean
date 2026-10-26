/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Injectivity of grading derivations

A grading derivation is injective when multiplication by its weight is injective
on each homogeneous piece. In particular, a positive integral grading over a
rational algebra has an injective Euler derivation. This supplies faithful
sheared representations without requiring a basis.

We use Mathlib's `LieDerivation.ofGrading` and Tau Ceti's
`DirectSum.map_decompose_shift` to test injectivity componentwise.
-/

public section

namespace LieDerivation

variable {N R L : Type*} [AddCommMonoid N] [DecidableEq N] [CommRing R]
  [LieRing L] [LieAlgebra R L] (ℒ : N → Submodule R L) [GradedLieAlgebra ℒ]

/-- A grading derivation is injective if its scalar weights act injectively on
all homogeneous pieces, including the possibly zero pieces. -/
theorem ofGrading_injective (φ : N →+ R)
    (hφ : ∀ n, Function.Injective (fun x : ℒ n => φ n • x)) :
    Function.Injective (ofGrading ℒ φ) := by
  intro x y hxy
  apply (DirectSum.decomposeLinearEquiv ℒ).injective
  apply DirectSum.ext
  intro n
  apply hφ n
  apply Subtype.ext
  have hhom (i : N) (a : L) (ha : a ∈ ℒ i) : ofGrading ℒ φ a ∈ ℒ i := by
    rw [ofGrading_apply_apply ℒ φ ha]
    exact (ℒ i).smul_mem _ ha
  have hcomp (z : L) :
      φ n • (DirectSum.decompose ℒ z n : L) =
        (DirectSum.decompose ℒ (ofGrading ℒ φ z) n : L) := by
    rw [← ofGrading_apply_apply ℒ φ (DirectSum.decompose ℒ z n).property]
    exact DirectSum.map_decompose_shift ℒ ℒ
      (ofGrading ℒ φ).toLinearMap.toAddMonoidHom id Function.injective_id hhom n z
  exact (hcomp x).trans ((congrArg (fun z => (DirectSum.decompose ℒ z n : L)) hxy).trans
    (hcomp y).symm)

end LieDerivation
