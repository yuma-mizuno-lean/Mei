/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Algebra.Equiv

/-!
# Transporting compatible ring maps through linear coordinates

A ring map compatible with scalar change becomes a semilinear map between
modules equipped with linear coordinates in its source and target algebras.
-/

public section

namespace LinearEquiv

variable {R S A B M N : Type*} [CommSemiring R] [CommSemiring S]
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]

/-- Compatible ring maps give semilinear maps after changing linear coordinates. -/
def semilinearTransport (φ : R →+* S) (ψ : A →+* B)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
    (E : A ≃ₗ[R] M) (E' : B ≃ₗ[S] N) : M →ₛₗ[φ] N where
  toFun a := E' (ψ (E.symm a))
  map_add' a b := by simp only [map_add]
  map_smul' r a := by
    rw [E.symm.map_smul, Algebra.smul_def, ψ.map_mul, hψ,
      ← Algebra.smul_def, E'.map_smul]

/-- The transported map applies the original ring map in the chosen coordinates. -/
@[simp]
theorem semilinearTransport_apply (φ : R →+* S) (ψ : A →+* B)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap S B (φ r))
    (E : A ≃ₗ[R] M) (E' : B ≃ₗ[S] N) (a : M) :
    semilinearTransport φ ψ hψ E E' a = E' (ψ (E.symm a)) := by
  -- This is the defining application of the semilinear-map record.
  rfl

end LinearEquiv
