/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Comparing ideal and submodule quotient maps

An algebra map preserving two ideals induces the same map on quotient rings as
its underlying linear map on the scalar-restricted quotient modules. This lets
linear equivariance results apply to coefficient quotient algebras through
Mathlib's `Submodule.Quotient.restrictScalarsEquiv`.
-/

public section

namespace Ideal

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- Quotient algebra maps agree with quotient linear maps under the canonical
comparison between ideal quotients and scalar-restricted submodule quotients. -/
@[simp]
theorem quotientMapₐ_restrictScalarsEquiv (I : Ideal A) (J : Ideal B)
    [I.IsTwoSided] [J.IsTwoSided] (f : A →ₐ[R] B) (h : I ≤ J.comap f)
    (x : A ⧸ I.restrictScalars R) :
    quotientMapₐ J f h (Submodule.Quotient.restrictScalarsEquiv R I x) =
      Submodule.Quotient.restrictScalarsEquiv R J
        ((I.restrictScalars R).mapQ (J.restrictScalars R) f.toLinearMap h x) := by
  obtain ⟨a, rfl⟩ := (I.restrictScalars R).mkQ_surjective x
  rfl

end Ideal
