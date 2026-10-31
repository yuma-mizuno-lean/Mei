/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideal quotient maps and congruences of units

An algebra map preserving two ideals induces the same map on quotient rings as
its underlying linear map on the scalar-restricted quotient modules. This lets
linear equivariance results apply to coefficient quotient algebras through
Mathlib's `Submodule.Quotient.restrictScalarsEquiv`.
Units congruent to one modulo a two-sided ideal retain that congruence under
all integer powers, including inversion.
-/

public section

namespace Ideal

/-- A unit congruent to one modulo a two-sided ideal remains so under every
integer power. In particular the congruence is preserved by inversion. -/
theorem zpow_sub_one_mem {A : Type*} [Ring A] (I : Ideal A) [I.IsTwoSided]
    (u : Aˣ) (hu : (u : A) - 1 ∈ I) (n : ℤ) :
    ((u ^ n : Aˣ) : A) - 1 ∈ I := by
  have h : Units.map (Quotient.mk I).toMonoidHom u = 1 := by
    apply Units.ext
    exact (Quotient.mk_eq_one_iff_sub_mem _).mpr hu
  apply (Quotient.mk_eq_one_iff_sub_mem _).mp
  have hp : Units.map (Quotient.mk I).toMonoidHom (u ^ n) = 1 := by
    rw [map_zpow, h, one_zpow]
  exact congrArg Units.val hp

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
