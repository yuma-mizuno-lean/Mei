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
Units congruent to one modulo a left ideal retain that congruence under
all integer powers, including inversion.
-/

public section

namespace Ideal

/-- A unit congruent to one modulo a left ideal remains so under every
integer power. In particular the congruence is preserved by inversion. -/
theorem zpow_sub_one_mem {A : Type*} [Ring A] (I : Ideal A)
    (u : Aˣ) (hu : (u : A) - 1 ∈ I) (n : ℤ) :
    ((u ^ n : Aˣ) : A) - 1 ∈ I := by
  have hinv : (↑u⁻¹ : A) - 1 ∈ I := by
    simpa only [mul_sub, mul_one, Units.inv_mul, neg_sub] using
      I.neg_mem (I.mul_mem_left (↑u⁻¹ : A) hu)
  refine zpow_induction_left (P := fun v : Aˣ => (v : A) - 1 ∈ I)
    (by simp) ?_ ?_ n
  · intro v hv
    simpa only [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel] using
      I.add_mem (I.mul_mem_left (u : A) hv) hu
  · intro v hv
    simpa only [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel] using
      I.add_mem (I.mul_mem_left (↑u⁻¹ : A) hv) hinv

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
