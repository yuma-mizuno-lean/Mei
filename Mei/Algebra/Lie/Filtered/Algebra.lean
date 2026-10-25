/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Filtered.Action
public import Mei.Algebra.Lie.Derivation.Action
public import Mei.RingTheory.FilteredAlgebra.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Filtration-raising actions on coefficient algebra quotients

A filtration-raising Lie action induces nilpotent representations on the quotient rings
of a filtered coefficient algebra. These representations intertwine the quotient-ring
transitions. No derivation assumption is needed for these linear representations; under
that assumption, they also satisfy the Leibniz rule.

The construction transports the module representation along Mathlib's
`Submodule.Quotient.restrictScalarsEquiv`, using `LinearEquiv.conjAlgEquiv`.
-/

public section

attribute [local instance] LieRing.ofAssociativeRing

namespace Mei.AlgFiltration

variable {N R L A : Type*} [AddCommMonoid N] [CommRing R]
  [LieRing L] [LieAlgebra R L] [Ring A] [Algebra R A]
  [LieRingModule L A] [LieModule R L A]
  (F : AlgFiltration A) (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [DirectSum.Decomposition ℒ] [IsPositiveGrading d ℒ]
  [IsFiltrationRaising d ℒ (F.toModuleFiltration R)]

/-- The finite-order Lie representation on the original coefficient quotient ring. -/
def quotientLieAction (k : ℕ) : L →ₗ⁅R⁆ Module.End R (A ⧸ F.ideal (k + 1)) :=
  let e := Submodule.Quotient.restrictScalarsEquiv R (F.ideal (k + 1))
  (e.conjAlgEquiv R).toLieEquiv.toLieHom.comp
    ((F.toModuleFiltration R).quotientLieAction d ℒ k)

/-- Quotient representatives are acted on by the original Lie action. -/
@[simp]
theorem quotientLieAction_mk (k : ℕ) (x : L) (a : A) :
    F.quotientLieAction d ℒ k x (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ ⁅x, a⁆ := by
  simp [quotientLieAction, LinearEquiv.conjAlgEquiv_apply, ← Ideal.Quotient.mk_eq_mk,
    (F.toModuleFiltration R).quotientLieAction_mk d ℒ k x a]

/-- The finite-order operator retains the Leibniz rule. -/
theorem quotientLieAction_mul [IsDerivationAction L A]
    (k : ℕ) (x : L) (a b : A ⧸ F.ideal (k + 1)) :
    F.quotientLieAction d ℒ k x (a * b) =
      a * F.quotientLieAction d ℒ k x b + F.quotientLieAction d ℒ k x a * b := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, quotientLieAction_mk]
  simp only [IsDerivationAction.lie_mul, map_add, map_mul, quotientLieAction_mk]

/-- At order `k`, every acting endomorphism has `(k + 1)`st power zero. -/
theorem quotientLieAction_pow_eq_zero (k : ℕ) (x : L) :
    F.quotientLieAction d ℒ k x ^ (k + 1) = 0 := by
  simp only [quotientLieAction, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    AlgEquiv.toLieEquiv_apply, ← map_pow]
  rw [(F.toModuleFiltration R).quotientLieAction_pow_eq_zero d ℒ k x, map_zero]

/-- Quotient-ring transitions intertwine the coefficient representations. -/
@[simp]
theorem factor_quotientLieAction {k l : ℕ} (h : k ≤ l) (x : L)
    (q : A ⧸ F.ideal (l + 1)) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))
      (F.quotientLieAction d ℒ l x q) =
        F.quotientLieAction d ℒ k x
          (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) q) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

end Mei.AlgFiltration
