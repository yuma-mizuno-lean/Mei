/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Lie actions by associative derivations

The Leibniz rule for a Lie action on an associative ring is independent of its scalar ring.
Together with a Lie module structure it describes a linear action by derivations, including
on noncommutative coefficient algebras. Inner commutator actions are examples.
-/

public section

namespace Mei

/-- A Lie action on an associative ring acts by derivations of its multiplication. -/
class IsDerivationAction (L A : Type*) [LieRing L] [Ring A] [LieRingModule L A] : Prop where
  /-- The associative Leibniz rule. -/
  lie_mul : ∀ (x : L) (a b : A), ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b

attribute [local instance] LieRing.ofAssociativeRing

/-- The commutator action of an associative ring on itself is by derivations. -/
instance (A : Type*) [Ring A] : IsDerivationAction A A where
  lie_mul x a b := by simp [Ring.lie_def, mul_sub, sub_mul, mul_assoc]

end Mei
