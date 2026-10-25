/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
# Lie actions by associative derivations

A Lie action on an associative ring acts by derivations when it satisfies the Leibniz rule
for multiplication. Scalar linearity remains part of the usual `LieModule` structure.
This condition makes finite exponentials of nilpotent acting operators multiplicative.
-/

public section

namespace Mei

/-- The Leibniz condition for a Lie action on an associative ring. -/
class IsDerivationAction (L A : Type*) [LieRing L] [Ring A] [LieRingModule L A] : Prop where
  /-- Each acting operator satisfies the associative Leibniz rule. -/
  lie_mul : ∀ (x : L) (a b : A), ⁅x, a * b⁆ = a * ⁅x, b⁆ + ⁅x, a⁆ * b

end Mei
