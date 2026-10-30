/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Nilpotence of the truncated polynomial parameter

The class of `X` in `R[X]/(X^n)` has vanishing `n`th power over any
commutative coefficient ring, including at exponent zero.
-/

public section

namespace AdjoinRoot

/-- The parameter in the truncated polynomial ring `R[X]/(X^n)` has zero `n`th power. -/
@[simp]
theorem root_X_pow_pow {R : Type*} [CommRing R] (n : ℕ) :
    root (Polynomial.X ^ n : Polynomial R) ^ n = 0 := by
  rw [← mk_X, ← map_pow, mk_self]

end AdjoinRoot
