/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Ideal.Operations

/-!
# Products in powers of a left ideal

A product of `n` elements of a left ideal belongs to its `n`-th power.
Thus a vanishing ideal power annihilates every word of the corresponding length,
even in a noncommutative semiring and without a two-sidedness hypothesis.
-/

public section

namespace Ideal

variable {A : Type*} [Semiring A]

/-- A word vanishes if the corresponding power of its left ideal vanishes. -/
theorem list_prod_eq_zero_of_pow_eq_bot (I : Ideal A) (l : List A)
    (hl : ∀ x ∈ l, x ∈ I) (hI : I ^ l.length = ⊥) : l.prod = 0 := by
  have h := Ideal.list_prod_mem_pow hl
  rwa [hI, Ideal.mem_bot] at h

end Ideal
