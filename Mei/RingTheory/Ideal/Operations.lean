/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Vanishing products in nilpotent ideals

When the fourth power of a left ideal vanishes, every product of four of its elements
is zero. This allows polynomial identities in such elements to truncate at degree three,
even in a noncommutative semiring.
-/

public section

namespace Ideal

variable {A : Type*} [Semiring A]

/-- A product of four elements of a left ideal vanishes if its fourth power is bottom. -/
theorem mul_four_eq_zero_of_pow_eq_bot (I : Ideal A) (hI : I ^ 4 = ⊥)
    {a b c d : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I) :
    a * b * c * d = 0 := by
  have h := Ideal.mul_mem_mul (Ideal.mul_mem_mul (Ideal.mul_mem_mul ha hb) hc) hd
  -- Expand the fixed numeral power with the left-associated ideal-power convention.
  have he : ((I * I) * I) * I = I ^ 4 := by
    simp only [show (4 : ℕ) = 3 + 1 from rfl, Submodule.pow_succ,
      show (3 : ℕ) = 2 + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl,
      Submodule.pow_zero, Ideal.one_eq_top, Ideal.top_mul]
  rwa [he, hI, Ideal.mem_bot] at h

end Ideal
