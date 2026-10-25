/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Induction

/-!
# Products in powers of a left ideal

A product of `n` elements of a left ideal belongs to its `n`-th power.
Thus a vanishing ideal power annihilates every word of the corresponding length,
even in a noncommutative semiring and without a two-sidedness hypothesis.
-/

public section

namespace Ideal

variable {A : Type*} [Semiring A]

/-- A word in a left ideal lies in the ideal power given by its length. -/
theorem list_prod_mem_pow (I : Ideal A) (l : List A) (hl : ∀ x ∈ l, x ∈ I) :
    l.prod ∈ I ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp only [List.prod_nil, List.length_nil, Submodule.pow_zero,
      Ideal.one_eq_top, Submodule.mem_top]
  | append_singleton l x ih =>
    simp only [List.prod_append, List.prod_singleton, List.length_append,
      List.length_singleton, Submodule.pow_succ]
    exact Ideal.mul_mem_mul (ih (fun a ha => hl a (by simp [ha]))) (hl x (by simp))

/-- A word vanishes if the corresponding power of its left ideal vanishes. -/
theorem list_prod_eq_zero_of_pow_eq_bot (I : Ideal A) (l : List A)
    (hl : ∀ x ∈ l, x ∈ I) (hI : I ^ l.length = ⊥) : l.prod = 0 := by
  have h := I.list_prod_mem_pow l hl
  rwa [hI, Ideal.mem_bot] at h

end Ideal
