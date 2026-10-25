/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Nilpotence in finite filtration quotients

The kernel of projection from a finite filtration quotient to the order-one
quotient consists of nilpotent elements. Multiplicativity bounds the nilpotency
exponent by the cutoff, without assuming commutative multiplication.
-/

public section

namespace Mei.AlgFiltration

variable {A : Type*} [Ring A] (F : AlgFiltration A)

/-- An element killed by projection to order one is nilpotent in every finite quotient. -/
theorem isNilpotent_of_factor_eq_zero (k : ℕ) (x : A ⧸ F.ideal (k + 1))
    (hx : Ideal.Quotient.factor (F.antitone (Nat.le_add_left 1 k)) x = 0) :
    IsNilpotent x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ F.ideal 1 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Ideal.Quotient.factor_mk] using hx
  refine ⟨k + 1, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  simpa only [Nat.mul_one] using F.pow_mem ha (k + 1)

end Mei.AlgFiltration
