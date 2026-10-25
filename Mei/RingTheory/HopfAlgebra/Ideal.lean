/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Antipode stability of powers of Hopf ideals

Although powers of a Hopf ideal need not be Hopf ideals, the antipode preserves
every power. Antimultiplicativity reverses the factor order, and two-sided ideal
powers absorb this reversal. The result applies over commutative semirings.

The ideal and its antipode stability are supplied by `TauCeti.HopfIdeal`.
-/

public section

namespace Mei.HopfIdeal

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

/-- The antipode preserves every power of the underlying ideal of a Hopf ideal. -/
theorem antipode_mem_pow (I : TauCeti.HopfIdeal R H) (n : ℕ) {u : H}
    (hu : u ∈ I.toIdeal ^ n) :
    _root_.HopfAlgebraStruct.antipode R u ∈ I.toIdeal ^ n := by
  have hI {x : H} (hx : x ∈ I.toIdeal) :
      _root_.HopfAlgebraStruct.antipode R x ∈ I.toIdeal :=
    TauCeti.HopfIdeal.mem_toIdeal.mpr (I.antipode_mem (TauCeti.HopfIdeal.mem_toIdeal.mp hx))
  induction n generalizing u with
  | zero => rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial
  | succ n ih =>
    rw [Submodule.pow_succ] at hu
    refine Submodule.mul_induction_on hu ?_ ?_
    · intro a ha b hb
      rw [_root_.HopfAlgebra.antipode_mul_antidistrib, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (hI hb) (ih ha)
    · intro a b ha hb
      rw [map_add]
      exact add_mem ha hb

end Mei.HopfIdeal
