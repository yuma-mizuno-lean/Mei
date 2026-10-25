/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Products of commuting unipotent elements

The finite logarithm preserves commutation and converts a product of commuting
unipotent elements to a sum. The proof uses the finite polynomial definition and
the exponential/logarithm inverse identities supplied by Tau Ceti.
-/

public section

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Finite logarithms of commuting elements commute. -/
theorem Commute.nilpotentLog {a b : A} (h : Commute a b) :
    Commute (IsNilpotent.log a) (IsNilpotent.log b) := by
  rw [IsNilpotent.log_def, IsNilpotent.log_def]
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_right
  intro j hj
  have hab : Commute (a - 1) (b - 1) :=
    (h.sub_left (Commute.one_left b)).sub_right (Commute.one_right (a - 1))
  exact ((hab.pow_pow i j).smul_left _).smul_right _

/-- The finite logarithm takes commuting unipotent products to sums. -/
theorem IsNilpotent.log_mul_of_commute {a b : A} (hab : Commute a b)
    (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) :
    IsNilpotent.log (a * b) = IsNilpotent.log a + IsNilpotent.log b := by
  have hlog := hab.nilpotentLog
  have he : IsNilpotent.exp (IsNilpotent.log a + IsNilpotent.log b) = a * b := by
    rw [IsNilpotent.exp_add_of_commute hlog (IsNilpotent.isNilpotent_log ha)
      (IsNilpotent.isNilpotent_log hb), IsNilpotent.exp_log ha, IsNilpotent.exp_log hb]
  rw [← he, IsNilpotent.log_exp
    (hlog.isNilpotent_add (IsNilpotent.isNilpotent_log ha) (IsNilpotent.isNilpotent_log hb))]
