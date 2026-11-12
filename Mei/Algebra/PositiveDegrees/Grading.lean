/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Grading
public import Mei.Algebra.PositiveDegrees.Basic
public import TauCeti.Algebra.DirectSum.DegreeTail

/-!
# Degree submodules of positive gradings

The degree cutoff agrees with the module filtration used by Mei.
-/

public section

open TauCeti (PositiveDegrees IsPositiveGrading)

namespace TauCeti.PositiveDegrees

variable {N R M : Type*} [AddCommMonoid N] [Semiring R] [AddCommMonoid M] [Module R M]
  (d : PositiveDegrees N) (ℒ : N → Submodule R M)

/-- Strict positive cutoffs are the corresponding successor degree tails. -/
theorem degreeSubmodule_eq_degreeTail (k : ℕ) :
    d.degreeSubmodule ℒ k = TauCeti.DirectSum.degreeTail ℒ d.degree (k + 1) := by
  apply le_antisymm
  · rw [degreeSubmodule_def]
    apply iSup_le
    intro n
    apply TauCeti.DirectSum.le_degreeTail
    have := n.property
    omega
  · rw [TauCeti.DirectSum.degreeTail_def]
    refine iSup_le fun n => iSup_le fun hn => ?_
    apply d.le_degreeSubmodule ℒ
    omega

variable [IsPositiveGrading d ℒ]

/-- Any nonzero homogeneous element has strictly positive degree. -/
theorem degree_pos_of_mem_ne_zero {n : N} {x : M} (hx : x ∈ ℒ n) (hne : x ≠ 0) :
    0 < d.degree n := by
  have hn : n ∈ d.monoid ∧ n ≠ 0 := by
    by_contra h
    have hb := IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n (by tauto)
    exact hne (by simpa [hb] using hx)
  exact d.degree_pos hn.1 hn.2

end TauCeti.PositiveDegrees
