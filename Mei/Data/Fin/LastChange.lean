/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Max

/-!
# The first change in a finite tuple

A nonconstant tuple has a unique adjacent change preceded by entries equal to
its initial entry. For tuples read in backward order, this locates the last
change along the forward sequence.
-/

public section

namespace Fin

/-- A nonconstant tuple has a unique first adjacent change. The condition on
the preceding entries includes the output side of the changing pair. -/
theorem existsUnique_first_change {α : Sort*} {n : ℕ} (b : Fin (n + 1) → α)
    (hb : ¬ ∀ i, b i = b 0) :
    ∃! j : Fin n, b j.succ ≠ b 0 ∧ ∀ i ≤ j.castSucc, b i = b 0 := by
  classical
  let S := Finset.univ.filter fun i => b i ≠ b 0
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := not_forall.mp hb
    exact ⟨i, by simp [S, hi]⟩
  let k := S.min' hS
  have hk : b k ≠ b 0 := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hk0 : k ≠ 0 := by intro h; exact hk (congrArg b h)
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hk0
  have hprefix : ∀ i < k, b i = b 0 := by
    intro i hi
    by_contra hn
    have hki := S.min'_le i (by simp [S, hn])
    exact (not_le_of_gt hi) hki
  refine ⟨j, ⟨by simpa only [hj] using hk, fun i hi =>
    hprefix i (by rw [← hj]; exact lt_of_le_of_lt hi j.castSucc_lt_succ)⟩, ?_⟩
  rintro l ⟨hl, hp⟩
  apply le_antisymm
  · by_contra h
    exact hk (hp k (by rw [← hj]; exact Fin.succ_le_castSucc_iff.mpr (lt_of_not_ge h)))
  · by_contra h
    exact hl (hprefix l.succ (by
      rw [← hj]
      exact Fin.succ_lt_succ_iff.mpr (lt_of_not_ge h)))

end Fin
