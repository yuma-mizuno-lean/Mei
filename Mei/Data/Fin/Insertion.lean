/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Duplicating entries of finite tuples

Duplicating a segment label and inserting an encounter between its two copies
use adjacent insertion indices. The identity below relates these conventions.
-/

public section

namespace Fin

/-- Duplicating an entry after itself and dropping the final entry is the same
as inserting it before itself in the tuple with its final entry dropped. -/
theorem insertNth_succ_castSucc {α : Sort*} {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → α) (j : Fin (n + 1)) :
    i.succ.insertNth (α := fun _ => α) (v i) v j.castSucc =
      i.insertNth (α := fun _ => α) (v i) (fun k => v k.castSucc) j := by
  rcases lt_trichotomy j i with h | rfl | h
  · obtain ⟨k, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
    have h' : k.castSucc.castSucc < i.succ :=
      Fin.castSucc_lt_succ_iff.mpr h.le
    rw [← succAbove_of_castSucc_lt i.succ k.castSucc h', insertNth_apply_succAbove,
      ← succAbove_of_castSucc_lt i k h, insertNth_apply_succAbove]
    simp [succAbove_of_castSucc_lt i k h]
  · rw [← succAbove_succ_self j, insertNth_apply_succAbove, insertNth_apply_same]
  · obtain ⟨k, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
    have hik : i ≤ k.castSucc := Fin.le_castSucc_iff.mpr h
    by_cases he : i = k.castSucc
    · subst i
      simp only [Fin.castSucc_succ, insertNth_apply_same]
      rw [← succAbove_castSucc_self k, insertNth_apply_succAbove]
    · have h' : i.succ ≤ k.castSucc.castSucc :=
        Fin.succ_le_castSucc_iff.mpr (lt_of_le_of_ne hik he)
      rw [← Fin.succ_castSucc, ← succAbove_of_le_castSucc i.succ k.castSucc h',
        insertNth_apply_succAbove, ← succAbove_of_le_castSucc i k hik,
        insertNth_apply_succAbove]

end Fin
