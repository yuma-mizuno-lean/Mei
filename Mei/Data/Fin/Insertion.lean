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

/-- Applying a function entrywise commutes with insertion into a finite tuple. -/
@[simp]
theorem comp_insertNth {α β : Sort*} {n : ℕ} (i : Fin (n + 1))
    (f : α → β) (a : α) (p : Fin n → α) :
    f ∘ i.insertNth (α := fun _ => α) a p =
      i.insertNth (α := fun _ => β) (f a) (f ∘ p) := by
  funext j
  cases j using Fin.succAboveCases i <;> simp

/-- Duplicating an entry after itself and dropping the final entry is the same
as inserting it before itself in the tuple with its final entry dropped. -/
theorem insertNth_succ_castSucc {α : Sort*} {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → α) (j : Fin (n + 1)) :
    i.succ.insertNth (α := fun _ => α) (v i) v j.castSucc =
      i.insertNth (α := fun _ => α) (v i) (fun k => v k.castSucc) j := by
  rcases lt_trichotomy j i with h | rfl | h
  · simp only [insertNth_apply_below (Fin.castSucc_lt_succ_iff.mpr h.le),
      insertNth_apply_below h]
    grind [Fin.castPred_castSucc, Fin.castSucc_castPred]
  · simp only [insertNth_apply_below (Fin.castSucc_lt_succ_iff.mpr le_rfl),
      insertNth_apply_same]
    grind [Fin.castPred_castSucc]
  · rcases lt_or_eq_of_le (Fin.succ_le_castSucc_iff.mpr h) with h' | h'
    · simp only [insertNth_apply_above h', insertNth_apply_above h, eq_rec_constant]
      grind [Fin.castSucc_pred_eq_pred_castSucc]
    · simp only [← h', insertNth_apply_same, insertNth_apply_above h, eq_rec_constant]
      congr 1
      apply Fin.ext
      have := congrArg Fin.val h'
      simp at this ⊢
      omega

/-- Repeating an entry before appending a final entry agrees with repeating
the corresponding entry in the extended tuple. -/
theorem snoc_insertNth_self {α : Sort*} {n : ℕ} (r : Fin n → α) (a : α)
    (i : Fin (n + 1)) :
    snoc (α := fun _ => α) (i.insertNth (snoc (α := fun _ => α) r a i) r) a =
      i.succ.insertNth (α := fun _ => α) (snoc (α := fun _ => α) r a i)
        (snoc (α := fun _ => α) r a) := by
  funext j
  refine lastCases ?_ (fun j => ?_) j
  · cases i using lastCases with
    | last => simp
    | cast i =>
      rw [insertNth_apply_above (by
        simpa only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last,
          Nat.add_lt_add_iff_right] using i.isLt)]
      simp [Fin.pred_last]
  · simp only [snoc_castSucc, insertNth_succ_castSucc]

end Fin
