/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Dropping the first entry of a tuple with an appended final entry

Appending a final entry commutes with dropping the first entry of a tuple. This
reads the entry after an index of a degree history that ends with its incoming
degree, without peeling the first segment off the history. We use Mathlib's
`Fin.snoc`.
-/

public section

namespace Fin

/-- Dropping the first entry of a tuple commutes with appending a final entry. -/
theorem snoc_succ {α : Sort*} {n : ℕ} (g : Fin (n + 1) → α) (x : α) (i : Fin (n + 1)) :
    snoc (α := fun _ => α) g x i.succ = snoc (α := fun _ => α) (fun j : Fin n => g j.succ) x i := by
  refine lastCases ?_ (fun j => ?_) i
  · simp
  · rw [succ_castSucc, snoc_castSucc, snoc_castSucc]

end Fin
