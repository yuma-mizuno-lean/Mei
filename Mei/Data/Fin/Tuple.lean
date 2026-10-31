/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Deletion before the final entry of a tuple

Deleting an entry before an appended final entry commutes with appending that
entry. This lets encounter-indexed degree histories retain their incoming degree
when an encounter is deleted. We use Mathlib's `Fin.removeNth` and `Fin.snoc`.
-/

public section

namespace Fin

/-- Deleting an entry preceding an appended final entry preserves that final entry. -/
@[simp]
theorem removeNth_snoc {α : Sort*} {n : ℕ} (r : Fin (n + 1) → α) (a : α)
    (i : Fin (n + 1)) :
    i.castSucc.removeNth (snoc (α := fun _ => α) r a) =
      snoc (α := fun _ => α) (i.removeNth r) a := by
  funext j
  refine lastCases ?_ (fun j => ?_) j
  · simp only [removeNth, succAbove_ne_last_last (castSucc_ne_last i), snoc_last]
  · simp only [removeNth, castSucc_succAbove_castSucc, snoc_castSucc]

end Fin
