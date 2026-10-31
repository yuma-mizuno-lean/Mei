/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Appending and deleting entries of tuples

Deleting an entry before an appended final entry commutes with appending that
entry. This lets encounter-indexed degree histories retain their incoming degree
when an encounter is deleted. The adjacent entry in an appended tuple is computed
within its block, using the first entry of the right block at the junction.
Appending a final entry also preserves every constant prefix.
We use Mathlib's `Fin.removeNth`, `Fin.snoc` and `Fin.append`.
-/

public section

namespace Fin

/-- Appending a final entry preserves the value at every index of a constant prefix. -/
theorem snoc_eq_of_const_prefix {α : Sort*} {m n : ℕ} {x : Fin (m + n) → α}
    {q : α} (hx : ∀ i : Fin m, x (castAdd n i) = q) (a : α)
    (l : Fin (m + n + 1)) (hl : l.val < m) :
    snoc (α := fun _ => α) x a l = q := by
  have he : l = (castAdd n (⟨l.val, hl⟩ : Fin m)).castSucc := Fin.ext rfl
  rw [he, snoc_castSucc, hx]

/-- Applying a function to an appended tuple applies it to each block. -/
@[simp]
theorem comp_append {α β : Sort*} {m n : ℕ} (f : α → β)
    (a : Fin m → α) (b : Fin n → α) :
    f ∘ append a b = append (f ∘ a) (f ∘ b) := by
  funext j
  refine addCases (fun _ => ?_) (fun _ => ?_) j <;> simp

/-- The entry after an index in the left block, including the block junction. -/
@[simp]
theorem snoc_append_castAdd_succ {α : Sort*} {n m : ℕ}
    (p : Fin n → α) (q : Fin m → α) (a : α) (j : Fin n) :
    snoc (α := fun _ => α) (append p q) a (castAdd m j).succ =
      snoc (α := fun _ => α) p (snoc (α := fun _ => α) q a 0) j.succ := by
  rw [succ_castAdd]
  split_ifs with hj
  · rw [← append_snoc, append_right, hj, snoc_last]
  · simp only [snoc_castAdd, append_left]
    have hlt : j.succ.val < n := lt_of_le_of_ne (Nat.succ_le_of_lt j.isLt)
      (fun he => hj (Fin.ext he))
    simp only [snoc, dite_eq_left hlt]
    congr 1

/-- The entry after an index in the right block is computed in that block. -/
@[simp]
theorem snoc_append_natAdd_succ {α : Sort*} {n m : ℕ}
    (p : Fin n → α) (q : Fin m → α) (a : α) (j : Fin m) :
    snoc (α := fun _ => α) (append p q) a (natAdd n j).succ =
      snoc (α := fun _ => α) q a j.succ := by
  rw [succ_natAdd, ← append_snoc, append_right]

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
