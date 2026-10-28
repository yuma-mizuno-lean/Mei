/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Order.Basic

/-!
# Enumerating finite sets in key order

Every finite set has a duplicate-free enumeration sorted by a key in a linear order.
Equal keys may occur in either order. This allows ordered products over finite sets
without requiring an order on the elements themselves.
-/

public section

namespace Finset

/-- A finite set has a duplicate-free enumeration sorted by any linearly ordered key.
Elements with equal keys may occur in either order. -/
theorem exists_nodup_pairwise_le_key {α β : Type*} [LinearOrder β] (S : Finset α)
    (f : α → β) : ∃ l : List α, l.Nodup ∧ (∀ j, j ∈ l ↔ j ∈ S) ∧
      l.Pairwise fun j k => f j ≤ f k := by
  classical
  let r : α → α → Bool := fun j k => decide (f j ≤ f k)
  have hr := List.pairwise_mergeSort (le := r)
    (fun a b c hab hbc => by
      simp only [r, decide_eq_true_eq] at hab hbc ⊢
      exact hab.trans hbc)
    (fun a b => by simpa [r] using le_total (f a) (f b)) S.toList
  refine ⟨S.toList.mergeSort r, (List.mergeSort_perm _ _).nodup_iff.mpr S.nodup_toList,
    fun j => by simp, hr.imp fun h => ?_⟩
  simpa [r] using h

end Finset
