/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Ring.Int

/-!
# Length bounds from sums of bounded integer weights

If every entry of an integer list is at most `B`, a sum greater than `B * (k - 1)`
forces the list to have at least `k` entries. Applied to the weights of letters in a word,
this converts a lower bound on total weight into a lower bound on word length.
-/

public section

namespace List

/-- An integer list with entries at most `B` has at least `k` entries if its sum is at least
`B * (k - 1) + 1`. No lower bound on the entries is required. -/
theorem le_length_of_sum_ge (l : List ℤ) (B k : ℕ) (hb : ∀ x ∈ l, x ≤ (B : ℤ))
    (hl : (B * (k - 1) + 1 : ℕ) ≤ l.sum) : k ≤ l.length := by
  by_contra h
  have hlen : l.length ≤ k - 1 := by omega
  have hs : l.sum ≤ (B : ℤ) * l.length := by
    simpa only [nsmul_eq_mul, mul_comm] using l.sum_le_length_nsmul (B : ℤ) hb
  have hbound := hs.trans
    (mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr hlen) (Int.natCast_nonneg B))
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hl
  omega

end List
