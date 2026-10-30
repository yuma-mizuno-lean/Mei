/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Filtering list products and sums

Deleting factors that evaluate to `1` preserves a list product, even in a noncommutative
monoid. The additive counterpart deletes terms that evaluate to `0`.
-/

public section

namespace List

variable {F G : Type*} [Monoid G]

/-- Deleting factors that evaluate to `1` does not change a product, as for
`Finset.prod_filter_of_ne`. The monoid need not be commutative. -/
@[to_additive /-- Deleting terms that evaluate to `0` does not change a sum. -/]
theorem prod_map_filter_of_ne {p : F → Prop} [DecidablePred p] {e : F → G} (l : List F)
    (h : ∀ x ∈ l, e x ≠ 1 → p x) : ((l.filter p).map e).prod = (l.map e).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih := ih fun x hx => h x (mem_cons_of_mem a hx)
    by_cases ha : p a
    · simp [ha, ih]
    · simp [ha, ih, not_not.mp (mt (h a mem_cons_self) ha)]

end List
