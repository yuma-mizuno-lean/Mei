/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Sort

/-!
# Products over insertion sorts with partially commuting factors

Sorting a list changes the product of its images in a monoid only by swapping factors that are
out of order. If every pair of entries is either already in order for the sorting relation, or
has commuting images, then the insertion sort has the same product.
-/

public section

namespace List

variable {α M : Type*} [Monoid M] (r : α → α → Prop) [DecidableRel r] (f : α → M)

/-- Inserting `a` into a list `u` whose entries are either after `a` for `r` or have images
commuting with `f a` places `f a` at the front of the product. -/
theorem prod_map_orderedInsert (a : α) {u : List α}
    (hu : ∀ b ∈ u, r a b ∨ Commute (f a) (f b)) :
    ((u.orderedInsert r a).map f).prod = f a * (u.map f).prod := by
  induction u with
  | nil => simp
  | cons b u ih =>
    rw [orderedInsert_cons]
    split_ifs with h
    · simp
    · have hb := (hu b mem_cons_self).resolve_left h
      simp only [map_cons, prod_cons, ih fun c hc => hu c (mem_cons_of_mem _ hc)]
      rw [← mul_assoc, ← mul_assoc, hb.eq]

/-- If each pair of entries of `l` is in order for `r` or has commuting images, then the
insertion sort of `l` has the same product of images as `l`. -/
theorem prod_map_insertionSort {l : List α}
    (hl : l.Pairwise fun a b => r a b ∨ Commute (f a) (f b)) :
    ((l.insertionSort r).map f).prod = (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := pairwise_cons.mp hl
    rw [insertionSort_cons, prod_map_orderedInsert r f a fun b hb =>
      ha b ((mem_insertionSort r).mp hb), map_cons, prod_cons, ih hl]

end List
