/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort

/-!
# Ordered products and identity factors

Products of sorted finite sets in a noncommutative monoid depend only on the
indices with nonidentity values. This allows products at different finite cutoffs
to be compared without imposing commutativity. The argument uses Mathlib's
`List.prod_filter_bne_one` and uniqueness of strictly sorted lists.
-/

public section

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [Monoid M]

/-- Sorted products agree when their index sets agree wherever the factor is not one. -/
theorem prod_map_sort_eq_of_ne_one (s t : Finset ι) (f : ι → M)
    (h : ∀ i, f i ≠ 1 → (i ∈ s ↔ i ∈ t)) :
    (s.sort.map f).prod = (t.sort.map f).prod := by
  classical
  have hfilter : (s.sort.filter fun i => f i != 1) =
      (t.sort.filter fun i => f i != 1) := by
    apply List.Pairwise.eq_of_mem_iff
      ((s.sortedLT_sort).pairwise.filter _) ((t.sortedLT_sort).pairwise.filter _)
    intro i
    simp only [List.mem_filter, mem_sort, bne_iff_ne]
    exact and_congr_left fun hi => h i hi
  have hprod (l : List ι) :
      ((l.filter fun i => f i != 1).map f).prod = (l.map f).prod := by
    simpa only [List.filter_map, Function.comp_def] using
      List.prod_filter_bne_one (l.map f)
  rw [← hprod (s.sort (· ≤ ·)), hfilter, hprod (t.sort (· ≤ ·))]

end Finset
