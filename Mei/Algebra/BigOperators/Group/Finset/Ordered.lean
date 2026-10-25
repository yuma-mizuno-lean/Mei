/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Basic

/-!
# Finite ordered products

An ordered product in a possibly noncommutative monoid is unchanged by adjoining
indices whose factors are one. This allows compatible finite supports at different
orders to define a product in an inverse limit. Products use `Finset.sort` and
`List.prod`, so the smallest index is the leftmost factor. Consecutive factors
can be exchanged when they commute. Identity factors are removed using Mathlib's
`List.prod_filter_bne_one`.
-/

public section

namespace Finset

variable {ι M : Type*} [LinearOrder ι] [Monoid M]

/-- Enlarging an ordered index set by identity factors preserves the product. -/
theorem prod_map_sort_subset {s t : Finset ι} (hst : s ⊆ t) (f : ι → M)
    (hf : ∀ i ∈ t, i ∉ s → f i = 1) :
    (s.sort.map f).prod = (t.sort.map f).prod := by
  classical
  have hfilter : (s.sort.filter fun i => f i != 1) =
      (t.sort.filter fun i => f i != 1) := by
    apply List.Pairwise.eq_of_mem_iff
      ((sortedLT_sort s).pairwise.filter _) ((sortedLT_sort t).pairwise.filter _)
    intro i
    simp only [List.mem_filter, mem_sort, bne_iff_ne]
    constructor
    · exact fun h => ⟨hst h.1, h.2⟩
    · exact fun h => ⟨by_contra fun hi => h.2 (hf i h.1 hi), h.2⟩
  calc
    _ = ((s.sort.filter fun i => f i != 1).map f).prod := by
      simpa only [List.filter_map, Function.comp_def, bne_iff_ne] using
        (List.prod_filter_bne_one (s.sort.map f)).symm
    _ = ((t.sort.filter fun i => f i != 1).map f).prod := by rw [hfilter]
    _ = _ := by
      simpa only [List.filter_map, Function.comp_def, bne_iff_ne] using
        List.prod_filter_bne_one (t.sort.map f)

/-- Swapping two consecutive indices in a finite increasing product preserves it
when their factors commute. -/
theorem prod_map_sort_swap (s : Finset ι) (f : ι → M) {a b : ι}
    (hab : a < b) (ha : a ∈ s) (hb : b ∈ s)
    (hgap : ∀ i ∈ s, ¬ (a < i ∧ i < b)) (hcomm : Commute (f a) (f b)) :
    (s.sort.map (fun i => f (Equiv.swap a b i))).prod = (s.sort.map f).prod := by
  classical
  let l := (s.filter (· < a)).sort
  let r := (s.filter (b < ·)).sort
  have hl : ∀ i ∈ l, i < a := by simp [l]
  have hr : ∀ i ∈ r, b < i := by simp [r]
  -- Isolate the two consecutive indices between an unchanged prefix and suffix.
  have hsort : s.sort = l ++ [a, b] ++ r := by
    apply (sortedLT_sort s).eq_of_mem_iff
    · apply List.sortedLT_append.mpr
      refine ⟨?_, sortedLT_sort _, ?_⟩
      · apply List.sortedLT_append.mpr
        refine ⟨sortedLT_sort _, by simp [hab, List.sortedLT_nil], ?_⟩
        intro i hi j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hl i hi
        · exact (hl i hi).trans hab
      · intro i hi j hj
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with hi | rfl | rfl
        · exact (hl i hi).trans (hab.trans (hr j hj))
        · exact hab.trans (hr j hj)
        · exact hr j hj
    · intro i
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        l, r, mem_sort, mem_filter]
      constructor
      · intro hi
        have := hgap i hi
        by_cases hia : i = a <;> by_cases hib : i = b <;> grind
      · grind
  have hleft : l.map (fun i => f (Equiv.swap a b i)) = l.map f := by
    apply List.map_congr_left
    intro i hi
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_lt (hl i hi))
      (ne_of_lt ((hl i hi).trans hab))]
  have hright : r.map (fun i => f (Equiv.swap a b i)) = r.map f := by
    apply List.map_congr_left
    intro i hi
    rw [Equiv.swap_apply_of_ne_of_ne (ne_of_gt (hab.trans (hr i hi)))
      (ne_of_gt (hr i hi))]
  simp only [hsort, List.map_append, List.prod_append, hleft, hright,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hcomm.eq]

end Finset
