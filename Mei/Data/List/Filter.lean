/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.Basic

/-!
# Filtering sorted lists

A list whose elements are sorted by a key `τ` is the concatenation of its fibres
`l.filter (τ · = t)`, taken along any strictly increasing list `T` of keys containing
every value of `τ` on `l`. Elements with equal keys keep their relative order.

This is used to compare products of time-sorted enumerations of wall crossings with
products of their simultaneous crossing events. For a strictly decreasing list,
filtering below a selected entry recovers the suffix after it.
-/

public section

namespace List

variable {α β : Type*}

/-- If no element failing `p` precedes an element satisfying `p`, then the list is the
elements satisfying `p` followed by the remaining elements. -/
theorem filter_append_filter_not_of_pairwise {p : α → Bool} :
    ∀ {l : List α}, l.Pairwise (fun a b => p b → p a) →
      l.filter p ++ l.filter (fun a => !p a) = l
  | [], _ => rfl
  | a :: l, h => by
    rw [pairwise_cons] at h
    by_cases ha : p a
    · simp [ha, filter_append_filter_not_of_pairwise h.2]
    · have hl : ∀ b ∈ l, p b = false := fun b hb => by
        by_contra hb'
        exact ha (h.1 b hb (by simpa using hb'))
      have h₁ : l.filter p = [] := filter_eq_nil_iff.mpr fun b hb => by simp [hl b hb]
      have h₂ : l.filter (fun a => !p a) = l := filter_eq_self.mpr fun b hb => by simp [hl b hb]
      simp [ha, h₁, h₂]

/-- A list sorted by a key `τ` is the concatenation of its fibres over any strictly
increasing list of keys containing all values of `τ` on the list. -/
theorem flatten_map_filter_eq_of_pairwise [PartialOrder β] [DecidableEq β] {τ : α → β} :
    ∀ {T : List β} {l : List α}, T.Pairwise (· < ·) → l.Pairwise (fun a b => τ a ≤ τ b) →
      (∀ a ∈ l, τ a ∈ T) → (T.map fun t => l.filter fun a => τ a = t).flatten = l
  | [], l, _, _, hmem => by
    cases l with
    | nil => rfl
    | cons a l => simpa using hmem a mem_cons_self
  | t :: T, l, hT, hl, hmem => by
    rw [pairwise_cons] at hT
    have hmin : ∀ a ∈ l, t ≤ τ a := fun a ha => by
      rcases mem_cons.mp (hmem a ha) with h | h
      · exact h.ge
      · exact (hT.1 _ h).le
    have hrest : (T.map fun s => l.filter fun a => τ a = s) =
        T.map fun s => (l.filter fun a => !decide (τ a = t)).filter fun a => τ a = s := by
      refine map_congr_left fun s hs => ?_
      rw [filter_filter]
      refine filter_congr fun a _ => ?_
      by_cases has : τ a = s
      · simp [has, (hT.1 s hs).ne']
      · simp [has]
    rw [map_cons, flatten_cons, hrest, flatten_map_filter_eq_of_pairwise hT.2 (hl.filter _)
      (fun a ha => by
        obtain ⟨ha, hat⟩ := mem_filter.mp ha
        exact (mem_cons.mp (hmem a ha)).resolve_left (by simpa using hat))]
    refine filter_append_filter_not_of_pairwise (hl.imp_of_mem fun {a b} ha _ hab hb => ?_)
    simpa using le_antisymm ((of_decide_eq_true hb).symm ▸ hab) (hmin a ha)

/-- In a strictly decreasing list, the entries below a selected entry are exactly
those following it. -/
theorem Pairwise.filter_lt_getElem_eq_drop [Preorder α] [DecidableLT α] {l : List α}
    (hl : l.Pairwise (· > ·)) (j : ℕ) (hj : j < l.length) :
    l.filter (fun a => decide (a < l[j])) = l.drop (j + 1) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := pairwise_cons.mp hl
    cases j with
    | zero =>
      simp only [getElem_cons_zero, lt_self_iff_false, decide_false,
        filter_cons_of_neg, Bool.false_eq_true, not_false_eq_true, drop_succ_cons, drop_zero]
      exact filter_eq_self.mpr fun b hb => by simpa using ha b hb
    | succ j =>
      have hj' : j < l.length := by simpa using hj
      have hnot : ¬ a < l[j] := not_lt_of_gt (ha _ (getElem_mem hj'))
      simpa only [getElem_cons_succ, hnot, decide_false, filter_cons_of_neg,
        Bool.false_eq_true, not_false_eq_true, drop_succ_cons] using ih hl j hj'

end List
