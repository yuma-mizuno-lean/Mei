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

Products of conditional factors `if p x then e x else 1` are the products over the filtered
lists (`List.prod_map_filter_eq_prod_map_ite`), and they split along a disjunction `p ∨ q` of
conditions when no factor satisfying `q` precedes one satisfying `p`
(`List.prod_map_ite_or`). These are the noncommutative counterparts of `Finset.prod_filter`
and `Finset.prod_ite`, used for ordered products of wall labels.
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

/-- The product over a filtered list is the product of the conditional factors, as for
`Finset.prod_filter`. The monoid need not be commutative. -/
@[to_additive /-- The sum over a filtered list is the sum of the conditional terms. -/]
theorem prod_map_filter_eq_prod_map_ite (p : F → Prop) [DecidablePred p] (e : F → G)
    (l : List F) :
    ((l.filter fun x => p x).map e).prod = (l.map fun x => if p x then e x else 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases ha : p a <;> simp [ha, ih]

/-- A product of conditional factors is `1` if every factor whose condition holds is `1`. -/
@[to_additive /-- A sum of conditional terms is `0` if every term whose condition holds is
`0`. -/]
theorem prod_map_ite_eq_one {p : F → Prop} [DecidablePred p] {e : F → G} {l : List F}
    (h : ∀ x ∈ l, p x → e x = 1) : (l.map fun x => if p x then e x else 1).prod = 1 :=
  prod_eq_one fun y hy => by
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    split_ifs with hp
    · exact h x hx hp
    · rfl

/-- A product of conditional factors is the full product if every factor whose condition
fails is `1`. -/
@[to_additive /-- A sum of conditional terms is the full sum if every term whose condition
fails is `0`. -/]
theorem prod_map_ite_eq_prod_map {p : F → Prop} [DecidablePred p] {e : F → G} {l : List F}
    (h : ∀ x ∈ l, ¬p x → e x = 1) :
    (l.map fun x => if p x then e x else 1).prod = (l.map e).prod :=
  (prod_map_filter_eq_prod_map_ite p e l).symm.trans
    (prod_map_filter_of_ne l fun x hx => not_imp_comm.mp (h x hx))

/-- Products of conditional factors agree if every factor is `1` or has equivalent
conditions. -/
@[to_additive /-- Sums of conditional terms agree if every term is `0` or has equivalent
conditions. -/]
theorem prod_map_ite_congr {p q : F → Prop} [DecidablePred p] [DecidablePred q] {e : F → G}
    {l : List F} (h : ∀ x ∈ l, e x = 1 ∨ (p x ↔ q x)) :
    (l.map fun x => if p x then e x else 1).prod =
      (l.map fun x => if q x then e x else 1).prod :=
  congrArg prod (map_congr_left fun x hx => by
    rcases h x hx with h | h
    · simp [h]
    · exact if_congr h rfl rfl)

/-- If the conditions `p` and `q` are disjoint on `l` and no factor satisfying `q` precedes one
satisfying `p`, the conditional product for `p ∨ q` is that for `p` followed by that for
`q`. -/
@[to_additive /-- If the conditions `p` and `q` are disjoint on `l` and no term satisfying `q`
precedes one satisfying `p`, the conditional sum for `p ∨ q` is that for `p` followed by that
for `q`. -/]
theorem prod_map_ite_or {p q : F → Prop} [DecidablePred p] [DecidablePred q] (e : F → G)
    {l : List F} (hpq : ∀ x ∈ l, p x → ¬q x) (hord : l.Pairwise fun x y => q x → ¬p y) :
    (l.map fun x => if p x ∨ q x then e x else 1).prod =
      (l.map fun x => if p x then e x else 1).prod *
        (l.map fun x => if q x then e x else 1).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [pairwise_cons] at hord
    simp only [map_cons, prod_cons]
    rw [ih (fun x hx => hpq x (mem_cons_of_mem a hx)) hord.2]
    by_cases hp : p a
    · simp [hp, hpq a mem_cons_self hp, mul_assoc]
    · by_cases hq : q a
      · rw [prod_map_ite_eq_one (p := p) fun x hx hpx => absurd hpx (hord.1 x hx hq)]
        simp [hp, hq]
      · simp [hp, hq]

end List
