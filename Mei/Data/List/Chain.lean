/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.Data.List.Chain

/-!
# Chains of relations transitive on a predicate

A list whose adjacent elements are related is pairwise related as soon as the relation is
transitive on the elements of the list. This refines `List.isChain_iff_pairwise`, which asks
for transitivity everywhere, to relations that are transitive only on elements satisfying a
predicate `p`, such as an angular order restricted to a cone.
-/

public section

namespace List

variable {α : Type*} {r : α → α → Prop} {p : α → Prop}

/-- A list whose adjacent elements are related, all of whose elements satisfy `p`, is pairwise
related when `r` is transitive on elements satisfying `p`. -/
theorem IsChain.pairwise_of_forall_mem {l : List α} (hl : l.IsChain r) (hp : ∀ a ∈ l, p a)
    (htrans : ∀ a b c, p a → p b → p c → r a b → r b c → r a c) : l.Pairwise r := by
  induction l with
  | nil => exact Pairwise.nil
  | cons a l ih =>
    have ihl := ih hl.tail fun b hb => hp b (mem_cons_of_mem a hb)
    refine pairwise_cons.mpr ⟨fun c hc => ?_, ihl⟩
    cases l with
    | nil => simp at hc
    | cons b l =>
      have hab : r a b := (isChain_cons_cons.mp hl).1
      rcases mem_cons.mp hc with rfl | hc
      · exact hab
      · exact htrans a b c (hp a mem_cons_self) (hp b (mem_cons_of_mem a mem_cons_self))
          (hp c (mem_cons_of_mem a (mem_cons_of_mem b hc))) hab
          ((pairwise_cons.mp ihl).1 c hc)

end List
