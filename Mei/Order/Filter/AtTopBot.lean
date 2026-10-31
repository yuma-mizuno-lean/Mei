/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Reversing eventual predicates at infinity

Reflection about a fixed parameter transfers eventual predicates at negative
infinity to eventual predicates at positive infinity. This identifies admission
of an incoming path with admission of its reversed tail.
-/

public section

namespace Filter

/-- Subtracting the parameter from a constant exchanges eventual predicates
at negative and positive infinity. -/
theorem eventually_const_sub_atBot {G : Type*} [AddCommGroup G] [PartialOrder G]
    [IsOrderedAddMonoid G] [IsDirectedOrder G] (b : G) {p : G → Prop} :
    (∀ᶠ t in atBot, p (b - t)) ↔ ∀ᶠ s in atTop, p s := by
  have hm : map (fun t : G => b - t) atBot = atTop := calc
    map (fun t : G => b - t) atBot =
        map ((fun t : G => t + b) ∘ Neg.neg) atBot := by
      simp [Function.comp_def, sub_eq_add_neg, add_comm]
    _ = map (fun t : G => t + b) (map Neg.neg atBot) := map_map.symm
    _ = atTop := by rw [map_neg_atBot, map_add_atTop_eq]
  rw [← eventually_map, hm]

end Filter
