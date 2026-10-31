/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.List.OfFn

/-!
# Tuple lookup for a prepended list

The lookup function of a prepended list is the corresponding `Fin.cons` tuple.
This function-level form of `List.get_cons_zero` and `List.get_cons_succ'`
allows transport of constructions indexed by an entire list lookup tuple.
-/

public section

namespace List

/-- Prepending a list prepends its entire lookup tuple. -/
@[simp]
theorem get_cons_eq_cons {α : Type*} (a : α) (l : List α) :
    (a :: l).get = Fin.cons a l.get := by
  funext j
  cases j using Fin.cases <;> rfl

end List
