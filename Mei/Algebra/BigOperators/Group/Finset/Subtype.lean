/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude Code
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over a fiber parameterized by an admitted subtype

A finite sum over a fiber that is in bijection with the admitted members of a
finite label type is the sum over all labels, with the weight of each rejected
label replaced by zero. Distinct labels remain distinct summands.
-/

public section

namespace Fintype

variable {X H β : Type*} [Fintype X] [Fintype H] [AddCommMonoid β]

/-- Sum over a fiber identified with the admitted labels `{a // P a}` as the
sum over all labels, where rejected labels contribute zero. -/
theorem sum_eq_sum_ite_of_equiv_subtype {P : H → Prop} [DecidablePred P]
    (e : X ≃ {a // P a}) (f : X → β) (g : H → β) (hfg : ∀ x, f x = g (e x).val) :
    ∑ x, f x = ∑ a, if P a then g a else 0 := by
  rw [Fintype.sum_equiv e f (fun a => g a.val) hfg, ← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp) g).symm

end Fintype
