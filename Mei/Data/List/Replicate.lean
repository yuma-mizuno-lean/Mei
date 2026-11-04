/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Count

/-!
# Replicate lists

A permutation between two concatenations of replicate lists on distinct letters determines
the exponents. Under an injective map, the entries of a list with the same image as `i` are
the copies of `i`.
-/

public section

namespace List

variable {α : Type*}

/-- If `a^p b^q` is a permutation of `b^A a^B` for distinct `a, b`, then `p = B` and `q = A`. -/
theorem eq_and_eq_of_perm_replicate_append_replicate {a b : α} (hab : a ≠ b)
    {p q A B : ℕ} (h : (replicate p a ++ replicate q b).Perm
      (replicate A b ++ replicate B a)) : p = B ∧ q = A := by
  classical
  have c₁ := h.count_eq a
  have c₂ := h.count_eq b
  simpa [count_replicate, hab, hab.symm] using And.intro c₁ c₂

/-- Under injectivity of `m`, the entries `j` of `l` with `m j = m i` are the copies of `i`. -/
theorem filter_eq_replicate_count_of_injective {β : Type*} [DecidableEq α] [DecidableEq β]
    {m : α → β} (hinj : Function.Injective m) (i : α) (l : List α) :
    l.filter (fun j => m j = m i) = replicate (l.count i) i := by
  rw [← filter_beq]
  exact filter_congr fun j _ => Bool.eq_iff_iff.2 (by simp [hinj.eq_iff])

end List
