/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Proper zero-level subsets

A function that is negative somewhere on a set cannot vanish on the entire set.
-/

public section

namespace Set

/-- A function with a negative value on a set has a proper zero-level subset. -/
theorem zero_face_ne_self_of_exists_neg {α : Type*} (P : Set α) (g : α → ℝ)
    (hg : ∃ p ∈ P, g p < 0) : {x ∈ P | g x = 0} ≠ P := by
  intro heq
  obtain ⟨p, hp, hgp⟩ := hg
  have hpface : p ∈ {x ∈ P | g x = 0} := by rwa [heq]
  exact hgp.ne hpface.2

end Set
