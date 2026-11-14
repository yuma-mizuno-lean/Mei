/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Alternating.Contraction
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Contraction of conormal orientations

Contracting a top-degree conormal form by a vector outside the tangent subspace
produces a nonzero conormal form for the enlarged tangent subspace. This is the
orientation operation for a transverse polyhedral sweep.

The construction uses Mathlib's `AlternatingMap.curryLeft` and `map_insertNth`,
and descent through `Submodule.conormalFormsEquiv` to the normal quotient.
-/

public section

open Module

namespace AlternatingMap

section CommSemiring

variable {R M E : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommGroup E]
  [Module R M] [Module R E] {k : ℕ}

/-- Inserting two vectors in the first two slots anticommutes. -/
theorem curryLeft_curryLeft (α : M [⋀^Fin (k + 2)]→ₗ[R] E) (n m : M) :
    (α.curryLeft n).curryLeft m = -((α.curryLeft m).curryLeft n) := by
  have he := curryLeft_same α (n + m)
  simp only [map_add, curryLeft_add, LinearMap.add_apply, curryLeft_same,
    zero_add, add_zero] at he
  exact eq_neg_of_add_eq_zero_right he

end CommSemiring

end AlternatingMap
