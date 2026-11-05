/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Applying indexed functions after a change of index

An indexed function commutes with transporting its argument and result along
an equality of indices. The domain and codomain families may have different universes.
-/

public section

namespace Function

universe u v w

/-- An indexed function commutes with casts in its domain and codomain families. -/
theorem cast_apply {ι : Sort u} {A : ι → Sort v} {B : ι → Sort w}
    (f : ∀ i, A i → B i) {i j : ι} (hij : i = j) (x : A i) :
    cast (congrArg B hij) (f i x) = f j (cast (congrArg A hij) x) := by
  cases hij
  rfl

end Function
