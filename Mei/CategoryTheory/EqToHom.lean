/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Cancellation of equality morphisms

This cancellation lemma can be applied by unification when the categories of intermediate
`eqToHom`s agree only after unfolding, so rewriting with `eqToHom_trans` does not match.
-/

public section

namespace CategoryTheory

/-- Three composable `eqToHom`s returning to their source cancel before any morphism. -/
lemma eqToHom_comp_eqToHom_comp_eqToHom_comp {E : Type*} [Category E] {X Y Z W : E}
    (p : X = Y) (q : Y = Z) (r : Z = X) (f : X ⟶ W) :
    eqToHom p ≫ eqToHom q ≫ eqToHom r ≫ f = f := by
  cases p
  cases q
  simp

end CategoryTheory
