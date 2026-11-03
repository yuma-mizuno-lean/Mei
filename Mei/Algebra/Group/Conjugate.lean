/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group

/-!
# Conjugating an exchange relation

An exchange relation `X * Y = Y * (T * X)` expresses `T` as the group commutator-like word
`Y⁻¹ * X * Y * X⁻¹`.
-/

public section

namespace Mei

/-- Conjugating the exchange `X Y = Y T X` gives `Y⁻¹ X Y X⁻¹ = T`. -/
theorem inv_mul_mul_mul_inv_eq_of_mul_eq {G : Type*} [Group G] {X Y T : G}
    (h : X * Y = Y * (T * X)) : Y⁻¹ * X * Y * X⁻¹ = T := by
  calc Y⁻¹ * X * Y * X⁻¹ = Y⁻¹ * (X * Y) * X⁻¹ := by group
    _ = T := by rw [h]; group

end Mei
