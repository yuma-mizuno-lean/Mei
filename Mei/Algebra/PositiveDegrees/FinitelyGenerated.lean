/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.PositiveDegrees.Basic
public import Mei.Algebra.Group.AddSubmonoid.Degree

/-!
# Positive degrees from finite generation

A strictly positive integral functional on a finitely generated additive submonoid
gives positive degree data. The finite cutoffs are supplied by
`AddSubmonoid.FG.finite_setOf_degree_le`. This constructor allows algebraic and
geometric finite-generation criteria to feed the same graded completion interface.
-/

public section

namespace Mei.PositiveDegrees

variable {N : Type*} [AddCommMonoid N] {P : AddSubmonoid N}

/-- A strictly positive integral functional on a finitely generated submonoid
defines positive degree data, without a cancellation or saturation assumption. -/
def ofFG (hP : P.FG) (δ : N →+ ℤ)
    (hδ : ∀ {n}, n ∈ P → n ≠ 0 → 0 < δ n) : PositiveDegrees N where
  monoid := P
  degree := δ
  degree_pos := hδ
  finite_le := hP.finite_setOf_degree_le δ (fun _ hn hn0 => hδ hn hn0)

/-- The finite-generation construction retains the given submonoid. -/
@[simp]
theorem ofFG_monoid (hP : P.FG) (δ : N →+ ℤ)
    (hδ : ∀ {n}, n ∈ P → n ≠ 0 → 0 < δ n) :
    (ofFG hP δ hδ).monoid = P := (rfl)

/-- The finite-generation construction retains the given functional. -/
@[simp]
theorem ofFG_degree (hP : P.FG) (δ : N →+ ℤ)
    (hδ : ∀ {n}, n ∈ P → n ≠ 0 → 0 < δ n) :
    (ofFG hP δ hδ).degree = δ := (rfl)

end Mei.PositiveDegrees
