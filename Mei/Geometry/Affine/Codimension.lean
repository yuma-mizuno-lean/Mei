/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Dimension bounds for intersections of affine subspaces

Affine subspaces with equal-dimensional but different directions have an
intersection of strictly smaller direction dimension. In particular, distinct
hyperplane directions give intersections of codimension at least two. The
statements include empty intersections and require no topology or ordering of
the scalar division ring.
-/

public section

namespace AffineSubspace

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Intersecting equal-dimensional affine subspaces with different directions
strictly lowers the direction dimension, including for an empty intersection. -/
theorem finrank_direction_inf_lt_of_eq_of_ne (A B : AffineSubspace K V)
    (hdim : Module.finrank K A.direction = Module.finrank K B.direction)
    (hne : A.direction ≠ B.direction) :
    Module.finrank K (A ⊓ B).direction < Module.finrank K A.direction := by
  have hlt : A.direction ⊓ B.direction < A.direction := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hle : A.direction ≤ B.direction := by rw [← heq]; exact inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hle hdim)
  have hle : (A ⊓ B).direction ≤ A.direction ⊓ B.direction :=
    le_inf (direction_le inf_le_left) (direction_le inf_le_right)
  exact (Submodule.finrank_mono hle).trans_lt (Submodule.finrank_lt_finrank_of_lt hlt)

/-- The intersection of two codimension-one affine subspaces with different
directions has codimension at least two. No nonemptiness hypothesis is needed. -/
theorem finrank_direction_inf_add_one_lt (A B : AffineSubspace K V)
    (hA : Module.finrank K A.direction + 1 = Module.finrank K V)
    (hB : Module.finrank K B.direction + 1 = Module.finrank K V)
    (hne : A.direction ≠ B.direction) :
    Module.finrank K (A ⊓ B).direction + 1 < Module.finrank K V := by
  have heq : Module.finrank K A.direction = Module.finrank K B.direction :=
    Nat.add_right_cancel (hA.trans hB.symm)
  rw [← hA]
  exact Nat.add_lt_add_right (A.finrank_direction_inf_lt_of_eq_of_ne B heq hne) 1

end AffineSubspace
