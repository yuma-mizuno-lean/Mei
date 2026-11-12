/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.CompletedGroup.Basic
public import Mathlib.Algebra.Group.Support

/-!
# Supports of completed group projections

If an element is nonidentity at one order, its projection at every finer order
is also nonidentity.
-/

public section

open CategoryTheory Opposite

universe u

namespace TauCeti.CompletedGroup

variable {F : ℕᵒᵖ ⥤ GrpCat.{u}}

/-- The support of a family's projections grows with the cutoff. -/
theorem monotone_mulSupport_projection {ι : Type*} (x : ι → completedGroup F) :
    Monotone (fun k => Function.mulSupport fun i => projection k (x i)) := by
  intro k l hkl i
  simp only [Function.mem_mulSupport]
  intro hi he
  apply hi
  rw [← map_projection k l hkl (x i), he, map_one]

end TauCeti.CompletedGroup
