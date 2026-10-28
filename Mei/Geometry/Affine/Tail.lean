/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Abel

/-!
# Incoming germs of affine lines

An affine map from the real line is determined by its germ at negative infinity.
Thus restricting an affine representative to a smaller incoming half-line does
not change the represented germ. These are representative laws for incoming
affine tails; coefficient, source and chart/deck identifications are separate data.
The construction uses existing affine maps and filter germs without a new carrier.
-/

public section

namespace AffineMap

open Filter Set

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Affine representatives with the same incoming germ agree everywhere. -/
theorem eq_of_eventuallyEq_atBot {f g : ℝ →ᵃ[ℝ] P}
    (h : (f : ℝ → P) =ᶠ[atBot] g) : f = g := by
  obtain ⟨a, ha⟩ := eventually_atBot.mp h
  have hs := congrArg₂ (fun x y : P => x -ᵥ y)
    (ha a le_rfl) (ha (a - 1) (sub_le_self _ zero_le_one))
  rw [← f.linear_apply_vsub, ← g.linear_apply_vsub] at hs
  have hdiff : a - (a - 1) = (1 : ℝ) := by abel
  simp only [vsub_eq_sub, hdiff] at hs
  exact ext_linear (LinearMap.ext_ring hs) (ha a le_rfl)

/-- Equality of incoming affine germs is precisely equality of their representatives. -/
@[simp]
theorem eventuallyEq_atBot_iff {f g : ℝ →ᵃ[ℝ] P} :
    (f : ℝ → P) =ᶠ[atBot] g ↔ f = g :=
  ⟨eq_of_eventuallyEq_atBot, fun h => h ▸ Filter.EventuallyEq.rfl⟩

end AffineMap
