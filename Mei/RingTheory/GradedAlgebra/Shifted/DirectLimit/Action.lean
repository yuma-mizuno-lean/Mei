/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Action
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.NonUnital

/-!
# Multiplicative actions on global shifted coefficients

A compatible action on translated completions preserves the global product when
it preserves the mixed product of every pair of translated completions. This
shared descent applies to both completed Lie actions and quantum ray actions.
-/

public section

open TauCeti (PositiveDegrees)
noncomputable section

namespace TauCeti.PositiveDegrees

open Mei

variable {Γ R A G : Type*} [AddCommGroup Γ] [CommRing R]
  [Ring A] [Algebra R A] [DecidableEq Γ] [Monoid G]
  (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [SetLike.GradedMul 𝒜]
  (act : ∀ p, G →* (d.ShiftedCoefficients 𝒜 p ≃ₗ[R] d.ShiftedCoefficients 𝒜 p))
  (hact : ∀ (p q : Γ) (hpq : p - q ∈ d.monoid) (g : G)
    (x : d.ShiftedCoefficients 𝒜 p),
    d.shiftedCompletedInclusion 𝒜 p q hpq (act p g x) =
      act q g (d.shiftedCompletedInclusion 𝒜 p q hpq x))

/-- Preservation of chartwise mixed products descends to the global product. -/
@[simp]
theorem shiftedDirectLimitAction_map_mul
    (hmul : ∀ (p q : Γ) (g : G) (x : d.ShiftedCoefficients 𝒜 p)
      (y : d.ShiftedCoefficients 𝒜 q),
      act (p + q) g (d.shiftedCompletionMul 𝒜 p q x y) =
        d.shiftedCompletionMul 𝒜 p q (act p g x) (act q g y))
    (g : G) (x y : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitAction 𝒜 act hact g (x * y) =
      d.shiftedDirectLimitAction 𝒜 act hact g x *
        d.shiftedDirectLimitAction 𝒜 act hact g y := by
  obtain ⟨s, a, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  obtain ⟨t, b, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 y
  rw [toShiftedDirectLimit_mul, shiftedDirectLimitAction_toShiftedDirectLimitOfChart,
    hmul, shiftedDirectLimitAction_toShiftedDirectLimit,
    shiftedDirectLimitAction_toShiftedDirectLimit, toShiftedDirectLimit_mul]

end TauCeti.PositiveDegrees
