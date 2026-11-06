/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.NonUnital

/-!
# Commutativity of global shifted coefficients

Commutativity of the ambient coefficient algebra passes to the global shifted
coefficient ring, supplying applications such as quantum specialization at `q = 1`.
This does not require a graded unit, a spanning positive monoid, or finite support.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

/-- Commuting finite coefficients give commuting global coefficients, including
infinite families in arbitrary negative charts. No graded unit is required. -/
theorem commute_shiftedDirectLimit (hcomm : ∀ a b : A, Commute a b)
    (x y : d.ShiftedDirectLimit 𝒜) : Commute x y := by
  obtain ⟨s, a, b, ha, hb⟩ := Module.DirectLimit.exists_of₂ x y
  have ha' : d.toShiftedDirectLimit 𝒜 s a = x :=
    (d.toShiftedDirectLimit_apply 𝒜 s a).trans ha
  have hb' : d.toShiftedDirectLimit 𝒜 s b = y :=
    (d.toShiftedDirectLimit_apply 𝒜 s b).trans hb
  rw [commute_iff_eq]
  rw [← ha', ← hb', toShiftedDirectLimit_mul, toShiftedDirectLimit_mul]
  exact congrArg _ (d.shiftedCompletionMul_comm_same_origin 𝒜 hcomm
    (d.coefficientOrigin s) a b)

end Mei.PositiveDegrees
