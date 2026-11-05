/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit

/-!
# Associativity of global shifted coefficient multiplication

Multiplication on the global coefficient module is associative.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

/-- Multiplication of global coefficients is associative. -/
theorem shiftedDirectLimitMul_assoc (x y z : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMul 𝒜 (d.shiftedDirectLimitMul 𝒜 x y) z =
      d.shiftedDirectLimitMul 𝒜 x (d.shiftedDirectLimitMul 𝒜 y z) := by
  obtain ⟨s, x, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 x
  obtain ⟨t, y, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 y
  obtain ⟨u, z, rfl⟩ := d.exists_toShiftedDirectLimit 𝒜 z
  let p := d.coefficientOrigin s
  let q := d.coefficientOrigin t
  let r := d.coefficientOrigin u
  have hl : (p + q) + r - d.coefficientOrigin ((s + t) + u) ∈ d.monoid := by
    rw [coefficientOrigin_add, coefficientOrigin_add]
    simp only [p, q, r, sub_self, zero_mem]
  have hr : p + (q + r) - d.coefficientOrigin (s + (t + u)) ∈ d.monoid := by
    rw [coefficientOrigin_add, coefficientOrigin_add]
    simp only [p, q, r, sub_self, zero_mem]
  have hc := d.toShiftedDirectLimitOfChart_cast 𝒜 ((p + q) + r) (p + (q + r))
    (add_assoc p q r) ((s + t) + u) (s + (t + u)) hl hr
    (d.shiftedCompletionMul 𝒜 (p + q) r (d.shiftedCompletionMul 𝒜 p q x y) z)
  have ha := congrArg (d.toShiftedDirectLimitOfChart 𝒜 (p + (q + r)) (s + (t + u)) hr)
    (d.shiftedCompletionMul_assoc 𝒜 p q r x y z)
  simp only [toShiftedDirectLimit_eq_ofChart, shiftedDirectLimitMul_toShiftedDirectLimitOfChart]
  exact hc.symm.trans ha

end Mei.PositiveDegrees
