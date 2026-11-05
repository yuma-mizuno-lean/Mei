/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.GradedModule.Shifted.DirectLimit.Support
public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Unit

/-!
# Products of global supports and the positive coefficient subalgebra

Products of global coefficients supported in two translates belong to the
sum translate. In particular, the zero-origin coefficient chart is a subalgebra
of the global algebra. Its elements are precisely the families vanishing outside
the positive monoid; no finite-support or positive-difference spanning assumption
is needed.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜]

section Multiplication

variable [SetLike.GradedMul 𝒜]

/-- Multiplying two chart images produces a coefficient in the sum-support chart. -/
theorem mul_mem_range_toShiftedDirectLimitOfChart (p q : Γ)
    (s t v : Multiset d.monoid)
    (hps : p - d.coefficientOrigin s ∈ d.monoid)
    (hqt : q - d.coefficientOrigin t ∈ d.monoid)
    (hpqv : p + q - d.coefficientOrigin v ∈ d.monoid)
    {x y : d.ShiftedDirectLimit 𝒜}
    (hx : x ∈ LinearMap.range (d.toShiftedDirectLimitOfChart 𝒜 p s hps))
    (hy : y ∈ LinearMap.range (d.toShiftedDirectLimitOfChart 𝒜 q t hqt)) :
    x * y ∈ LinearMap.range (d.toShiftedDirectLimitOfChart 𝒜 (p + q) v hpqv) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  refine ⟨d.shiftedCompletionMul 𝒜 p q a b, ?_⟩
  rw [toShiftedDirectLimitOfChart_mul]
  simpa only [shiftedCompletedInclusion_refl] using
    d.toShiftedDirectLimitOfChart_inclusion 𝒜 (p + q) (p + q) (by simp) (s + t) v
      (d.add_sub_coefficientOrigin_mem hps hqt) hpqv (d.shiftedCompletionMul 𝒜 p q a b)

end Multiplication

variable [SetLike.GradedMonoid 𝒜]

private theorem one_mem_zero_chart :
    (1 : d.ShiftedDirectLimit 𝒜) ∈ LinearMap.range
      (d.toShiftedDirectLimitOfChart 𝒜 0 0 d.zero_coefficientOrigin_mem) := by
  apply (d.mem_range_toShiftedDirectLimitOfChart_iff 𝒜 0 0 d.zero_coefficientOrigin_mem 1).mpr
  intro u hu
  rw [shiftedDirectLimitComponents_one]
  apply Subtype.ext
  have h0 : (0 : Γ) ≠ u := by
    intro h
    apply hu
    rw [← h]
    simp
  exact DirectSum.decompose_of_mem_ne 𝒜 SetLike.GradedOne.one_mem h0

/-- Global coefficients supported in the positive monoid, as a subalgebra. -/
def positiveCoefficientSubalgebra : Subalgebra R (d.ShiftedDirectLimit 𝒜) :=
  (LinearMap.range
    (d.toShiftedDirectLimitOfChart 𝒜 0 0 d.zero_coefficientOrigin_mem)).toSubalgebra
      (d.one_mem_zero_chart 𝒜) (by
        intro x y hx hy
        have hsum : (0 : Γ) + 0 - d.coefficientOrigin (0 : Multiset d.monoid) ∈ d.monoid := by
          simpa only [zero_add] using d.zero_coefficientOrigin_mem
        have hxy := d.mul_mem_range_toShiftedDirectLimitOfChart 𝒜 0 0 0 0 0
          d.zero_coefficientOrigin_mem d.zero_coefficientOrigin_mem hsum hx hy
        apply (d.mem_range_toShiftedDirectLimitOfChart_iff 𝒜 0 0
          d.zero_coefficientOrigin_mem (x * y)).mpr
        intro u hu
        exact (d.mem_range_toShiftedDirectLimitOfChart_iff 𝒜 (0 + 0) 0 hsum
          (x * y)).mp hxy u (by simpa only [zero_add] using hu))

/-- The positive subalgebra is exactly the image submodule of the zero-origin chart. -/
@[simp]
theorem positiveCoefficientSubalgebra_toSubmodule :
    (d.positiveCoefficientSubalgebra 𝒜).toSubmodule =
      LinearMap.range (d.toShiftedDirectLimitOfChart 𝒜 0 0 d.zero_coefficientOrigin_mem) := by
  -- `Submodule.toSubalgebra` retains the supplied submodule as its underlying carrier.
  rfl

/-- Positive global coefficients are characterized by vanishing outside the positive monoid. -/
theorem mem_positiveCoefficientSubalgebra_iff (x : d.ShiftedDirectLimit 𝒜) :
    x ∈ d.positiveCoefficientSubalgebra 𝒜 ↔
      ∀ u, u ∉ d.monoid → d.shiftedDirectLimitComponents 𝒜 x u = 0 := by
  -- A subalgebra and its underlying submodule have the same membership predicate.
  change x ∈ (d.positiveCoefficientSubalgebra 𝒜).toSubmodule ↔ _
  rw [positiveCoefficientSubalgebra_toSubmodule, mem_range_toShiftedDirectLimitOfChart_iff]
  simp only [sub_zero]

end Mei.PositiveDegrees
