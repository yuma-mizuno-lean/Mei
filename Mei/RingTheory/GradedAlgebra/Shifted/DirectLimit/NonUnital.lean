/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.Shifted.DirectLimit.Assoc

/-!
# The nonunital algebra of global shifted coefficients

The global bilinear product and its associativity law make the existing module
direct limit a nonunital ring. Scalar multiplication commutes and associates with
this product. The additive group and module structures are the original direct-limit
structures; no unit or degree-zero assumption is introduced here.
-/

public section
noncomputable section

namespace Mei.PositiveDegrees

variable {Γ R A : Type*} [AddCommGroup Γ] [CommRing R] [Ring A] [Algebra R A]
  [DecidableEq Γ] (d : PositiveDegrees Γ) (𝒜 : Γ → Submodule R A)
  [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜]

instance instNonUnitalRingShiftedDirectLimit : NonUnitalRing (d.ShiftedDirectLimit 𝒜) where
  __ := (inferInstance : AddCommGroup (d.ShiftedDirectLimit 𝒜))
  mul x y := d.shiftedDirectLimitMul 𝒜 x y
  mul_assoc := d.shiftedDirectLimitMul_assoc 𝒜
  left_distrib a b c := (d.shiftedDirectLimitMul 𝒜 a).map_add b c
  right_distrib a b c := congrArg (fun f => f c) ((d.shiftedDirectLimitMul 𝒜).map_add a b)
  zero_mul a := congrArg (fun f => f a) (d.shiftedDirectLimitMul 𝒜).map_zero
  mul_zero a := (d.shiftedDirectLimitMul 𝒜 a).map_zero

/-- The ring multiplication is the descended completed bilinear product. -/
@[simp]
theorem shiftedDirectLimitMul_eq_mul (x y : d.ShiftedDirectLimit 𝒜) :
    d.shiftedDirectLimitMul 𝒜 x y = x * y := by
  -- The nonunital ring instance defines its `mul` field to be this bilinear map.
  rfl

/-- Multiplication of two chart images is the original completed product in the sum chart. -/
@[simp]
theorem toShiftedDirectLimit_mul (s t : Multiset d.monoid)
    (x : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin s))
    (y : d.ShiftedCoefficients 𝒜 (d.coefficientOrigin t)) :
    d.toShiftedDirectLimit 𝒜 s x * d.toShiftedDirectLimit 𝒜 t y =
      d.toShiftedDirectLimitOfChart 𝒜 (d.coefficientOrigin s + d.coefficientOrigin t)
        (s + t) (d.add_sub_coefficientOrigin_mem (by simp) (by simp))
        (d.shiftedCompletionMul 𝒜 (d.coefficientOrigin s) (d.coefficientOrigin t) x y) := by
  rw [← shiftedDirectLimitMul_eq_mul, shiftedDirectLimitMul_toShiftedDirectLimit,
    shiftedDirectLimitChartMul_apply]

/-- Multiplication of arbitrary-origin chart images is their completed product. -/
@[simp]
theorem toShiftedDirectLimitOfChart_mul (p q : Γ) (s t : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hq : q - d.coefficientOrigin t ∈ d.monoid)
    (x : d.ShiftedCoefficients 𝒜 p) (y : d.ShiftedCoefficients 𝒜 q) :
    d.toShiftedDirectLimitOfChart 𝒜 p s hp x * d.toShiftedDirectLimitOfChart 𝒜 q t hq y =
      d.toShiftedDirectLimitOfChart 𝒜 (p + q) (s + t)
        (d.add_sub_coefficientOrigin_mem hp hq) (d.shiftedCompletionMul 𝒜 p q x y) := by
  rw [← shiftedDirectLimitMul_eq_mul, shiftedDirectLimitMul_toShiftedDirectLimitOfChart]

instance instSMulCommClassShiftedDirectLimit :
    SMulCommClass R (d.ShiftedDirectLimit 𝒜) (d.ShiftedDirectLimit 𝒜) where
  smul_comm r x y := (map_smul (d.shiftedDirectLimitMul 𝒜 x) r y).symm

instance instIsScalarTowerShiftedDirectLimit :
    IsScalarTower R (d.ShiftedDirectLimit 𝒜) (d.ShiftedDirectLimit 𝒜) where
  smul_assoc r x y := by
    simp only [smul_eq_mul]
    rw [← shiftedDirectLimitMul_eq_mul, ← shiftedDirectLimitMul_eq_mul,
      map_smul, LinearMap.smul_apply]

end Mei.PositiveDegrees
