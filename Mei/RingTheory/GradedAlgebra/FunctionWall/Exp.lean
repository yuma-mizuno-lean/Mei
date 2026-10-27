/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.GradedAlgebra.FunctionWall.Basic
public import Mei.RingTheory.Derivation.Grading
public import Mei.RingTheory.Derivation.Exp
public import Mei.RingTheory.Nilpotent.Log

/-!
# Function walls as finite exponentials

For an integer-graded commutative rational algebra, a weight-zero unit `f` with
nilpotent `f - 1` defines a nilpotent derivation `log(f) D`, where `D` multiplies
weight `i` by `i`. Its finite exponential is the function-wall automorphism,
on positive and negative weights alike. This identifies multiplicative wall
functions with exponential derivation actions in nilpotent coefficient quotients.

The comparison uses `Derivation.exp_smul_toLinearMap_apply`, Mathlib's finite
exponential, and Tau Ceti's finite logarithm and exponential one-parameter group.
The function-wall exponential formula follows Travis Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.GradedAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The logarithmic function-wall derivation `log(f) D`, where `D` is the
integer weight derivation. Its exponential is meaningful when `f - 1` is nilpotent. -/
def functionWallDerivation (f : (𝒜 0)ˣ) : Derivation R A A :=
  IsNilpotent.log (algebraMap (𝒜 0) A (f : 𝒜 0)) •
    gradingDerivation 𝒜 (Int.castAddHom R)

/-- The logarithmic wall derivation is the scalar multiple of the integer
weight derivation by the logarithm of the wall function. -/
theorem functionWallDerivation_def (f : (𝒜 0)ˣ) :
    functionWallDerivation 𝒜 f =
      IsNilpotent.log (algebraMap (𝒜 0) A (f : 𝒜 0)) •
        gradingDerivation 𝒜 (Int.castAddHom R) := (rfl)

/-- The logarithmic wall derivation multiplies a homogeneous element by its
weight times the logarithm of the wall function. -/
theorem functionWallDerivation_apply_of_mem (f : (𝒜 0)ˣ) {i : ℤ} {a : A}
    (ha : a ∈ 𝒜 i) : functionWallDerivation 𝒜 f a =
      IsNilpotent.log (algebraMap (𝒜 0) A (f : 𝒜 0)) * (i • a) := by
  simp only [functionWallDerivation, Derivation.smul_apply,
    gradingDerivation_apply_of_mem 𝒜 _ ha, Int.coe_castAddHom,
    Int.cast_smul_eq_zsmul, smul_eq_mul]

/-- Evaluation on a homogeneous element with its weight in its type. -/
@[simp]
theorem functionWallDerivation_apply (f : (𝒜 0)ˣ) {i : ℤ} (a : 𝒜 i) :
    functionWallDerivation 𝒜 f a =
      IsNilpotent.log (algebraMap (𝒜 0) A (f : 𝒜 0)) * (i • (a : A)) :=
  functionWallDerivation_apply_of_mem 𝒜 f a.property

private theorem gradingDerivation_log (f : (𝒜 0)ˣ) :
    gradingDerivation 𝒜 (Int.castAddHom R)
      (IsNilpotent.log (algebraMap (𝒜 0) A (f : 𝒜 0))) = 0 := by
  rw [IsNilpotent.log_def]
  simp [map_rat_smul, Derivation.leibniz_pow]

/-- A vanishing power of `f - 1` bounds the nilpotency of the logarithmic
function-wall derivation. Thus no finite-rank assumption on the algebra is needed. -/
theorem functionWallDerivation_pow_eq_zero (f : (𝒜 0)ˣ) {k : ℕ}
    (hf : (algebraMap (𝒜 0) A (f : 𝒜 0) - 1) ^ k = 0) :
    (functionWallDerivation 𝒜 f).toLinearMap ^ k = 0 :=
  (gradingDerivation 𝒜 (Int.castAddHom R)).smul_toLinearMap_pow_eq_zero
    (gradingDerivation_log 𝒜 f) (IsNilpotent.pow_log_eq_zero hf)

/-- The function-wall automorphism is the finite exponential of its logarithmic
weight derivation. The unipotence hypothesis is on the ambient algebra, so the
result applies directly to finite-order coefficient quotients. -/
theorem functionWallAction_eq_exp (f : (𝒜 0)ˣ)
    (hf : IsNilpotent (algebraMap (𝒜 0) A (f : 𝒜 0) - 1)) :
    (functionWallAction 𝒜 f).toLinearMap =
      IsNilpotent.exp (functionWallDerivation 𝒜 f).toLinearMap := by
  ext a
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [AlgEquiv.toLinearMap_apply, functionWallAction_apply]
    rw [functionWallDerivation,
      (gradingDerivation 𝒜 (Int.castAddHom R)).exp_smul_toLinearMap_apply
        (gradingDerivation_log 𝒜 f) (IsNilpotent.isNilpotent_log hf)
        (gradingDerivation_apply 𝒜 (Int.castAddHom R) a)]
    simp only [Int.coe_castAddHom, Int.cast_smul_eq_zsmul]
    have he := Units.exp_zsmul_log
      (Units.map (algebraMap (𝒜 0) A).toMonoidHom f) hf i
    rw [← map_zpow (Units.map (algebraMap (𝒜 0) A).toMonoidHom)] at he
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at he
    rw [he, mul_comm]
  | add a b ha hb => simp_all

end Mei.GradedAlgebra
