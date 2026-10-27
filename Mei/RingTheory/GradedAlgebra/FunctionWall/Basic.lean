/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Function walls on graded algebras

A unit `f` in the degree-zero semiring of an integer-graded commutative algebra defines
an algebra automorphism sending a homogeneous element `a` of degree `d` to `a f^d`.
These automorphisms describe function walls: the grading is the weight of a wall
normal, so negative weights require genuine units. They preserve the grading,
compose by multiplication of units, and are natural under graded ring maps,
including maps between different scalar rings.

The construction uses Mathlib's `DirectSum.toAlgebra` and
`DirectSum.decomposeAlgEquiv`. The function-wall formula is the one in Mandel,
*Scattering diagrams, theta functions, and refined tropical curve counts*,
Example 2.1(i), arXiv:1503.06183v5.
-/

public section

namespace Mei.GradedAlgebra

open DirectSum

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

private noncomputable def functionWallHom (f : (𝒜 0)ˣ) : A →ₐ[R] A :=
  (DirectSum.toAlgebra R (fun i => ↥(𝒜 i)) (fun i =>
    (LinearMap.mulRight R (algebraMap (𝒜 0) A (f ^ i : (𝒜 0)ˣ))).comp (𝒜 i).subtype)
    (by simp)
    (by
      intro i j x y
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Submodule.subtype_apply,
        SetLike.coe_gMul, zpow_add, Units.val_mul, map_mul]
      ring)).comp (decomposeAlgEquiv 𝒜).toAlgHom

private theorem functionWallHom_apply (f : (𝒜 0)ˣ) {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) :
    functionWallHom 𝒜 f a = a * algebraMap (𝒜 0) A (f ^ i : (𝒜 0)ˣ) := by
  simp [functionWallHom, decompose_of_mem 𝒜 ha, DirectSum.toAlgebra]

private theorem functionWallHom_mem (f : (𝒜 0)ˣ) {i : ℤ} {a : A} (ha : a ∈ 𝒜 i) :
    functionWallHom 𝒜 f a ∈ 𝒜 i := by
  rw [functionWallHom_apply 𝒜 f ha]
  simpa only [add_zero, SetLike.GradeZero.algebraMap_apply] using
    SetLike.GradedMul.mul_mem ha (f ^ i : (𝒜 0)ˣ).val.property

private theorem functionWallHom_mul (f g : (𝒜 0)ˣ) (a : A) :
    functionWallHom 𝒜 f (functionWallHom 𝒜 g a) = functionWallHom 𝒜 (f * g) a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [functionWallHom_apply 𝒜 f (functionWallHom_mem 𝒜 g a.property),
      functionWallHom_apply 𝒜 g a.property, functionWallHom_apply 𝒜 (f * g) a.property]
    rw [_root_.mul_zpow f g i]
    simp only [Units.val_mul, map_mul]
    ring
  | add a b ha hb => simp [ha, hb]

private theorem functionWallHom_one (a : A) : functionWallHom 𝒜 1 a = a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => simp [functionWallHom_apply 𝒜 1 a.property]
  | add a b ha hb => simp [ha, hb]

/-- The function-wall automorphism multiplying weight `d` by the `d`-th power of a
unit of the weight-zero ring. Scalars have weight zero, so it is an algebra automorphism. -/
noncomputable def functionWallAction (f : (𝒜 0)ˣ) : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (functionWallHom 𝒜 f) (functionWallHom 𝒜 f⁻¹)
    (by ext a; simp [functionWallHom_mul, functionWallHom_one])
    (by ext a; simp [functionWallHom_mul, functionWallHom_one])

/-- The function-wall formula on an element of known weight, positive or negative. -/
theorem functionWallAction_apply_of_mem {i : ℤ} {a : A} (f : (𝒜 0)ˣ) (ha : a ∈ 𝒜 i) :
    functionWallAction 𝒜 f a = a * algebraMap (𝒜 0) A (f ^ i : (𝒜 0)ˣ) :=
  functionWallHom_apply 𝒜 f ha

/-- The function-wall formula on a homogeneous element whose weight is part of its type. -/
@[simp]
theorem functionWallAction_apply {i : ℤ} (f : (𝒜 0)ˣ) (a : 𝒜 i) :
    functionWallAction 𝒜 f a = (a : A) * algebraMap (𝒜 0) A (f ^ i : (𝒜 0)ˣ) :=
  functionWallAction_apply_of_mem 𝒜 f a.property

/-- Function walls preserve every weight space. -/
theorem functionWallAction_mem {i : ℤ} {a : A} (f : (𝒜 0)ˣ) (ha : a ∈ 𝒜 i) :
    functionWallAction 𝒜 f a ∈ 𝒜 i :=
  functionWallHom_mem 𝒜 f ha

/-- The constant function one acts trivially. -/
@[simp]
theorem functionWallAction_one : functionWallAction 𝒜 1 = AlgEquiv.refl := by
  ext a
  exact functionWallHom_one 𝒜 a

/-- Multiplication of weight-zero units gives composition of their function walls. -/
@[simp]
theorem functionWallAction_mul (f g : (𝒜 0)ˣ) :
    functionWallAction 𝒜 (f * g) = (functionWallAction 𝒜 g).trans (functionWallAction 𝒜 f) := by
  ext a
  exact (functionWallHom_mul 𝒜 f g a).symm

/-- Inverting a wall function inverts its automorphism. -/
@[simp]
theorem functionWallAction_inv (f : (𝒜 0)ˣ) :
    functionWallAction 𝒜 f⁻¹ = (functionWallAction 𝒜 f).symm := by
  simp [functionWallAction, AlgEquiv.ofAlgHom_symm]

/-- A function wall preserves, and reflects, membership in each weight space. -/
@[simp]
theorem functionWallAction_mem_iff {i : ℤ} {a : A} (f : (𝒜 0)ˣ) :
    functionWallAction 𝒜 f a ∈ 𝒜 i ↔ a ∈ 𝒜 i := by
  constructor
  · intro ha
    have h := functionWallAction_mem 𝒜 f⁻¹ ha
    simpa using h
  · exact functionWallAction_mem 𝒜 f

/-- Each homogeneous component is multiplied by the corresponding power of the wall
function. This formula also applies to elements with several nonzero components. -/
@[simp]
theorem decompose_functionWallAction (f : (𝒜 0)ˣ) (a : A) (i : ℤ) :
    (decompose 𝒜 (functionWallAction 𝒜 f a) i : A) =
      (decompose 𝒜 a i : A) * algebraMap (𝒜 0) A (f ^ i : (𝒜 0)ˣ) := by
  let φ : 𝒜 →+*ᵍ 𝒜 :=
    { (functionWallAction 𝒜 f).toRingHom with
      map_mem := functionWallAction_mem 𝒜 f }
  calc
    _ = φ (decompose 𝒜 a i) := (φ.map_directSumDecompose (x := a) (i := i)).symm
    _ = _ := functionWallAction_apply 𝒜 f (decompose 𝒜 a i)

section Naturality

variable {S B : Type*} [CommSemiring S] [CommSemiring B] [Algebra S B]
  (ℬ : ℤ → Submodule S B) [GradedAlgebra ℬ]

/-- Graded ring maps intertwine function walls with the image of their weight-zero
unit. In particular, this applies to graded quotient maps in truncation towers. -/
@[simp]
theorem map_functionWallAction (φ : 𝒜 →+*ᵍ ℬ) (f : (𝒜 0)ˣ) (a : A) :
    φ (functionWallAction 𝒜 f a) =
      functionWallAction ℬ (Units.map φ.gradedZeroRingHom.toMonoidHom f)
        (φ a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    have hφ : φ (a : A) ∈ ℬ i := φ.map_mem a.property
    rw [functionWallAction_apply_of_mem 𝒜 f a.property,
      functionWallAction_apply_of_mem ℬ _ hφ]
    simp only [map_mul, SetLike.GradeZero.algebraMap_apply]
    rw [← map_zpow]
    rfl
  | add a b ha hb => simp [ha, hb]

end Naturality

end Mei.GradedAlgebra
