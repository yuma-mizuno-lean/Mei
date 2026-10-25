/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Tensor products of ideals

The image of the tensor product of two left ideals in the tensor product algebra
is a left ideal. If both ideals are two-sided, so is their tensor image. These
ideals multiply compatibly with multiplication in each factor, providing the
terms used in total-degree tensor filtrations.

The underlying image is Mathlib's `Submodule.map₂` of `TensorProduct.mk`, or
equivalently the range of `TensorProduct.mapIncl`. Multiplicativity uses Tau
Ceti's `Submodule.map₂_tmul_mul_le`. No flatness or commutativity of the two
algebras is required.
-/

public section

open scoped TensorProduct

namespace Ideal

variable (R : Type*) {A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]

/-- The image of the tensor product of two left ideals in the tensor product algebra. -/
noncomputable def tensorProduct (I : Ideal A) (J : Ideal B) : Ideal (A ⊗[R] B) where
  __ := (Submodule.map₂ (TensorProduct.mk R A B)
    (I.restrictScalars R) (J.restrictScalars R)).toAddSubmonoid
  smul_mem' z x hx := by
    rw [← TensorProduct.range_mapIncl] at hx
    obtain ⟨t, rfl⟩ := hx
    induction z with
    | tmul a b =>
      induction t with
      | tmul i j =>
        simpa using Submodule.apply_mem_map₂ (TensorProduct.mk R A B)
          (I.mul_mem_left a i.property) (J.mul_mem_left b j.property)
      | add t u ht hu => simpa [mul_add] using Submodule.add_mem _ ht hu
    | add z w hz hw => simpa [add_mul] using Submodule.add_mem _ hz hw

/-- The tensor ideal has the usual tensor image as its underlying scalar submodule. -/
@[simp]
theorem tensorProduct_restrictScalars (I : Ideal A) (J : Ideal B) :
    (I.tensorProduct R J).restrictScalars R =
      Submodule.map₂ (TensorProduct.mk R A B) (I.restrictScalars R) (J.restrictScalars R) :=
  (rfl)

/-- Membership in a tensor ideal means being the image of a tensor of ideal elements. -/
theorem mem_tensorProduct_iff (I : Ideal A) (J : Ideal B) (x : A ⊗[R] B) :
    x ∈ I.tensorProduct R J ↔
      ∃ t : (I.restrictScalars R) ⊗[R] (J.restrictScalars R),
        TensorProduct.mapIncl (I.restrictScalars R) (J.restrictScalars R) t = x := by
  rw [← Submodule.restrictScalars_mem R, tensorProduct_restrictScalars,
    ← TensorProduct.range_mapIncl]
  rfl

/-- A pure tensor of elements of the two ideals belongs to their tensor ideal. -/
theorem tmul_mem_tensorProduct {I : Ideal A} {J : Ideal B} {a : A} {b : B}
    (ha : a ∈ I) (hb : b ∈ J) : a ⊗ₜ[R] b ∈ I.tensorProduct R J :=
  Submodule.apply_mem_map₂ (TensorProduct.mk R A B) ha hb

/-- To contain a tensor ideal it suffices to contain its pure tensors. -/
theorem tensorProduct_le_iff (I : Ideal A) (J : Ideal B) (K : Ideal (A ⊗[R] B)) :
    I.tensorProduct R J ≤ K ↔ ∀ a ∈ I, ∀ b ∈ J, a ⊗ₜ[R] b ∈ K := by
  exact Submodule.map₂_le (f := TensorProduct.mk R A B)
    (p := I.restrictScalars R) (q := J.restrictScalars R) (r := K.restrictScalars R)

/-- Tensor ideals are monotone in both factors. -/
theorem tensorProduct_mono {I I' : Ideal A} {J J' : Ideal B}
    (hI : I ≤ I') (hJ : J ≤ J') : I.tensorProduct R J ≤ I'.tensorProduct R J' :=
  Submodule.map₂_le_map₂ hI hJ

/-- Tensoring the whole algebras gives the whole tensor product algebra. -/
@[simp]
theorem tensorProduct_top_top :
    (⊤ : Ideal A).tensorProduct R (⊤ : Ideal B) = ⊤ := by
  apply (Submodule.restrictScalars_injective R)
  simp [TensorProduct.map₂_mk_top_top_eq_top]

/-- Tensoring a zero ideal on the left gives the zero ideal. -/
@[simp]
theorem tensorProduct_bot_left (J : Ideal B) :
    (⊥ : Ideal A).tensorProduct R J = ⊥ := by
  apply (Submodule.restrictScalars_injective R)
  simp

/-- Tensoring a zero ideal on the right gives the zero ideal. -/
@[simp]
theorem tensorProduct_bot_right (I : Ideal A) :
    I.tensorProduct R (⊥ : Ideal B) = ⊥ := by
  apply (Submodule.restrictScalars_injective R)
  simp

/-- Tensor images of two-sided ideals are two-sided. -/
instance tensorProduct_isTwoSided (I : Ideal A) (J : Ideal B) [I.IsTwoSided] [J.IsTwoSided] :
    (I.tensorProduct R J).IsTwoSided where
  mul_mem_of_left z hx := by
    obtain ⟨t, rfl⟩ := (mem_tensorProduct_iff R I J _).mp hx
    clear hx
    induction z with
    | tmul a b =>
      induction t with
      | tmul i j =>
        simpa using tmul_mem_tensorProduct R
          (I.mul_mem_right a i.property) (J.mul_mem_right b j.property)
      | add t u ht hu => simpa [add_mul] using (I.tensorProduct R J).add_mem ht hu
    | add z w hz hw => simpa [mul_add] using (I.tensorProduct R J).add_mem hz hw

/-- Products of tensor ideals lie in the tensor ideal of the products. -/
theorem tensorProduct_mul_le (I I' : Ideal A) (J J' : Ideal B) :
    I.tensorProduct R J * I'.tensorProduct R J' ≤ (I * I').tensorProduct R (J * J') := by
  -- Restricting scalars identifies ideal multiplication with submodule multiplication.
  apply (Submodule.restrictScalars_le R).mp
  simp only [Submodule.restrictScalars_mul, tensorProduct_restrictScalars]
  exact Submodule.map₂_tmul_mul_le _ _ _ _

end Ideal
