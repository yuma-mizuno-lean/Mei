/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.LinearAlgebra.TensorProduct.Filtration
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Multiplicative total-degree tensor filtrations

The total-degree tensor filtration of two multiplicative submodule families is
multiplicative. If both degree-zero terms are full, every term is a two-sided
ideal, even for noncommutative coefficient algebras. These ideals can be used to
form quotient towers and completed tensor products.

The multiplication estimate uses `Submodule.map₂_tmul_mul_le` from Tau Ceti.
The input is expressed as submodule families so it applies to ideal filtrations
after restriction of scalars, without imposing flatness or choosing tensor
representatives.
-/

public section

namespace Mei

open scoped TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
  (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)

/-- The total-degree tensor filtration of multiplicative families is multiplicative. -/
theorem tensorFiltration_mul_le
    (hF : ∀ a b, F a * F b ≤ F (a + b))
    (hG : ∀ a b, G a * G b ≤ G (a + b)) (n m : ℕ) :
    tensorFiltration F G n * tensorFiltration F G m ≤ tensorFiltration F G (n + m) := by
  rw [tensorFiltration_def F G n, tensorFiltration_def F G m]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
  intro c d hcd a b hab
  exact (Submodule.map₂_tmul_mul_le (F a) (F c) (G b) (G d)).trans
    ((Submodule.map₂_le_map₂ (hF a c) (hG b d)).trans
      (map₂_le_tensorFiltration F G (n := n + m) (by omega)))

variable (hF : ∀ a b, F a * F b ≤ F (a + b))
  (hG : ∀ a b, G a * G b ≤ G (a + b))
  (hF0 : F 0 = ⊤) (hG0 : G 0 = ⊤)

/-- Each term of a full, multiplicative tensor filtration is a left ideal. -/
def tensorFiltrationIdeal (n : ℕ) : Ideal (A ⊗[R] B) where
  __ := (tensorFiltration F G n).toAddSubmonoid
  smul_mem' x y hy := by
    have hx : x ∈ tensorFiltration F G 0 := by simp [hF0, hG0]
    simpa using tensorFiltration_mul_le F G hF hG 0 n (Submodule.mul_mem_mul hx hy)

/-- The underlying scalar submodule is exactly the original tensor filtration term. -/
@[simp]
theorem tensorFiltrationIdeal_restrictScalars (n : ℕ) :
    (tensorFiltrationIdeal F G hF hG hF0 hG0 n).restrictScalars R =
      tensorFiltration F G n := (rfl)

/-- Membership in a tensor filtration ideal is membership in its total-degree submodule. -/
@[simp]
theorem mem_tensorFiltrationIdeal {n : ℕ} {x : A ⊗[R] B} :
    x ∈ tensorFiltrationIdeal F G hF hG hF0 hG0 n ↔ x ∈ tensorFiltration F G n :=
  Iff.rfl

/-- The tensor filtration ideals are two-sided, without commutativity of either factor. -/
instance tensorFiltrationIdeal_isTwoSided (n : ℕ) :
    (tensorFiltrationIdeal F G hF hG hF0 hG0 n).IsTwoSided where
  mul_mem_of_left x hy := by
    have hx : x ∈ tensorFiltration F G 0 := by simp [hF0, hG0]
    simpa using tensorFiltration_mul_le F G hF hG n 0 (Submodule.mul_mem_mul hy hx)

/-- Tensor filtration ideals decrease with the order. -/
theorem tensorFiltrationIdeal_antitone :
    Antitone (tensorFiltrationIdeal F G hF hG hF0 hG0) := by
  intro n m h x hx
  exact tensorFiltration_antitone F G h hx

/-- The degree-zero tensor ideal is the full ring. -/
@[simp]
theorem tensorFiltrationIdeal_zero : tensorFiltrationIdeal F G hF hG hF0 hG0 0 = ⊤ := by
  ext x
  simp [hF0, hG0]

/-- Total-degree tensor ideals carry the standard multiplicative filtration. -/
instance tensorFiltrationIdeal_isRingFiltration :
    IsRingFiltration
      (fun n : ℕᵒᵈ => tensorFiltrationIdeal F G hF hG hF0 hG0 n.ofDual)
      (fun n : ℕᵒᵈ => tensorFiltrationIdeal F G hF hG hF0 hG0 (n.ofDual + 1)) where
  mono _ _ h := tensorFiltrationIdeal_antitone F G hF hG hF0 hG0 h
  is_le h := tensorFiltrationIdeal_antitone F G hF hG hF0 hG0 (Nat.succ_le_of_lt h)
  is_sup P n h := h (OrderDual.toDual (n.ofDual + 1)) (by exact Nat.lt_succ_self _)
  one_mem := by simp
  mul_mem i j x y hx hy := tensorFiltration_mul_le F G hF hG i.ofDual j.ofDual
    (Submodule.mul_mem_mul hx hy)

end Mei
