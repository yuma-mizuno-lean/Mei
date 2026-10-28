/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.NormalForm
public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Order.Nonneg.Basic

/-!
# Incoming lifts for a slab

The two Laurent chambers of `R[X,Y]/(XY-a)` have incoming lifts
`c T^n ↦ c X^n` and `c T^n ↦ c Y^n` for nonnegative `n`.
Their opposite images are `c a^n T^(-n)`. These lifts define a
`GradedCorrespondence` for the normal-weight gradings of the chambers, including
weight zero on both sides. The span is jointly injective even when `a` is a zero
divisor, and its two lifts agree on weight zero.

Here `R` may itself be a tangential monoid algebra; the grading in this file records
only the Laurent exponent, retaining the entire tangential coefficient in each piece.
The left and right Laurent variables each have degree one in their own chamber.

We use `NodeAlgebra.leftLaurentMap`, `NodeAlgebra.rightLaurentMap` and their
joint injectivity from the normal-form construction, and Mathlib's
`AddMonoidAlgebra.grade` decomposition. The slab interpretation follows
Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Definitions 3.1–3.3, arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra AddMonoidAlgebra LaurentPolynomial

variable {R : Type*} [CommRing R] (a : R)

/-- Lift a nonnegative Laurent-weight piece through the chosen nodal coordinate.
Coordinate `0` lifts from the left chamber and coordinate `1` from the right. -/
def incomingLift (i : Fin 2) (n : {n : ℤ | 0 ≤ n}) :
    grade R n.val →ₗ[R] NodeAlgebra R a :=
  (LinearMap.toSpanSingleton R _ (coord a i ^ n.val.toNat)).comp
    (((Finsupp.lapply n.val).comp (coeffLinearEquiv R).toLinearMap).comp
      (grade R n.val).subtype)

/-- An incoming lift multiplies the coordinate power by the input coefficient. -/
theorem incomingLift_apply (i : Fin 2) (n : {n : ℤ | 0 ≤ n}) (u : grade R n.val) :
    incomingLift a i n u = u.val.coeff n.val • coord a i ^ n.val.toNat := (rfl)

@[simp]
theorem incomingLift_C_mul_T (i : Fin 2) (n : ℕ) (c : R) :
    incomingLift a i (Nat.cast n : Nonneg ℤ)
      ⟨C c * T n, by rw [← single_eq_C_mul_T]; exact single_mem_grade _ _⟩ =
        c • coord a i ^ n := by
  simp only [incomingLift_apply, Nonneg.coe_natCast, ← single_eq_C_mul_T,
    coeff_single, Finsupp.single_eq_same, Int.toNat_natCast]

/-- The left incoming lift is a section of the left chamber map. -/
@[simp]
theorem leftLaurentMap_incomingLift (n : {n : ℤ | 0 ≤ n}) (u : grade R n.val) :
    leftLaurentMap a (incomingLift a 0 n u) = u := by
  obtain ⟨c, hc⟩ := (mem_grade_iff' R n.val u.val).mp u.property
  have hu : u.val = single n.val c := hc.symm
  simp [incomingLift_apply, hu, Int.toNat_of_nonneg n.property,
    Algebra.smul_def, ← C_eq_algebraMap, C, T, single_mul_single, -single_eq_C_mul_T]

/-- The right incoming lift is a section of the right chamber map. -/
@[simp]
theorem rightLaurentMap_incomingLift (n : {n : ℤ | 0 ≤ n}) (u : grade R n.val) :
    rightLaurentMap a (incomingLift a 1 n u) = u := by
  obtain ⟨c, hc⟩ := (mem_grade_iff' R n.val u.val).mp u.property
  have hu : u.val = single n.val c := hc.symm
  simp [incomingLift_apply, hu, Int.toNat_of_nonneg n.property,
    Algebra.smul_def, ← C_eq_algebraMap, C, T, single_mul_single, -single_eq_C_mul_T]

/-- Crossing from the left multiplies the coefficient by `a^n` and reverses
the Laurent exponent. This formula requires no invertibility of `a`. -/
theorem rightLaurentMap_incomingLift_zero (n : {n : ℤ | 0 ≤ n})
    (u : grade R n.val) :
    rightLaurentMap a (incomingLift a 0 n u) =
      single (-n.val) (u.val.coeff n.val * a ^ n.val.toNat) := by
  simp [incomingLift_apply, ← C_eq_algebraMap, Algebra.smul_def,
    C, T, single_mul_single, -single_eq_C_mul_T, Int.toNat_of_nonneg n.property]

/-- Crossing from the right has the same coefficient multiplier as crossing
from the left, with the two chamber variables exchanged. -/
theorem leftLaurentMap_incomingLift_one (n : {n : ℤ | 0 ≤ n})
    (u : grade R n.val) :
    leftLaurentMap a (incomingLift a 1 n u) =
      single (-n.val) (u.val.coeff n.val * a ^ n.val.toNat) := by
  simp [incomingLift_apply, ← C_eq_algebraMap, Algebra.smul_def,
    C, T, single_mul_single, -single_eq_C_mul_T, Int.toNat_of_nonneg n.property]

/-- Both chambers lift a weight-zero coefficient to the same scalar. -/
@[simp]
theorem incomingLift_zero (i : Fin 2) (u : grade R (0 : ℤ)) :
    incomingLift a i ⟨0, by simp⟩ u = algebraMap R (NodeAlgebra R a) (u.val.coeff 0) := by
  simp [incomingLift_apply, Algebra.smul_def]

/-- Incoming lifts preserve products of admissible homogeneous coefficients. -/
theorem incomingLift_mul (i : Fin 2) (n m : {n : ℤ | 0 ≤ n})
    (u : grade R n.val) (v : grade R m.val) :
    incomingLift a i
      ⟨n.val + m.val, add_nonneg (a := n.val) (b := m.val) n.property m.property⟩
      ⟨u.val * v.val, SetLike.mul_mem_graded u.property v.property⟩ =
        incomingLift a i n u * incomingLift a i m v := by
  obtain ⟨c, hc⟩ := (mem_grade_iff' R n.val u.val).mp u.property
  obtain ⟨d, hd⟩ := (mem_grade_iff' R m.val v.val).mp v.property
  simp [incomingLift_apply, ← hc, ← hd, lsingle_apply, single_mul_single,
    Int.toNat_add n.property m.property, pow_add, mul_smul_mul_comm,
    -single_eq_C_mul_T]

/-- The normal-weight slab correspondence. Nonnegative powers are admissible
from either chamber; the two zero-weight lifts agree. -/
def normalWeightCorrespondence :
    GradedCorrespondence (B := NodeAlgebra R a) (grade R : ℤ → _) (grade R : ℤ → _)
      {n | 0 ≤ n} {n | 0 ≤ n} where
  left := (leftLaurentMap a).toLinearMap
  right := (rightLaurentMap a).toLinearMap
  liftLeft := incomingLift a 0
  liftRight := incomingLift a 1
  left_liftLeft _ := by ext; simp
  right_liftRight _ := by ext; simp

@[simp]
theorem normalWeightCorrespondence_left :
    (normalWeightCorrespondence a).left = (leftLaurentMap a).toLinearMap := (rfl)

@[simp]
theorem normalWeightCorrespondence_right :
    (normalWeightCorrespondence a).right = (rightLaurentMap a).toLinearMap := (rfl)

@[simp]
theorem normalWeightCorrespondence_liftLeft (n : {n : ℤ | 0 ≤ n}) :
    (normalWeightCorrespondence a).liftLeft n = incomingLift a 0 n := (rfl)

@[simp]
theorem normalWeightCorrespondence_liftRight (n : {n : ℤ | 0 ≤ n}) :
    (normalWeightCorrespondence a).liftRight n = incomingLift a 1 n := (rfl)

/-- The opposite image of an incoming coefficient is concentrated in weight `-n`. -/
theorem normalWeightCorrespondence_transfer (n : {n : ℤ | 0 ≤ n}) (j : ℤ)
    (u : grade R n.val) :
    ((normalWeightCorrespondence a).transfer n j u : R[T;T⁻¹]) =
      if j = -n.val then single (-n.val) (u.val.coeff n.val * a ^ n.val.toNat) else 0 := by
  rw [GradedCorrespondence.transfer_apply, normalWeightCorrespondence_right,
    normalWeightCorrespondence_liftLeft]
  simp only [AlgHom.toLinearMap_apply, rightLaurentMap_incomingLift_zero,
    grade.decompose_single]
  by_cases h : j = -n.val
  · subst j
    simp
  · simp [DirectSum.of_eq_of_ne _ _ _ h, h]

/-- The reverse transfer has the same formula, in the other Laurent variable. -/
theorem normalWeightCorrespondence_symm_transfer (n : {n : ℤ | 0 ≤ n}) (j : ℤ)
    (u : grade R n.val) :
    ((normalWeightCorrespondence a).symm.transfer n j u : R[T;T⁻¹]) =
      if j = -n.val then single (-n.val) (u.val.coeff n.val * a ^ n.val.toNat) else 0 := by
  rw [GradedCorrespondence.transfer_apply, GradedCorrespondence.symm_right,
    GradedCorrespondence.symm_liftLeft, normalWeightCorrespondence_left,
    normalWeightCorrespondence_liftRight]
  simp only [AlgHom.toLinearMap_apply, leftLaurentMap_incomingLift_one,
    grade.decompose_single]
  by_cases h : j = -n.val
  · subst j
    simp
  · simp [DirectSum.of_eq_of_ne _ _ _ h, h]

end Mei.NodeAlgebra
