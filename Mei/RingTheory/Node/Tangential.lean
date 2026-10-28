/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Correspondence
public import Mei.RingTheory.Node.ScalarTower
public import Mei.Algebra.MonoidAlgebra.Grading

/-!
# Slab correspondences with tangential exponents

For `a : R[M]`, the two chambers of `R[M][X,Y]/(XY-a)` are graded by
`ℤ × M`, recording the Laurent exponent and the tangential exponent separately.
The incoming lift of `c z^m T^n` is `c z^m X^n` or `c z^m Y^n` for `n ≥ 0`.
Crossing replaces it by `c z^m a^n T^(-n)`. Its individual tangential components
are the homogeneous transfers, including when `a` is not homogeneous.

The construction refines `normalWeightCorrespondence` using Mathlib's
`AddMonoidAlgebra.curryAlgEquiv`, retaining its existing chamber maps and incoming
lifts. The slab interpretation follows Gross–Hacking–Siebert, *Theta functions
on varieties with effective anti-canonical class*, Definitions 3.1–3.3,
arXiv:1601.07081v4.
-/

public section

noncomputable section

namespace Mei.NodeAlgebra

open TauCeti TauCeti.NodeAlgebra AddMonoidAlgebra LaurentPolynomial
open scoped TauCeti.NodeAlgebra

variable {R M : Type*} [CommRing R] [AddCommMonoid M] (a : R[M])

/-- The left chamber map with both normal and tangential exponents retained. -/
def exponentLeftMap : NodeAlgebra R[M] a →ₐ[R] R[ℤ × M] :=
  (curryAlgEquiv R).symm.toAlgHom.comp ((leftLaurentMap a).restrictScalars R)

/-- The right chamber map with both normal and tangential exponents retained. -/
def exponentRightMap : NodeAlgebra R[M] a →ₐ[R] R[ℤ × M] :=
  (curryAlgEquiv R).symm.toAlgHom.comp ((rightLaurentMap a).restrictScalars R)

@[simp]
theorem curry_exponentLeftMap (x : NodeAlgebra R[M] a) :
    curryAlgEquiv R (exponentLeftMap a x) = leftLaurentMap a x :=
  (curryAlgEquiv R).apply_symm_apply _

@[simp]
theorem curry_exponentRightMap (x : NodeAlgebra R[M] a) :
    curryAlgEquiv R (exponentRightMap a x) = rightLaurentMap a x :=
  (curryAlgEquiv R).apply_symm_apply _

/-- The full-exponent chamber maps remain jointly injective. -/
theorem exponentMaps_jointly_injective :
    Function.Injective (fun x : NodeAlgebra R[M] a =>
      (exponentLeftMap a x, exponentRightMap a x)) := by
  intro x y h
  apply laurentMaps_jointly_injective a
  simpa using congrArg (fun p => (curryAlgEquiv R p.1, curryAlgEquiv R p.2)) h

/-- Lift a fully homogeneous incoming coefficient using the existing normal-weight lift. -/
def exponentIncomingLift (i : Fin 2) (p : {p : ℤ × M | 0 ≤ p.1}) :
    grade R p.val →ₗ[R] NodeAlgebra R[M] a :=
  ((incomingLift a i ⟨p.val.1, p.property⟩).restrictScalars R).comp
    (((curryAlgEquiv R).toLinearMap.comp (grade R p.val).subtype).codRestrict
      ((grade R[M] p.val.1).restrictScalars R)
      (fun u => curryAlgEquiv_mem_grade p.val u.val u.property))

/-- A fully homogeneous lift is the normal-weight lift of its curried input. -/
theorem exponentIncomingLift_apply (i : Fin 2) (p : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) :
    exponentIncomingLift a i p u = incomingLift a i ⟨p.val.1, p.property⟩
      ⟨curryAlgEquiv R u.val, curryAlgEquiv_mem_grade p.val u.val u.property⟩ := (rfl)

/-- An incoming monomial lifts to the same tangential coefficient times a nodal power. -/
@[simp]
theorem exponentIncomingLift_single (i : Fin 2) (n : ℕ) (m : M) (c : R) :
    exponentIncomingLift a i ⟨((n : ℤ), m), by simp⟩
      ⟨single (n, m) c, single_mem_grade _ _⟩ = single m c • coord a i ^ n := by
  simp [exponentIncomingLift_apply, incomingLift_apply, -single_eq_C_mul_T]

/-- The two full-exponent lifts agree on every tangential monomial of normal weight zero. -/
@[simp]
theorem exponentIncomingLift_zero (i : Fin 2) (m : M) (u : grade R ((0 : ℤ), m)) :
    exponentIncomingLift a i ⟨(0, m), by simp⟩ u =
      algebraMap R[M] (NodeAlgebra R[M] a) (single m (u.val.coeff (0, m))) := by
  simp only [exponentIncomingLift_apply, incomingLift_zero]
  rw [coeff_curryAlgEquiv_of_mem_grade _ _ u.property]

/-- Incoming lifts preserve products of admissible full-exponent pieces. -/
theorem exponentIncomingLift_mul (i : Fin 2) (p q : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) (v : grade R q.val) :
    exponentIncomingLift a i
      ⟨p.val + q.val, add_nonneg (a := p.val.1) (b := q.val.1) p.property q.property⟩
      ⟨u.val * v.val, SetLike.mul_mem_graded u.property v.property⟩ =
        exponentIncomingLift a i p u * exponentIncomingLift a i q v := by
  simp only [exponentIncomingLift_apply]
  simpa only [map_mul, Prod.fst_add] using incomingLift_mul a i ⟨p.val.1, p.property⟩
    ⟨q.val.1, q.property⟩
    ⟨curryAlgEquiv R u.val, curryAlgEquiv_mem_grade p.val u.val u.property⟩
    ⟨curryAlgEquiv R v.val, curryAlgEquiv_mem_grade q.val v.val v.property⟩

/-- The left full-exponent lift is a section of its own chamber map. -/
@[simp]
theorem exponentLeftMap_exponentIncomingLift (p : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) : exponentLeftMap a (exponentIncomingLift a 0 p u) = u := by
  apply (curryAlgEquiv R).injective
  simp [exponentIncomingLift_apply]

/-- The right full-exponent lift is a section of its own chamber map. -/
@[simp]
theorem exponentRightMap_exponentIncomingLift (p : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) : exponentRightMap a (exponentIncomingLift a 1 p u) = u := by
  apply (curryAlgEquiv R).injective
  simp [exponentIncomingLift_apply]

/-- Crossing from the left reverses the normal exponent and multiplies by `a^n`. -/
@[simp]
theorem exponentRightMap_exponentIncomingLift_zero (p : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) :
    exponentRightMap a (exponentIncomingLift a 0 p u) =
      (curryAlgEquiv R).symm (single (-p.val.1)
        (single p.val.2 (u.val.coeff p.val) * a ^ p.val.1.toNat)) := by
  apply (curryAlgEquiv R).injective
  simp only [curry_exponentRightMap, exponentIncomingLift_apply,
    rightLaurentMap_incomingLift_zero, AlgEquiv.apply_symm_apply]
  rw [coeff_curryAlgEquiv_of_mem_grade _ _ u.property]

/-- Crossing from the right has the same tangential multiplier and reversed normal exponent. -/
@[simp]
theorem exponentLeftMap_exponentIncomingLift_one (p : {p : ℤ × M | 0 ≤ p.1})
    (u : grade R p.val) :
    exponentLeftMap a (exponentIncomingLift a 1 p u) =
      (curryAlgEquiv R).symm (single (-p.val.1)
        (single p.val.2 (u.val.coeff p.val) * a ^ p.val.1.toNat)) := by
  apply (curryAlgEquiv R).injective
  simp only [curry_exponentLeftMap, exponentIncomingLift_apply,
    leftLaurentMap_incomingLift_one, AlgEquiv.apply_symm_apply]
  rw [coeff_curryAlgEquiv_of_mem_grade _ _ u.property]

/-- For the slab parameter `t(1+z^w)`, an incoming monomial has the binomial
crossing expansion. Coincident exponents in `M` combine in this finite sum. -/
theorem exponentRightMap_exponentIncomingLift_binomial (t c : R) (n : ℕ) (m w : M) :
    exponentRightMap (single 0 t + single w t)
      (exponentIncomingLift (single 0 t + single w t) 0 ⟨((n : ℤ), m), by simp⟩
        ⟨single (n, m) c, single_mem_grade _ _⟩) =
      ∑ j ∈ Finset.range (n + 1),
        single (-(n : ℤ), m + j • w) (c * t ^ n * (n.choose j : R)) := by
  rw [exponentRightMap_exponentIncomingLift_zero]
  simp only [coeff_single, Finsupp.single_eq_same, Int.toNat_natCast]
  apply (curryAlgEquiv R).injective
  simp only [AlgEquiv.apply_symm_apply, map_sum, curryAlgEquiv_single]
  rw [add_comm (single 0 t) (single w t), add_pow, Finset.mul_sum]
  trans single (-(n : ℤ)) (∑ j ∈ Finset.range (n + 1),
    single (m + j • w) (c * t ^ n * (n.choose j : R)))
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp [single_pow, natCast_def, single_mul_single, ← pow_add, Nat.add_sub_of_le hjn,
      mul_assoc, -single_eq_C_mul_T]
  · exact map_sum (singleAddHom (-(n : ℤ))) _ _

/-- The reverse crossing for `t(1+z^w)` has the same binomial expansion. -/
theorem exponentLeftMap_exponentIncomingLift_binomial (t c : R) (n : ℕ) (m w : M) :
    exponentLeftMap (single 0 t + single w t)
      (exponentIncomingLift (single 0 t + single w t) 1 ⟨((n : ℤ), m), by simp⟩
        ⟨single (n, m) c, single_mem_grade _ _⟩) =
      ∑ j ∈ Finset.range (n + 1),
        single (-(n : ℤ), m + j • w) (c * t ^ n * (n.choose j : R)) := by
  rw [exponentLeftMap_exponentIncomingLift_one]
  simpa only [exponentRightMap_exponentIncomingLift_zero] using
    exponentRightMap_exponentIncomingLift_binomial t c n m w

/-- The slab correspondence for the full normal and tangential exponent grading.
Nonnegative normal exponents are chosen as admissible on both sides. -/
def exponentCorrespondence :
    GradedCorrespondence (B := NodeAlgebra R[M] a)
      (grade R : ℤ × M → _) (grade R : ℤ × M → _)
      {p | 0 ≤ p.1} {p | 0 ≤ p.1} where
  left := (exponentLeftMap a).toLinearMap
  right := (exponentRightMap a).toLinearMap
  liftLeft := exponentIncomingLift a 0
  liftRight := exponentIncomingLift a 1
  left_liftLeft _ := by ext; simp
  right_liftRight _ := by ext; simp

@[simp]
theorem exponentCorrespondence_left :
    (exponentCorrespondence a).left = (exponentLeftMap a).toLinearMap := (rfl)

@[simp]
theorem exponentCorrespondence_right :
    (exponentCorrespondence a).right = (exponentRightMap a).toLinearMap := (rfl)

@[simp]
theorem exponentCorrespondence_liftLeft (p : {p : ℤ × M | 0 ≤ p.1}) :
    (exponentCorrespondence a).liftLeft p = exponentIncomingLift a 0 p := (rfl)

@[simp]
theorem exponentCorrespondence_liftRight (p : {p : ℤ × M | 0 ≤ p.1}) :
    (exponentCorrespondence a).liftRight p = exponentIncomingLift a 1 p := (rfl)

/-- A forward transfer reads one tangential coefficient of `c z^m a^n` at normal
weight `-n`. All other normal weights vanish. -/
@[simp↓]
theorem exponentCorrespondence_transfer [DecidableEq M]
    (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) (u : grade R p.val) :
    ((exponentCorrespondence a).transfer p q u : R[ℤ × M]) =
      if q.1 = -p.val.1 then
        single q ((single p.val.2 (u.val.coeff p.val) * a ^ p.val.1.toNat).coeff q.2)
      else 0 := by
  rw [GradedCorrespondence.transfer_apply, exponentCorrespondence_right,
    exponentCorrespondence_liftLeft, AlgHom.toLinearMap_apply,
    exponentRightMap_exponentIncomingLift_zero, coe_decompose_grade,
    coeff_curryAlgEquiv_symm]
  by_cases h : q.1 = -p.val.1 <;>
    simp [coeff_single, h, -single_eq_C_mul_T]

/-- The reverse transfer has the identical tangential coefficient formula. -/
@[simp↓]
theorem exponentCorrespondence_symm_transfer [DecidableEq M]
    (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) (u : grade R p.val) :
    ((exponentCorrespondence a).symm.transfer p q u : R[ℤ × M]) =
      if q.1 = -p.val.1 then
        single q ((single p.val.2 (u.val.coeff p.val) * a ^ p.val.1.toNat).coeff q.2)
      else 0 := by
  rw [GradedCorrespondence.transfer_apply, GradedCorrespondence.symm_right,
    GradedCorrespondence.symm_liftLeft, exponentCorrespondence_left,
    exponentCorrespondence_liftRight, AlgHom.toLinearMap_apply,
    exponentLeftMap_exponentIncomingLift_one, coe_decompose_grade,
    coeff_curryAlgEquiv_symm]
  by_cases h : q.1 = -p.val.1 <;>
    simp [coeff_single, h, -single_eq_C_mul_T]

end Mei.NodeAlgebra
