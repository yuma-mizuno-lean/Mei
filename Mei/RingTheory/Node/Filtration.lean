/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.RingTheory.Node.Tangential
public import Mei.Algebra.MonoidAlgebra.Ideal
public import Mei.Algebra.MonoidAlgebra.Filtration.Coefficient
public import Mei.Algebra.DirectSum.Component
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Coefficient order of slab crossings

In the slab `R[M][X,Y]/(XY-a)`, an incoming component of positive normal
weight `d` acquires the multiplier `a ^ d` on crossing. If every coefficient
of `a` lies in an ideal `I`, its outgoing components gain at least `d` powers
of `I`. A surviving sequence therefore has fewer than `r` transverse slab
crossings when `I ^ r = 0`. Tangential crossings have weight zero and need
not raise order.

`AddMonoidAlgebra.slabComponentMap` records a selected whole-component transfer
on its scalar coefficient. Both orientations of `exponentCorrespondence` induce this same
map. Its finite composites allow different slab parameters and independent
source and target exponents at each step, and arbitrary intervening scalar-linear
component maps, as needed when the chamber coordinates change between faces.
No regularity of the slab parameters is assumed.

A whole-component transfer to a different exponent also raises the coefficient filtration order.
`Mei.NodeAlgebra.homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence` incorporates
weight-zero transfers to a different exponent.

The component formulas are those of `exponentCorrespondence_transfer` and its
reverse, and the finite composites use Mathlib's `Module.End` multiplication.
For the positive-kink finiteness argument, see Gross–Hacking–Siebert, *Theta
functions on varieties with effective anti-canonical class*, Proposition 3.5
and Lemma 3.7 (arXiv:1601.07081v4).
-/

public noncomputable section

namespace AddMonoidAlgebra

section Scalar

variable {R M : Type*} [Semiring R] [AddMonoid M]

/-- The scalar coefficient map of a slab transfer from admissible exponent `p`
to exponent `q`. The same map describes either crossing orientation. -/
def slabComponentMap (a : R[M]) (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) :
    Module.End R R :=
  if q.1 = -p.val.1 then
    ((Finsupp.lapply q.2).comp (coeffLinearEquiv R).toLinearMap).comp
      ((LinearMap.mulRight R (a ^ p.val.1.toNat)).comp (lsingle p.val.2))
  else 0

/-- A selected component extracts the target coefficient of
`single p.val.2 c * a ^ p.val.1.toNat`, combining coincident translated exponents.
Components of the wrong normal weight vanish. -/
@[simp]
theorem slabComponentMap_apply (a : R[M]) (p : {p : ℤ × M | 0 ≤ p.1})
    (q : ℤ × M) (c : R) :
    slabComponentMap a p q c =
      if q.1 = -p.val.1 then (single p.val.2 c * a ^ p.val.1.toNat).coeff q.2 else 0 := by
  simp only [slabComponentMap]
  split_ifs <;> rfl

end Scalar

section Correspondence

open Mei.NodeAlgebra

variable {R M : Type*} [CommRing R] [AddCommMonoid M]

/-- The scalar component map recovers the entire forward homogeneous transfer. -/
theorem exponentCorrespondence_transfer_eq_single [DecidableEq M]
    (a : R[M]) (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) (u : grade R p.val) :
    ((exponentCorrespondence a).transfer p q u : R[ℤ × M]) =
      single q (slabComponentMap a p q (u.val.coeff p.val)) := by
  rw [exponentCorrespondence_transfer, slabComponentMap_apply]
  split_ifs <;> simp

/-- Reverse slab transfers have exactly the same scalar coefficient map. -/
theorem exponentCorrespondence_symm_transfer_eq_single [DecidableEq M]
    (a : R[M]) (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) (u : grade R p.val) :
    ((exponentCorrespondence a).symm.transfer p q u : R[ℤ × M]) =
      single q (slabComponentMap a p q (u.val.coeff p.val)) := by
  rw [exponentCorrespondence_symm_transfer, slabComponentMap_apply]
  split_ifs <;> simp

end Correspondence

end AddMonoidAlgebra

namespace Ideal

open AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R] [AddMonoid M]

/-- A slab crossing of normal weight `d` raises coefficient ideal order by `d`.
This includes zero and nonreduced slab parameters and weight-zero inputs. -/
theorem slabComponentMap_mem_pow (I : Ideal R) {a : R[M]}
    (ha : ∀ m, a.coeff m ∈ I) (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M)
    {b : ℕ} {c : R} (hc : c ∈ I ^ b) :
    slabComponentMap a p q c ∈ I ^ (b + p.val.1.toNat) := by
  classical
  rw [slabComponentMap_apply]
  split_ifs
  · rw [pow_add]
    refine coeff_mul_mem_mul (fun m => ?_) (coeff_pow_mem_pow ha _) _
    by_cases hm : p.val.2 = m
    · simpa [hm] using hc
    · simp [coeff_single, hm]
  · exact (I ^ _).zero_mem

/-- A slab component to a different exponent raises the ideal order by at least one, since a
component of positive normal weight gains that many powers and one of weight zero is carried to
itself. A component to the same exponent preserves the order. -/
theorem slabComponentMap_mem_pow_add_ite [DecidableEq M] (I : Ideal R) {a : R[M]}
    (ha : ∀ m, a.coeff m ∈ I) (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) {b : ℕ} {c : R}
    (hc : c ∈ I ^ b) :
    slabComponentMap a p q c ∈ I ^ (b + if p.val = q then 0 else 1) := by
  have hmem := slabComponentMap_mem_pow I ha p q hc
  by_cases hpq : p.val = q
  · simp only [hpq, ↓reduceIte, Nat.add_zero]
    exact Ideal.pow_le_pow_right (Nat.le_add_right _ _) hmem
  · simp only [hpq, ↓reduceIte]
    by_cases hd : p.val.1 = 0
    · have hq : slabComponentMap a p q c = 0 := by
        rw [slabComponentMap_apply]
        split_ifs with h
        · have h2 : p.val.2 ≠ q.2 := fun h2 => hpq (Prod.ext (by omega) h2)
          simp [hd, coeff_single, h2]
        · rfl
      rw [hq]
      exact (I ^ _).zero_mem
    · have hp : 0 ≤ p.val.1 := p.property
      exact Ideal.pow_le_pow_right (by omega) hmem

/-- Composite slab components gain the sum of their incoming normal weights.
The maps `f` allow arbitrary coefficient-linear operations before each slab
crossing. Index zero acts last, following multiplication in `Module.End`. -/
theorem prod_slabComponentMap_mul_apply_mem_pow (I : Ideal R) {n : ℕ}
    (a : Fin n → R[M]) (ha : ∀ j m, (a j).coeff m ∈ I)
    (p : Fin n → {p : ℤ × M | 0 ≤ p.1}) (q : Fin n → ℤ × M)
    (f : Fin n → Module.End R R) {b : ℕ} {c : R} (hc : c ∈ I ^ b) :
    (List.ofFn fun j => slabComponentMap (a j) (p j) (q j) * f j).prod c ∈
      I ^ (b + ∑ j, (p j).val.1.toNat) := by
  induction n with
  | zero => simpa using hc
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    have ht := ih (fun j => a j.succ) (fun j => ha j.succ)
      (fun j => p j.succ) (fun j => q j.succ) (fun j => f j.succ)
    have hf : f 0 ((List.ofFn fun j : Fin n =>
        slabComponentMap (a j.succ) (p j.succ) (q j.succ) * f j.succ).prod c) ∈
        I ^ (b + ∑ j : Fin n, (p j.succ).val.1.toNat) := by
      have he (x : R) : f 0 x = x * f 0 1 := by
        simpa only [smul_eq_mul, mul_one] using (f 0).map_smul x 1
      rw [he]
      exact (I ^ _).mul_mem_right _ ht
    simpa only [Module.End.mul_apply, Fin.sum_univ_succ, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using
      slabComponentMap_mem_pow I (ha 0) (p 0) (q 0) hf

/-- A nilpotent coefficient ideal kills a slab history once its accumulated
normal weight reaches the nilpotency bound. -/
theorem prod_slabComponentMap_mul_apply_eq_zero_of_pow_eq_bot (I : Ideal R) {n r b : ℕ}
    (hI : I ^ r = ⊥) (a : Fin n → R[M]) (ha : ∀ j m, (a j).coeff m ∈ I)
    (p : Fin n → {p : ℤ × M | 0 ≤ p.1}) (q : Fin n → ℤ × M)
    (f : Fin n → Module.End R R) {c : R} (hc : c ∈ I ^ b) (hr : r ≤ b + ∑ j, (p j).val.1.toNat) :
    (List.ofFn fun j => slabComponentMap (a j) (p j) (q j) * f j).prod c = 0 := by
  have h := Ideal.pow_le_pow_right hr
    (prod_slabComponentMap_mul_apply_mem_pow I a ha p q f hc)
  simpa only [hI, Ideal.mem_bot] using h

/-- A nonzero slab history has total incoming normal weight below the
nilpotency bound, also taking the order of its input into account. -/
theorem sum_normalWeight_lt_of_slabComponentMap_ne_zero (I : Ideal R) {n r b : ℕ}
    (hI : I ^ r = ⊥) (a : Fin n → R[M]) (ha : ∀ j m, (a j).coeff m ∈ I)
    (p : Fin n → {p : ℤ × M | 0 ≤ p.1}) (q : Fin n → ℤ × M)
    (f : Fin n → Module.End R R) {c : R} (hc : c ∈ I ^ b)
    (hne : (List.ofFn fun j => slabComponentMap (a j) (p j) (q j) * f j).prod c ≠ 0) :
    b + ∑ j, (p j).val.1.toNat < r := by
  by_contra h
  exact hne (prod_slabComponentMap_mul_apply_eq_zero_of_pow_eq_bot I hI a ha p q f hc (by omega))

/-- Fewer than `r` transverse slab crossings can occur in a surviving
component history when the kink coefficients lie in an ideal with `I ^ r = 0`.
Weight-zero encounters are retained and do not count as transverse crossings. -/
theorem card_transverse_lt_of_slabComponentMap_ne_zero (I : Ideal R) {n r : ℕ}
    (hI : I ^ r = ⊥) (a : Fin n → R[M]) (ha : ∀ j m, (a j).coeff m ∈ I)
    (p : Fin n → {p : ℤ × M | 0 ≤ p.1}) (q : Fin n → ℤ × M)
    (f : Fin n → Module.End R R) {c : R}
    (hne : (List.ofFn fun j => slabComponentMap (a j) (p j) (q j) * f j).prod c ≠ 0) :
    (Finset.univ.filter fun j => 0 < (p j).val.1).card < r := by
  classical
  have hsum := sum_normalWeight_lt_of_slabComponentMap_ne_zero I hI a ha p q f
    (b := 0) (c := c) (by simp) hne
  have hcard : (Finset.univ.filter fun j => 0 < (p j).val.1).card ≤
      ∑ j, (p j).val.1.toNat := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_le_sum fun j _ => by split_ifs <;> omega
  omega

end Ideal

namespace Mei.NodeAlgebra

open TauCeti AddMonoidAlgebra Mei

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [DecidableEq M] {I : Ideal R}

/-- Selecting a component after a total slab transfer extracts its scalar
component map on admissible inputs and is zero on inadmissible inputs. The
formula covers both orientations of the face. -/
theorem homogeneousComponent_exponentCorrespondence_eq_single {a : R[M]}
    {T : Module.End R R[ℤ × M]}
    (hT : T = (exponentCorrespondence a).totalTransfer ∨
      T = (exponentCorrespondence a).symm.totalTransfer)
    {p : ℤ × M} {x : R[ℤ × M]} (hx : x ∈ grade R p) (q : ℤ × M) :
    homogeneousComponent (grade R) q (T x) =
      if hp : 0 ≤ p.1 then single q (slabComponentMap a ⟨p, hp⟩ q (x.coeff p)) else 0 := by
  have key (C : GradedCorrespondence (B := NodeAlgebra R[M] a) (grade R : ℤ × M → _)
      (grade R : ℤ × M → _) {p | 0 ≤ p.1} {p | 0 ≤ p.1})
      (hC : ∀ (p : {p : ℤ × M | 0 ≤ p.1}) (q : ℤ × M) (u : grade R p.val),
        ((C.transfer p q u : grade R q) : R[ℤ × M]) =
          single q (slabComponentMap a p q (u.val.coeff p.val))) :
      homogeneousComponent (grade R) q (C.totalTransfer x) =
        if hp : 0 ≤ p.1 then single q (slabComponentMap a ⟨p, hp⟩ q (x.coeff p)) else 0 := by
    rw [homogeneousComponent_apply, GradedCorrespondence.totalTransfer_apply,
      C.decompose_right_liftLeftTotal_of_mem hx q]
    by_cases hp : 0 ≤ p.1
    · simpa only [Set.mem_ofPred_eq, hp, ↓reduceDIte] using hC ⟨p, hp⟩ q ⟨x, hx⟩
    · simp only [Set.mem_ofPred_eq, hp, ↓reduceDIte, Submodule.coe_zero]
  rcases hT with rfl | rfl
  · exact key _ fun p q u => exponentCorrespondence_transfer_eq_single a p q u
  · exact key _ fun p q u => exponentCorrespondence_symm_transfer_eq_single a p q u

/-- A whole slab component gains the incoming nonnegative normal weight in
coefficient order. Inadmissible negative normal weights give zero, so the
statement also holds there, with gain zero. -/
theorem homogeneousComponent_exponentCorrespondence_mem_coeffFiltration_add_normalWeight
    {a : R[M]} (ha : ∀ m, a.coeff m ∈ I) {T : Module.End R R[ℤ × M]}
    (hT : T = (exponentCorrespondence a).totalTransfer ∨
      T = (exponentCorrespondence a).symm.totalTransfer)
    {p q : ℤ × M} {x : R[ℤ × M]} (hx : x ∈ grade R p) {k : ℕ}
    (hxk : x ∈ (Ideal.coeffFiltration I (ℤ × M)).submodule k) :
    homogeneousComponent (grade R) q (T x) ∈
      (Ideal.coeffFiltration I (ℤ × M)).submodule (k + p.1.toNat) := by
  rw [homogeneousComponent_exponentCorrespondence_eq_single hT hx q]
  by_cases hp : 0 ≤ p.1
  · rw [dite_eq_left hp]
    exact (Ideal.single_mem_coeffFiltration_submodule (I := I) (M := ℤ × M)).mpr
      (Ideal.slabComponentMap_mem_pow I ha ⟨p, hp⟩ q
        ((Ideal.mem_coeffFiltration_submodule (I := I) (M := ℤ × M)).mp hxk p))
  · rw [dite_eq_right hp]
    exact Submodule.zero_mem _

/-- A homogeneous input in the `k`-th term of the coefficient filtration is sent by the
whole-component transfer of a slab correspondence, in either orientation, into the `k`-th term
if the output exponent is the input exponent, and into the `(k + 1)`-st term otherwise, provided
the slab parameter has all coefficients in `I`. -/
theorem homogeneousComponent_mem_coeffFiltration_of_exponentCorrespondence {a : R[M]}
    (ha : ∀ m, a.coeff m ∈ I) {T : Module.End R R[ℤ × M]}
    (hT : T = (exponentCorrespondence a).totalTransfer ∨
      T = (exponentCorrespondence a).symm.totalTransfer)
    {p q : ℤ × M} {x : R[ℤ × M]} (hx : x ∈ grade R p) {k : ℕ}
    (hxk : x ∈ (Ideal.coeffFiltration I (ℤ × M)).submodule k) :
    homogeneousComponent (grade R : ℤ × M → _) q (T x) ∈
      (Ideal.coeffFiltration I (ℤ × M)).submodule (k + if p = q then 0 else 1) := by
  rw [homogeneousComponent_exponentCorrespondence_eq_single hT hx q]
  by_cases hp : 0 ≤ p.1
  · rw [dite_eq_left hp]
    exact (Ideal.single_mem_coeffFiltration_submodule (I := I) (M := ℤ × M)).mpr
      (Ideal.slabComponentMap_mem_pow_add_ite I ha ⟨p, hp⟩ q
        ((Ideal.mem_coeffFiltration_submodule (I := I) (M := ℤ × M)).mp hxk p))
  · rw [dite_eq_right hp]
    exact Submodule.zero_mem _

end Mei.NodeAlgebra
