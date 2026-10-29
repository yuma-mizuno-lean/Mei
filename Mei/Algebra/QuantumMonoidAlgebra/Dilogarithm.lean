/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Conjugation
public import Mei.RingTheory.PowerSeries.QuantumDilogarithm

/-!
# Quantum dilogarithm actions in the monomial basis

Conjugation by the quantum dilogarithm of a positive-degree monomial has a finite
monomial expansion when its pairing with the input exponent is nonnegative.
The sum runs over subsets of the linear factors in the quantum dilogarithm's
rescaling equation. Its scalar includes the quantum ordering factor, so the
pairings one and two give respectively coefficients `1, 1` and `1, q + q⁻¹, 1`.
The identities hold in the coefficient completion, hence at every finite order.

We use `QuantumMonoidAlgebra.completedAeval_conj_monomial`,
`Units.rescale_pow_quantumDilogarithm_mul_inv` and Mathlib's `Finset.prod_one_add`.
The conventions follow Nakanishi, *Pentagon relation in quantum cluster scattering
diagrams*, §2.3, equations (2.14) and (2.21), arXiv:2202.01588v7.
-/

public section

noncomputable section

open scoped PowerSeries

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (hβ : β.IsAlt)
  (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ p ∈ P, 0 ≤ δ p)
  (n : P) (hn : 0 < δ n)
  (hq : ∀ j : ℕ, IsUnit ((q : R) ^ (j + 1) - (↑q⁻¹ : R) ^ (j + 1)))

local notation "F" => positiveFiltration q β P δ hδ
local notation "ι" => AlgFiltration.toCompletionₐ (R := R) F
local notation "z" => (fun p : P => ι (positiveMonomial q β P p))
local notation "x" => (Subtype.mk (z n)
  (completedMonomial_mem_first q β P δ hδ n hn) : AlgFiltration.completionIdeal F 1)
local notation "D" => AlgFiltration.completedAeval F x (Units.quantumDilogarithm q hq)

-- Direct inherited instances avoid searching through the quotient, product and
-- subring layers each time a finite sum in the completion is elaborated.
private instance positiveCompletionSemiring : Semiring (F).completion :=
  (inferInstance : Ring (F).completion).toSemiring

private instance positiveCompletionMonoid : Monoid (F).completion :=
  (inferInstance : Semiring (F).completion).toMonoid

private instance positiveCompletionPow : Pow (F).completion ℕ :=
  ⟨fun a j => (inferInstance : Monoid (F).completion).npow j a⟩

private instance positiveCompletionAddCommMonoid : AddCommMonoid (F).completion :=
  (inferInstance : Semiring (F).completion).toAddCommMonoid

private instance positiveCompletionAddSemigroup : AddSemigroup (F).completion :=
  (inferInstance : AddCommMonoid (F).completion).toAddSemigroup

private theorem pairing_two_sum {M : Type*} [AddCommMonoid M] [Module R M] (v : ℕ → M) :
    (∑ s ∈ (Finset.range 2).powerset,
      ((q ^ ((∑ j ∈ s, (2 * (j : ℤ) + 1)) - (2 : ℤ) * s.card) : Rˣ) : R) •
        v s.card) = v 0 + ((q : R) + (↑q⁻¹ : R)) • v 1 + v 2 := by
  have hs : (Finset.range 2).powerset = {∅, {1}, {0}, {0, 1}} := by decide
  rw [hs, Finset.sum_insert (by decide : (∅ : Finset ℕ) ∉ {{1}, {0}, {0, 1}}),
    Finset.sum_insert (by decide : ({1} : Finset ℕ) ∉ {{0}, {0, 1}}),
    Finset.sum_insert (by decide : ({0} : Finset ℕ) ∉ {{0, 1}}), Finset.sum_singleton]
  simp [add_smul, add_assoc]

include hβ

/-- For nonnegative pairing, the quantum dilogarithm action is evaluation of its
finite rescaling product in the completed coefficient algebra. -/
theorem quantumDilogarithm_conj_eq_prod (p : P) (r : ℕ) (hr : β n p = r) :
    D * z p * Ring.inverse D =
      z p * (F).completedAeval x
        (∏ j ∈ Finset.range r, (1 + PowerSeries.C ((q : R) ^ (2 * j + 1)) *
          PowerSeries.X)) := by
  classical
  let G : R⟦X⟧ˣ :=
    ⟨Units.quantumDilogarithm q hq, PowerSeries.invOfUnit (Units.quantumDilogarithm q hq) 1,
      PowerSeries.mul_invOfUnit _ 1 (by simp), PowerSeries.invOfUnit_mul _ 1 (by simp)⟩
  have hc := completedAeval_conj_monomial q β P δ hδ n hn hβ p G
  simp only [G, Units.val_mk, Units.inv_mk, hr,
    AlgFiltration.completedAeval_invOfUnit _ _ _ 1
      (Units.constantCoeff_quantumDilogarithm q hq)] at hc
  have he : ((q ^ (2 * (r : ℤ)) : Rˣ) : R) = (q : R) ^ (2 * r) := by
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, zpow_natCast, Units.val_pow_eq_pow_val]
  have hs : PowerSeries.rescale ((q ^ (2 * (r : ℤ)) : Rˣ) : R)
      (Units.quantumDilogarithm q hq) *
        PowerSeries.invOfUnit (Units.quantumDilogarithm q hq) 1 =
      ∏ j ∈ Finset.range r,
        (1 + PowerSeries.C ((q : R) ^ (2 * j + 1)) * PowerSeries.X) := by
    rw [he, Units.rescale_pow_quantumDilogarithm_mul_inv]
  exact hc.trans (congrArg (fun f : R⟦X⟧ => z p * (F).completedAeval x f) hs)

private theorem monomial_mul_completedAeval_prod (p : P) (r : ℕ) (hr : β n p = r)
    (s : Finset ℕ) :
    z p * (F).completedAeval x
        (∏ j ∈ s, (PowerSeries.C ((q : R) ^ (2 * j + 1)) * PowerSeries.X)) =
      ((q ^ ((∑ j ∈ s, (2 * (j : ℤ) + 1)) - (r : ℤ) * s.card) : Rˣ) : R) •
        z (p + s.card • n) := by
  classical
  have hprod : (∏ j ∈ s, (PowerSeries.C ((q : R) ^ (2 * j + 1)) * PowerSeries.X)) =
      PowerSeries.C ((q : R) ^ (∑ j ∈ s, (2 * j + 1))) * PowerSeries.X ^ s.card := by
    rw [← Finset.prod_mul_pow_card, ← map_prod, Finset.prod_pow_eq_pow_sum]
  refine (congrArg (fun f : R⟦X⟧ => z p * (F).completedAeval x f) hprod).trans ?_
  simp only [map_mul, AlgFiltration.completedAeval_C, map_pow,
    AlgFiltration.completedAeval_X]
  let v : (F).completion := z n ^ s.card
  have ha : (algebraMap R (F).completion (q : R)) ^ (∑ j ∈ s, (2 * j + 1)) =
      algebraMap R (F).completion ((q : R) ^ (∑ j ∈ s, (2 * j + 1))) :=
    ((algebraMap R (F).completion).map_pow _ _).symm
  refine (congrArg (fun a => z p * (a * v)) ha).trans ?_
  refine (congrArg (fun t => z p * t)
    (Algebra.smul_def ((q : R) ^ (∑ j ∈ s, (2 * j + 1)))
      v).symm).trans ?_
  refine (mul_smul_comm ((q : R) ^ (∑ j ∈ s, (2 * j + 1))) (z p) v).trans ?_
  have hm : positiveMonomial q β P p * positiveMonomial q β P n ^ s.card =
      ((q ^ (-((s.card : ℤ) * r)) : Rˣ) : R) •
        positiveMonomial q β P (p + s.card • n) := by
    apply Subtype.ext
    simp [monomial_pow q β hβ, ← hβ.neg_eq n p, hr]
  have heq := congrArg ι hm
  simp only [map_mul, map_pow, AlgHom.map_smul_of_tower] at heq
  refine (congrArg (fun t : (F).completion =>
    ((q : R) ^ (∑ j ∈ s, (2 * j + 1))) • t) heq).trans ?_
  simp only [smul_smul]
  simp only [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← Units.val_mul, ← zpow_add]
  congr 2
  push_cast
  simp [mul_comm, sub_eq_add_neg]

/-- For nonnegative pairing, quantum dilogarithm conjugation expands as a finite
sum of quantum monomials. Each subset selects the nonconstant terms of the
rescaling factors; the exponent includes the scalar from ordering the monomials. -/
theorem quantumDilogarithm_conj_eq_sum (p : P) (r : ℕ) (hr : β n p = r) :
    D * z p * Ring.inverse D =
      ∑ s ∈ (Finset.range r).powerset,
        ((q ^ ((∑ j ∈ s, (2 * (j : ℤ) + 1)) - (r : ℤ) * s.card) : Rˣ) : R) •
          z (p + s.card • n) := by
  classical
  refine (quantumDilogarithm_conj_eq_prod q β hβ P δ hδ n hn hq p r hr).trans ?_
  have hs := Finset.prod_one_add (R := R⟦X⟧)
    (f := fun j => PowerSeries.C ((q : R) ^ (2 * j + 1)) * PowerSeries.X) (Finset.range r)
  refine (congrArg (fun f : R⟦X⟧ => z p * (F).completedAeval x f) hs).trans ?_
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact monomial_mul_completedAeval_prod q β hβ P δ hδ n hn p r hr s

/-- Pairing one gives the two quantum monomials with coefficient one. -/
theorem quantumDilogarithm_conj_of_pairing_one (p : P) (hp : β n p = 1) :
    D * z p * Ring.inverse D = z p + z (p + n) := by
  have h := quantumDilogarithm_conj_eq_sum q β hβ P δ hδ n hn hq p 1 (by simpa using hp)
  have hs : (Finset.range 1).powerset = {∅, {0}} := by decide
  refine h.trans ((congrArg (fun t : Finset (Finset ℕ) => ∑ s ∈ t,
    ((q ^ ((∑ j ∈ s, (2 * (j : ℤ) + 1)) - (1 : ℤ) * s.card) : Rˣ) : R) •
      z (p + s.card • n)) hs).trans ?_)
  simp

/-- Pairing two gives the three monomial coefficients `1`, `q + q⁻¹`, `1`. -/
theorem quantumDilogarithm_conj_of_pairing_two (p : P) (hp : β n p = 2) :
    D * z p * Ring.inverse D =
      z p + ((q : R) + (↑q⁻¹ : R)) • z (p + n) + z (p + 2 • n) := by
  have h := quantumDilogarithm_conj_eq_sum q β hβ P δ hδ n hn hq p 2 (by simpa using hp)
  simpa only [zero_smul, add_zero, one_smul] using
    h.trans (pairing_two_sum q (fun j => z (p + j • n)))

end Mei.QuantumMonoidAlgebra
