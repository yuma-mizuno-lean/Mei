/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Positive
public import Mei.Algebra.QuantumMonoidAlgebra.Ray
public import Mei.RingTheory.FilteredAlgebra.PowerSeries.Semiconj
public import Mei.RingTheory.PowerSeries.QuantumDilogarithm

/-!
# Quantum ray conjugation in the positive coefficient completion

A monomial of strictly positive degree is an admissible completed evaluation point.
For an arbitrary bilinear form, conjugation by a scalar unit series along this ray
acts on positive monomials by the rescaling ratio with exponent `β(n,p) - β(p,n)`.
For alternating forms this exponent is `2β(n,p)`. The quantum dilogarithm
finite-product formulas retain this alternating assumption: the multiplier is an
ordered product of linear factors for nonnegative pairings and their ring
inverses for nonpositive pairings.

The coefficient ring is arbitrary commutative; only the dilogarithm statement
requires its usual invertible denominators. We reuse the formal quantum
semiconjugacy and the generic completed power series evaluation theorems.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

open PowerSeries

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ)
  (P : AddSubmonoid Γ) (δ : Γ →+ ℤ) (hδ : ∀ p ∈ P, 0 ≤ δ p)

local notation "F" => positiveFiltration q β P δ hδ

/-- A strictly positive degree quantum monomial defines a positive completed element. -/
def completedRayGenerator (n : P) (hn : 0 < δ n) : (F).completionIdeal 1 :=
  ⟨(F).toCompletion (positiveMonomial q β P n), by
    rw [(F).toCompletion_mem_completionIdeal_iff]
    simpa only [one_smul] using
      (smul_positiveMonomial_mem_positiveFiltration_iff q β P δ hδ 1 n (1 : R)).mpr
        (Or.inr (by omega))⟩

/-- The positive completed ray generator is the canonical image of its monomial. -/
@[simp]
theorem coe_completedRayGenerator (n : P) (hn : 0 < δ n) :
    (completedRayGenerator q β P δ hδ n hn : (F).completion) =
      (F).toCompletion (positiveMonomial q β P n) := (rfl)

/-- For arbitrary bilinear forms, positive monomial semiconjugacy uses
exponent `β(n,p) - β(p,n)`. -/
theorem positiveMonomial_semiconjBy_skew (n p : P) :
    SemiconjBy (positiveMonomial q β P p)
      (((q ^ (β n p - β p n) : Rˣ) : R) • positiveMonomial q β P n)
      (positiveMonomial q β P n) := by
  apply Subtype.ext
  simpa only [Subalgebra.coe_mul, Subalgebra.coe_smul, coe_positiveMonomial] using
    (monomial_semiconjBy_skew q β n p).eq

/-- Under `β.IsAlt`, positive monomial semiconjugacy uses exponent `2β(n,p)`. -/
theorem positiveMonomial_semiconjBy (hβ : β.IsAlt) (n p : P) :
    SemiconjBy (positiveMonomial q β P p)
      (((q ^ (2 * β n p) : Rˣ) : R) • positiveMonomial q β P n)
      (positiveMonomial q β P n) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul] using
    positiveMonomial_semiconjBy_skew q β P n p

/-- For arbitrary bilinear forms, completed ray semiconjugacy uses
exponent `β(n,p) - β(p,n)`. -/
theorem completedRayGenerator_semiconjBy_skew (n p : P) (hn : 0 < δ n) :
    SemiconjBy ((F).toCompletion (positiveMonomial q β P p))
      (((q ^ (β n p - β p n) : Rˣ) : R) •
        (completedRayGenerator q β P δ hδ n hn : (F).completion))
      (completedRayGenerator q β P δ hδ n hn) := by
  have h := congrArg ((F).toCompletionₐ (R := R))
    (positiveMonomial_semiconjBy_skew q β P n p).eq
  have hs := ((F).toCompletionₐ (R := R)).toLinearMap.map_smul
    ((q ^ (β n p - β p n) : Rˣ) : R) (positiveMonomial q β P n)
  simp only [map_mul] at h
  simp only [AlgHom.toLinearMap_apply] at hs
  simp only [hs] at h
  simpa only [SemiconjBy, AlgFiltration.toCompletionₐ_apply,
    coe_completedRayGenerator] using h

/-- Under `β.IsAlt`, completed ray semiconjugacy uses exponent `2β(n,p)`. -/
theorem completedRayGenerator_semiconjBy (hβ : β.IsAlt) (n p : P) (hn : 0 < δ n) :
    SemiconjBy ((F).toCompletion (positiveMonomial q β P p))
      (((q ^ (2 * β n p) : Rˣ) : R) •
        (completedRayGenerator q β P δ hδ n hn : (F).completion))
      (completedRayGenerator q β P δ hδ n hn) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul] using
    completedRayGenerator_semiconjBy_skew q β P δ hδ n p hn

/-- For arbitrary bilinear forms, completed ray conjugation uses
exponent `β(n,p) - β(p,n)`. -/
theorem completedRay_conj_skew (n p : P) (hn : 0 < δ n)
    (G : (PowerSeries R)ˣ) :
    (F).completedAeval (completedRayGenerator q β P δ hδ n hn) (G : PowerSeries R) *
        (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (↑(G⁻¹) : PowerSeries R) =
      (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (rescale ((q ^ (β n p - β p n) : Rˣ) : R) (G : PowerSeries R) *
            (↑(G⁻¹) : PowerSeries R)) :=
  (F).completedAeval_conj _ _ _
    (completedRayGenerator_semiconjBy_skew q β P δ hδ n p hn) G

/-- Under `β.IsAlt`, completed ray conjugation uses exponent `2β(n,p)`. -/
theorem completedRay_conj (hβ : β.IsAlt) (n p : P) (hn : 0 < δ n)
    (G : (PowerSeries R)ˣ) :
    (F).completedAeval (completedRayGenerator q β P δ hδ n hn) (G : PowerSeries R) *
        (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (↑(G⁻¹) : PowerSeries R) =
      (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (rescale ((q ^ (2 * β n p) : Rˣ) : R) (G : PowerSeries R) *
            (↑(G⁻¹) : PowerSeries R)) := by
  simpa only [← hβ.neg_eq n p, sub_neg_eq_add, ← two_mul] using
    completedRay_conj_skew q β P δ hδ n p hn G

/-- For a nonnegative pairing, completed quantum dilogarithm conjugation has a
finite ordered product multiplier. -/
theorem completedRay_quantumDilogarithm_conj
    (hq : ∀ j : ℕ, IsUnit ((q : R) ^ (j + 1) - (↑q⁻¹ : R) ^ (j + 1)))
    (hβ : β.IsAlt) (n p : P) (hn : 0 < δ n) (r : ℕ) (hr : β n p = r) :
    (F).completedAeval (completedRayGenerator q β P δ hδ n hn) (q.quantumDilogarithm hq) *
        (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (invOfUnit (q.quantumDilogarithm hq) 1) =
      (F).toCompletion (positiveMonomial q β P p) *
        ((List.range r).map fun j =>
          1 + (q : R) ^ (2 * j + 1) •
            (completedRayGenerator q β P δ hδ n hn : (F).completion)).prod := by
  let G : (PowerSeries R)ˣ :=
    ⟨q.quantumDilogarithm hq, invOfUnit (q.quantumDilogarithm hq) 1,
      mul_invOfUnit _ _ (by simp), invOfUnit_mul _ _ (by simp)⟩
  have hs : ((q ^ (2 * β n p) : Rˣ) : R) = (q : R) ^ (2 * r) := by
    rw [hr]
    norm_cast
  have hc := completedRay_conj q β P δ hδ hβ n p hn G
  -- Unpack the explicitly constructed unit, retaining the public conjugation identity.
  simp only [G, Units.inv_mk, Units.val_mk, hs] at hc
  refine hc.trans ?_
  simp only [q.rescale_pow_quantumDilogarithm_mul_inv hq r]
  congr 1
  clear hr hc hs
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Finset.prod_range_succ, map_mul, List.prod_range_succ, ih,
      map_add, map_one, AlgFiltration.completedAeval_C, AlgFiltration.completedAeval_X,
      Algebra.smul_def]

/-- For a nonpositive pairing, the multiplier is an ordered product of the ring
inverses of unit linear factors. Every factor is evaluated in the same ray, so no
commutativity of the full coefficient algebra is assumed. -/
theorem completedRay_quantumDilogarithm_conj_neg
    (hq : ∀ j : ℕ, IsUnit ((q : R) ^ (j + 1) - (↑q⁻¹ : R) ^ (j + 1)))
    (hβ : β.IsAlt) (n p : P) (hn : 0 < δ n) (r : ℕ) (hr : β n p = -(r : ℤ)) :
    (F).completedAeval (completedRayGenerator q β P δ hδ n hn) (q.quantumDilogarithm hq) *
        (F).toCompletion (positiveMonomial q β P p) *
        (F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (invOfUnit (q.quantumDilogarithm hq) 1) =
      (F).toCompletion (positiveMonomial q β P p) *
        ((List.range r).map fun j =>
          Ring.inverse (1 + (↑q⁻¹ : R) ^ (2 * j + 1) •
            (completedRayGenerator q β P δ hδ n hn : (F).completion))).prod := by
  let G : (PowerSeries R)ˣ :=
    ⟨q.quantumDilogarithm hq, invOfUnit (q.quantumDilogarithm hq) 1,
      mul_invOfUnit _ _ (by simp), invOfUnit_mul _ _ (by simp)⟩
  have hs : ((q ^ (2 * β n p) : Rˣ) : R) = (↑q⁻¹ : R) ^ (2 * r) := by
    rw [hr, mul_neg]
    have he : (2 : ℤ) * (r : ℤ) = ((2 * r : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, Units.inv_pow_eq_pow_inv]
  have hc := completedRay_conj q β P δ hδ hβ n p hn G
  -- Unpack the explicitly constructed unit, retaining the public conjugation identity.
  simp only [G, Units.inv_mk, Units.val_mk, hs] at hc
  refine hc.trans ?_
  simp only [q.rescale_inv_pow_quantumDilogarithm_mul_inv hq r]
  congr 1
  clear hr hc hs
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Finset.prod_range_succ, map_mul, List.prod_range_succ, ih]
    congr 1
    calc
      _ = Ring.inverse ((F).completedAeval (completedRayGenerator q β P δ hδ n hn)
          (1 + C ((↑q⁻¹ : R) ^ (2 * r + 1)) * X)) :=
        (F).completedAeval_invOfUnit _ _ 1 (by simp)
      _ = _ := by
        congr 1
        simp only [map_add, map_one, map_mul, AlgFiltration.completedAeval_C,
          AlgFiltration.completedAeval_X, Algebra.smul_def]

end Mei.QuantumMonoidAlgebra
