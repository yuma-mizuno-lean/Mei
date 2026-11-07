/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Quotient
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.SkewProduct

/-!
# Products under quantum ray actions for arbitrary bilinear forms

The product of shifted coefficients is compatible with arbitrary unit ray series
for every integral bilinear form, without an alternating hypothesis.
In positive coordinates, moving the first coefficient past the second origin
conjugates it and multiplies by the phase of the two origin monomials.
Conjugation rescales the ray evaluation point by the skew character. Origins
may have arbitrary degree and no characteristic-zero assumption is used.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "τ" => completedMonomialRightConjSkew q β d.monoid d.degree
  (fun _ h => d.degree_nonneg h)

/-- Moving past an origin rescales the completed ray generator by its commutation character. -/
theorem completedMonomialRightConjSkew_completedRayGenerator (s : Γ)
    (n : d.monoid) (hn : 0 < d.degree n) :
    τ s (completedRayGenerator q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) n hn : (F).completion) =
      ((q ^ (β n s - β s n) : Rˣ) : R) •
        (completedRayGenerator q β d.monoid d.degree
          (fun _ h => d.degree_nonneg h) n hn : (F).completion) := by
  have ht := completedMonomialRightConjSkew_toCompletion q β d.monoid d.degree
    (fun _ h => d.degree_nonneg h) s (positiveMonomial q β d.monoid n)
  have hm := positiveMonomialRightConjSkew_monomial q β d.monoid s n
  have hs := _root_.map_smul ((F).toCompletionₐ (R := R))
    (((q ^ (β n s - β s n) : Rˣ) : R)) (positiveMonomial q β d.monoid n)
  simp only [AlgFiltration.toCompletionₐ_apply] at hs
  simpa only [coe_completedRayGenerator] using
    ht.trans ((congrArg ((F).toCompletion) hm).trans hs)

/-- Moving past an origin rescales the evaluation point of every scalar ray series. -/
theorem completedMonomialRightConjSkew_completedAeval (s : Γ)
    (n : d.monoid) (hn : 0 < d.degree n) (H : PowerSeries R) :
    τ s ((F).completedAeval (completedRayGenerator q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) n hn) H) =
      (F).completedAeval (((q ^ (β n s - β s n) : Rˣ) : R) •
        completedRayGenerator q β d.monoid d.degree
          (fun _ h => d.degree_nonneg h) n hn) H := by
  let x := completedRayGenerator q β d.monoid d.degree
    (fun _ h => d.degree_nonneg h) n hn
  let y := (((q ^ (β n s - β s n) : Rˣ) : R) • x)
  let ψ := positiveMonomialRightConjSkew q β d.monoid s
  let hf := fun k => positiveMonomialRightConjSkew_filtration_le q β d.monoid d.degree
    (fun _ h => d.degree_nonneg h) s (k + 1)
  have he := (F).mapCompletion_completedAeval_of_eq (F) (RingHom.id R) ψ.toRingHom
    (fun r => by
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.id_apply]
        using ψ.commutes r)
    id monotone_id hf
    (positiveMonomialRightConjSkew_filtration_le q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) s 1)
    (τ s).toRingHom (coe_completedMonomialRightConjSkew q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) s) x y
    (completedMonomialRightConjSkew_completedRayGenerator q β d s n hn) H
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, PowerSeries.map_id, id_eq] using he

/-- Origin conjugation transports a twisted action to the rescaled evaluation point. -/
theorem completedMonomialRightConjSkew_twistedSeriesAction (s : Γ)
    (n : d.monoid) (hn : 0 < d.degree n) (c : R) (H : (PowerSeries R)ˣ)
    (a : (F).completion) :
    τ s ((F).completedTwistedSeriesAction
      (completedRayGenerator q β d.monoid d.degree
        (fun _ h => d.degree_nonneg h) n hn) c H a) =
      (F).completedTwistedSeriesAction
        (((q ^ (β n s - β s n) : Rˣ) : R) • completedRayGenerator q β d.monoid d.degree
          (fun _ h => d.degree_nonneg h) n hn) c H (τ s a) := by
  simp only [AlgFiltration.completedTwistedSeriesAction_apply, map_mul,
    completedMonomialRightConjSkew_completedAeval]

private theorem shiftedRayAction_twisted_coordinates_skew
    (n : d.monoid) (hn : 0 < d.degree n) (p : Γ) (H : (PowerSeries R)ˣ)
    (a : (F).completion) :
    shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a) =
      positiveCompletionShiftEquiv q β d p
        ((F).completedTwistedSeriesAction
          (completedRayGenerator q β d.monoid d.degree
            (fun _ h => d.degree_nonneg h) n hn)
          (((q ^ (β n p - β p n) : Rˣ) : R)) H a) := by
  simpa only [AlgFiltration.completedTwistedSeriesAction_apply] using
    shiftedRayAction_coordinates_skew q β d n hn p H a

private theorem shiftedRayAction_product_coordinates_skew
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (H : (PowerSeries R)ˣ)
    (a b : (F).completion) :
    shiftedRayAction q β d n hn (p + s) H
        (d.shiftedCompletionMul (grade q β) p s
          (positiveCompletionShiftEquiv q β d p a)
          (positiveCompletionShiftEquiv q β d s b)) =
      d.shiftedCompletionMul (grade q β) p s
        (shiftedRayAction q β d n hn p H (positiveCompletionShiftEquiv q β d p a))
        (shiftedRayAction q β d n hn s H (positiveCompletionShiftEquiv q β d s b)) := by
  let x := completedRayGenerator q β d.monoid d.degree
    (fun _ h => d.degree_nonneg h) n hn
  let c (r : Γ) : R := ((q ^ (β n r - β r n) : Rˣ) : R)
  have hc : c (p + s) = c p * c s := by
    have he : β n (p + s) - β (p + s) n =
        (β n p - β p n) + (β n s - β s n) := by
      simp only [map_add, LinearMap.add_apply]
      abel
    simp only [c, he, zpow_add, Units.val_mul]
  let μ : R := ((q ^ β p s : Rˣ) : R)
  let T (r : Γ) := (F).completedTwistedSeriesAction x (c r) H
  have ht : T (p + s) (μ • (τ s a * b)) =
      μ • (τ s (T p a) * T s b) := by
    calc
      _ = μ • T (p + s) (τ s a * b) := _root_.map_smul (T (p + s)) μ _
      _ = μ • (F).completedTwistedSeriesAction x (c p * c s) H (τ s a * b) :=
        congrArg (fun r => μ • (F).completedTwistedSeriesAction x r H (τ s a * b)) hc
      _ = μ • ((F).completedTwistedSeriesAction (c s • x) (c p) H (τ s a) * T s b) :=
        congrArg (fun z => μ • z)
          ((F).completedTwistedSeriesAction_mul x (c p) (c s) H (τ s a) b)
      _ = _ := congrArg (fun z => μ • (z * T s b))
        (completedMonomialRightConjSkew_twistedSeriesAction q β d s n hn (c p) H a).symm
  calc
    _ = shiftedRayAction q β d n hn (p + s) H
        (positiveCompletionShiftEquiv q β d (p + s) (μ • (τ s a * b))) :=
      congrArg (shiftedRayAction q β d n hn (p + s) H)
        (shiftedCompletionMul_positiveCompletionShiftEquiv_skew q β d p s a b)
    _ = positiveCompletionShiftEquiv q β d (p + s)
        (T (p + s) (μ • (τ s a * b))) :=
      shiftedRayAction_twisted_coordinates_skew q β d n hn (p + s) H _
    _ = positiveCompletionShiftEquiv q β d (p + s)
        (μ • (τ s (T p a) * T s b)) :=
      congrArg (positiveCompletionShiftEquiv q β d (p + s)) ht
    _ = d.shiftedCompletionMul (grade q β) p s
        (positiveCompletionShiftEquiv q β d p (T p a))
        (positiveCompletionShiftEquiv q β d s (T s b)) :=
      (shiftedCompletionMul_positiveCompletionShiftEquiv_skew q β d p s (T p a) (T s b)).symm
    _ = _ := congrArg₂ (fun u v => d.shiftedCompletionMul (grade q β) p s u v)
      (shiftedRayAction_twisted_coordinates_skew q β d n hn p H a).symm
      (shiftedRayAction_twisted_coordinates_skew q β d n hn s H b).symm

/-- Every unit ray series preserves multiplication between arbitrary shifted completions. -/
theorem shiftedRayAction_shiftedCompletionMul_skew
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (H : (PowerSeries R)ˣ)
    (a : d.ShiftedCoefficients (grade q β) p)
    (b : d.ShiftedCoefficients (grade q β) s) :
    shiftedRayAction q β d n hn (p + s) H
        (d.shiftedCompletionMul (grade q β) p s a b) =
      d.shiftedCompletionMul (grade q β) p s
        (shiftedRayAction q β d n hn p H a)
        (shiftedRayAction q β d n hn s H b) := by
  simpa only [LinearEquiv.apply_symm_apply] using
    shiftedRayAction_product_coordinates_skew q β d n hn p s H
      ((positiveCompletionShiftEquiv q β d p).symm a)
      ((positiveCompletionShiftEquiv q β d s).symm b)

end Mei.QuantumMonoidAlgebra
