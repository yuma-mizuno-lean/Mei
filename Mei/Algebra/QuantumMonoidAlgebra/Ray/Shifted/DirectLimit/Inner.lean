/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.DirectLimit.SkewAlgebra
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.DirectLimit.Positive.Basic

/-!
# Quantum ray actions are inner on global coefficients

Evaluation of a unit power series in the positive completion gives a unit in the
global coefficient algebra. The existing global ray action is conjugation by
this unit, on every arbitrary-origin chart and on infinite coefficient
families. Neither a spanning nor an alternating hypothesis is required.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ] [DecidableEq Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)
local notation "G" => d.ShiftedDirectLimit (grade q β)
local notation "τ" => completedMonomialRightConjSkew q β d.monoid d.degree
  (fun _ h => d.degree_nonneg h)

private theorem product_coordinates (p s : Γ) (v w : Multiset d.monoid)
    (hp : p - d.coefficientOrigin v ∈ d.monoid)
    (hs : s - d.coefficientOrigin w ∈ d.monoid) (a b : (F).completion) :
    d.toShiftedDirectLimitOfChart (grade q β) p v hp (positiveCompletionShiftEquiv q β d p a) *
        d.toShiftedDirectLimitOfChart (grade q β) s w hs (positiveCompletionShiftEquiv q β d s b) =
      d.toShiftedDirectLimitOfChart (grade q β) (p + s) (v + w)
        (d.add_sub_coefficientOrigin_mem hp hs)
        (positiveCompletionShiftEquiv q β d (p + s)
          (((q ^ β p s : Rˣ) : R) • (τ s a * b))) := by
  have hsum : p + s - d.coefficientOrigin (v + w) ∈ d.monoid :=
    d.add_sub_coefficientOrigin_mem hp hs
  let E := d.toShiftedDirectLimitOfChart (grade q β) (p + s) (v + w) hsum
  have h1 := d.shiftedDirectLimitMul_eq_mul (grade q β)
    (d.toShiftedDirectLimitOfChart (grade q β) p v hp (positiveCompletionShiftEquiv q β d p a))
    (d.toShiftedDirectLimitOfChart (grade q β) s w hs (positiveCompletionShiftEquiv q β d s b))
  have h2 := d.shiftedDirectLimitMul_toShiftedDirectLimitOfChart (grade q β) p s v w hp hs
    (positiveCompletionShiftEquiv q β d p a) (positiveCompletionShiftEquiv q β d s b)
  have h3 := congrArg E (shiftedCompletionMul_positiveCompletionShiftEquiv_skew q β d p s a b)
  exact h1.symm.trans (h2.trans h3)

private theorem chart_coordinates_congr (p r : Γ) (s t : Multiset d.monoid)
    (hpr : p = r) (hst : s = t)
    (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (hr : r - d.coefficientOrigin t ∈ d.monoid) (a : (F).completion) :
    d.toShiftedDirectLimitOfChart (grade q β) p s hp (positiveCompletionShiftEquiv q β d p a) =
      d.toShiftedDirectLimitOfChart (grade q β) r t hr
        (positiveCompletionShiftEquiv q β d r a) := by
  subst t
  exact toShiftedDirectLimitOfChart_positiveCompletionShiftEquiv_congr q β d
    hpr s hp hr a

/-- A positive completed left factor acts in a translated chart by origin conjugation. -/
theorem positiveCompletionToDirectLimit_mul_chart (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (a b : (F).completion) :
    positiveCompletionToDirectLimit q β d a *
        d.toShiftedDirectLimitOfChart (grade q β) p s hp (positiveCompletionShiftEquiv q β d p b) =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (positiveCompletionShiftEquiv q β d p (τ p a * b)) := by
  have h0 : (0 : Γ) - d.coefficientOrigin 0 ∈ d.monoid := d.zero_coefficientOrigin_mem
  have h := product_coordinates q β d 0 p 0 s h0 hp a b
  calc
    _ = d.toShiftedDirectLimitOfChart (grade q β) (0 + p) (0 + s)
        (by simpa only [zero_add] using hp)
        (positiveCompletionShiftEquiv q β d (0 + p) (τ p a * b)) := by
      simpa only [map_zero, LinearMap.zero_apply, zpow_zero, Units.val_one,
        one_smul, ← positiveCompletionToDirectLimit_apply] using h
    _ = _ := chart_coordinates_congr q β d (0 + p) p (0 + s) s
      (zero_add p) (zero_add s) _ hp _

/-- A positive completed right factor is ordinary multiplication in translated coordinates. -/
theorem chart_mul_positiveCompletionToDirectLimit (p : Γ) (s : Multiset d.monoid)
    (hp : p - d.coefficientOrigin s ∈ d.monoid) (a b : (F).completion) :
    d.toShiftedDirectLimitOfChart (grade q β) p s hp (positiveCompletionShiftEquiv q β d p a) *
        positiveCompletionToDirectLimit q β d b =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (positiveCompletionShiftEquiv q β d p (a * b)) := by
  have h0 : (0 : Γ) - d.coefficientOrigin 0 ∈ d.monoid := d.zero_coefficientOrigin_mem
  have h := product_coordinates q β d p 0 s 0 hp h0 a b
  calc
    _ = d.toShiftedDirectLimitOfChart (grade q β) (p + 0) (s + 0)
        (by simpa only [add_zero] using hp)
        (positiveCompletionShiftEquiv q β d (p + 0) (a * b)) := by
      simpa only [map_zero, zpow_zero, Units.val_one, one_smul, completedMonomialRightConjSkew_zero,
        ← positiveCompletionToDirectLimit_apply] using h
    _ = _ := chart_coordinates_congr q β d (p + 0) p (s + 0) s
      (add_zero p) (add_zero s) _ hp _

variable (n : d.monoid) (hn : 0 < d.degree n)

/-- A ray-series unit evaluated in the positive completion and then in global coefficients. -/
def directLimitRayUnit : (PowerSeries R)ˣ →* Gˣ :=
  Units.map ((positiveCompletionToDirectLimit q β d).comp
    ((F).completedAeval (completedRayGenerator q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) n hn))).toMonoidHom

/-- The underlying global ray unit is positive completed evaluation. -/
@[simp]
theorem coe_directLimitRayUnit (H : (PowerSeries R)ˣ) :
    (directLimitRayUnit q β d n hn H : G) =
      positiveCompletionToDirectLimit q β d
        ((F).completedAeval (completedRayGenerator q β d.monoid d.degree
          (fun _ h => d.degree_nonneg h) n hn) (H : PowerSeries R)) := by
  -- Units.map and AlgHom.comp retain the evaluated underlying element.
  rfl

/-- Inverse global ray units evaluate the inverse series. -/
@[simp]
theorem coe_directLimitRayUnit_inv (H : (PowerSeries R)ˣ) :
    (↑(directLimitRayUnit q β d n hn H)⁻¹ : G) =
      positiveCompletionToDirectLimit q β d
        ((F).completedAeval (completedRayGenerator q β d.monoid d.degree
          (fun _ h => d.degree_nonneg h) n hn) (↑(H⁻¹) : PowerSeries R)) := by
  -- The monoid homomorphism maps the inverse unit to the inverse evaluated unit.
  rfl

local notation "ev" => Mei.AlgFiltration.completedAeval (F)
  (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)

private theorem conjugated_chart_coordinates (H : (PowerSeries R)ˣ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (a : (F).completion) :
    positiveCompletionToDirectLimit q β d (ev (H : PowerSeries R)) *
        d.toShiftedDirectLimitOfChart (grade q β) p s hp
          (positiveCompletionShiftEquiv q β d p a) *
        positiveCompletionToDirectLimit q β d (ev (↑(H⁻¹) : PowerSeries R)) =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (positiveCompletionShiftEquiv q β d p
          (ev (PowerSeries.rescale (((q ^ (β n p - β p n) : Rˣ) : R))
            (H : PowerSeries R)) * a * ev (↑(H⁻¹) : PowerSeries R))) := by
  let z := completedRayGenerator q β d.monoid d.degree
    (fun _ h => d.degree_nonneg h) n hn
  let c : R := ((q ^ (β n p - β p n) : Rˣ) : R)
  let u := (F).completedAeval z (H : PowerSeries R)
  let v := (F).completedAeval z (↑(H⁻¹) : PowerSeries R)
  let C (b : (F).completion) := d.toShiftedDirectLimitOfChart (grade q β) p s hp
    (positiveCompletionShiftEquiv q β d p b)
  have htau : τ p u = (F).completedAeval z (PowerSeries.rescale c (H : PowerSeries R)) :=
    (completedMonomialRightConjSkew_completedAeval q β d p n hn
      (H : PowerSeries R)).trans ((F).completedAeval_smul z c (H : PowerSeries R))
  have hleft := positiveCompletionToDirectLimit_mul_chart q β d p s hp u a
  have hright := chart_mul_positiveCompletionToDirectLimit q β d p s hp (τ p u * a) v
  have hprod : positiveCompletionToDirectLimit q β d u * C a *
      positiveCompletionToDirectLimit q β d v = C (τ p u * a * v) :=
    (congrArg (fun b : G => b * positiveCompletionToDirectLimit q β d v) hleft).trans hright
  exact hprod.trans (congrArg (fun b : (F).completion => C (b * a * v)) htau)

private theorem ray_action_chart_coordinates (H : (PowerSeries R)ˣ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (a : (F).completion) :
    directLimitRayAction q β d n hn H
        (d.toShiftedDirectLimitOfChart (grade q β) p s hp
          (positiveCompletionShiftEquiv q β d p a)) =
      d.toShiftedDirectLimitOfChart (grade q β) p s hp
        (positiveCompletionShiftEquiv q β d p
          (ev (PowerSeries.rescale (((q ^ (β n p - β p n) : Rˣ) : R))
            (H : PowerSeries R)) * a * ev (↑(H⁻¹) : PowerSeries R))) := by
  have hchar := directLimitRayAction_toShiftedDirectLimitOfChart q β d n hn H p s hp
    (positiveCompletionShiftEquiv q β d p a)
  have hcoord := congrArg (d.toShiftedDirectLimitOfChart (grade q β) p s hp)
    (shiftedRayAction_coordinates_skew q β d n hn p H a)
  exact hchar.trans hcoord

private theorem ray_action_chart_eq_conjugation (H : (PowerSeries R)ˣ)
    (p : Γ) (s : Multiset d.monoid) (hp : p - d.coefficientOrigin s ∈ d.monoid)
    (a : (F).completion) :
    directLimitRayAction q β d n hn H
        (d.toShiftedDirectLimitOfChart (grade q β) p s hp
          (positiveCompletionShiftEquiv q β d p a)) =
      (directLimitRayUnit q β d n hn H : G) *
        d.toShiftedDirectLimitOfChart (grade q β) p s hp
          (positiveCompletionShiftEquiv q β d p a) *
        (↑(directLimitRayUnit q β d n hn H)⁻¹ : G) := by
  let x := d.toShiftedDirectLimitOfChart (grade q β) p s hp
    (positiveCompletionShiftEquiv q β d p a)
  have hl := congrArg (fun u : G => u * x * (↑(directLimitRayUnit q β d n hn H)⁻¹ : G))
    (coe_directLimitRayUnit q β d n hn H)
  have hr := congrArg (fun v : G =>
    positiveCompletionToDirectLimit q β d (ev (H : PowerSeries R)) * x * v)
    (coe_directLimitRayUnit_inv q β d n hn H)
  exact (ray_action_chart_coordinates q β d n hn H p s hp a).trans
    ((conjugated_chart_coordinates q β d n hn H p s hp a).symm.trans
      (hl.trans hr).symm)

/-- The existing global linear ray action is conjugation by its evaluated ray unit. -/
theorem directLimitRayAction_eq_conjugation (H : (PowerSeries R)ˣ) (x : G) :
    directLimitRayAction q β d n hn H x =
      (directLimitRayUnit q β d n hn H : G) * x *
        (↑(directLimitRayUnit q β d n hn H)⁻¹ : G) := by
  refine (d.exists_toShiftedDirectLimit (grade q β) x).elim fun s hs => ?_
  refine hs.elim fun b hb => ?_
  let p := d.coefficientOrigin s
  let a := (positiveCompletionShiftEquiv q β d p).symm b
  have hp : p - d.coefficientOrigin s ∈ d.monoid := by simp only [p, sub_self, zero_mem]
  have hcoord := congrArg (d.toShiftedDirectLimitOfChart (grade q β) p s hp)
    ((positiveCompletionShiftEquiv q β d p).apply_symm_apply b)
  have hchart : d.toShiftedDirectLimitOfChart (grade q β) p s hp b =
      d.toShiftedDirectLimit (grade q β) s b := by
    rw [PositiveDegrees.toShiftedDirectLimitOfChart_apply,
      PositiveDegrees.shiftedCompletedInclusion_refl]
  have hx : d.toShiftedDirectLimitOfChart (grade q β) p s hp
      (positiveCompletionShiftEquiv q β d p a) = x := hcoord.trans (hchart.trans hb)
  have h := ray_action_chart_eq_conjugation q β d n hn H p s hp a
  exact (congrArg (directLimitRayAction q β d n hn H) hx).symm.trans
    (h.trans (congrArg (fun y : G => (directLimitRayUnit q β d n hn H : G) * y *
      (↑(directLimitRayUnit q β d n hn H)⁻¹ : G)) hx))

/-- The global algebra action is inner, with no alternating or spanning hypothesis. -/
theorem directLimitRaySkewAlgAction_eq_conjugation (H : (PowerSeries R)ˣ) (x : G) :
    directLimitRaySkewAlgAction q β d n hn H x =
      (directLimitRayUnit q β d n hn H : G) * x *
        (↑(directLimitRayUnit q β d n hn H)⁻¹ : G) :=
  (directLimitRaySkewAlgAction_apply q β d n hn H x).trans
    (directLimitRayAction_eq_conjugation q β d n hn H x)

end Mei.QuantumMonoidAlgebra
