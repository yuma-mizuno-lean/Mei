/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.QuantumMonoidAlgebra.Ray.Shifted.Quotient
public import Mei.Algebra.QuantumMonoidAlgebra.Shifted.Inclusion
public import Mei.Algebra.Group.Action.Semiconj

/-!
# Quantum ray actions respect inclusions of shifted supports

Changing the origin of a translated support keeps every ambient coefficient
unchanged. The shifted ray actions commute with these inclusions, so the action
on a coefficient is independent of any comparable choice of origin. The original
finite relative quotients inherit the same compatibility at each common cutoff.
The commutation character depends on the skew part of the bilinear form, so no
alternation assumption is needed.
-/

public section
noncomputable section

namespace Mei.QuantumMonoidAlgebra

variable {R Γ : Type*} [CommRing R] [AddCommGroup Γ]
  (q : Rˣ) (β : LinearMap.BilinForm ℤ Γ) (d : PositiveDegrees Γ)

local notation "F" => positiveFiltration q β d.monoid d.degree (fun _ h => d.degree_nonneg h)

/-- Ray actions commute with ambient-coefficient-preserving inclusions of translated supports. -/
private theorem inclusion_action_coordinates
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (hps : p - s ∈ d.monoid)
    (H : (PowerSeries R)ˣ) (a : (F).completion) :
    d.shiftedCompletedInclusion (grade q β) p s hps
        (shiftedRayAction q β d n hn p H
          (positiveCompletionShiftEquiv q β d p a)) =
      shiftedRayAction q β d n hn s H
        (d.shiftedCompletedInclusion (grade q β) p s hps
          (positiveCompletionShiftEquiv q β d p a)) := by
  have hc : ((q ^ ((β n p - β p n)) : Rˣ) : R) =
      ((q ^ ((β n s - β s n)) : Rˣ) : R) * ((q ^ ((β n (p - s) - β (p - s) n)) : Rˣ) : R) := by
    have he : (β n p - β p n) = (β n s - β s n) + (β n (p - s) - β (p - s) n) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [he, zpow_add, Units.val_mul]
  have he := (F).completedAeval_mul_of_semiconj
    (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
    ((F).toCompletion (positiveMonomial q β d.monoid ⟨p - s, hps⟩))
    (((q ^ ((β n (p - s) - β (p - s) n)) : Rˣ) : R))
    (completedRayGenerator_semiconjBy_skew q β d.monoid d.degree
      (fun _ h => d.degree_nonneg h) n ⟨p - s, hps⟩ hn)
    (PowerSeries.rescale (((q ^ ((β n s - β s n)) : Rˣ) : R)) (H : PowerSeries R))
  have hres :
      PowerSeries.rescale (((q ^ ((β n (p - s) - β (p - s) n)) : Rˣ) : R))
          (PowerSeries.rescale (((q ^ ((β n s - β s n)) : Rˣ) : R)) (H : PowerSeries R)) =
        PowerSeries.rescale (((q ^ ((β n p - β p n)) : Rˣ) : R)) (H : PowerSeries R) :=
    (PowerSeries.rescale_rescale _ _ _).trans
      (congrArg (fun c : R => PowerSeries.rescale c (H : PowerSeries R)) hc.symm)
  have he' := he.trans (congrArg (fun G : PowerSeries R =>
    (F).toCompletion (positiveMonomial q β d.monoid ⟨p - s, hps⟩) *
      (F).completedAeval
        (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn) G)
    hres)
  have hm := SemiconjBy.smul_mul_mul (R := R) (A := (F).completion) he'.symm
    (((q ^ β s (p - s))⁻¹ : Rˣ) : R) a
    ((F).completedAeval
      (completedRayGenerator q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn)
      (↑(H⁻¹) : PowerSeries R))
  -- Express the inclusion as multiplication by the shift monomial and commute
  -- the twisted ray factor across that monomial using semiconjugacy.
  calc
    _ = _ := congrArg (d.shiftedCompletedInclusion (grade q β) p s hps)
      (shiftedRayAction_coordinates_skew q β d n hn p H a)
    _ = _ := shiftedCompletedInclusion_positiveCompletionShiftEquiv q β d p s hps _
    _ = _ := congrArg (positiveCompletionShiftEquiv q β d s) hm
    _ = _ := (shiftedRayAction_coordinates_skew q β d n hn s H _).symm
    _ = _ := (congrArg (shiftedRayAction q β d n hn s H)
      (shiftedCompletedInclusion_positiveCompletionShiftEquiv q β d p s hps a)).symm

/-- Ray actions commute with inclusions for arbitrary completed shifted coefficients. -/
theorem shiftedCompletedInclusion_shiftedRayAction
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (hps : p - s ∈ d.monoid)
    (H : (PowerSeries R)ˣ) (a : d.ShiftedCoefficients (grade q β) p) :
    d.shiftedCompletedInclusion (grade q β) p s hps
        (shiftedRayAction q β d n hn p H a) =
      shiftedRayAction q β d n hn s H
        (d.shiftedCompletedInclusion (grade q β) p s hps a) := by
  have he := (positiveCompletionShiftEquiv q β d p).apply_symm_apply a
  calc
    _ = _ := (congrArg (fun z : d.ShiftedCoefficients (grade q β) p =>
      d.shiftedCompletedInclusion (grade q β) p s hps (shiftedRayAction q β d n hn p H z))
      he).symm
    _ = _ := inclusion_action_coordinates q β d n hn p s hps H
      ((positiveCompletionShiftEquiv q β d p).symm a)
    _ = _ := congrArg (fun z : d.ShiftedCoefficients (grade q β) p =>
      shiftedRayAction q β d n hn s H
        (d.shiftedCompletedInclusion (grade q β) p s hps z)) he

/-- For a nonnegative shift, the natural positive inclusion intertwines the algebra ray action. -/
theorem shiftedToPositiveCompletion_shiftedRayAction
    (n : d.monoid) (hn : 0 < d.degree n) (p : d.monoid)
    (H : (PowerSeries R)ˣ) (a : d.ShiftedCoefficients (grade q β) p) :
    shiftedToPositiveCompletion q β d p (shiftedRayAction q β d n hn p H a) =
      completedRayAction q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn H
        (shiftedToPositiveCompletion q β d p a) := by
  have hi (z : d.ShiftedCoefficients (grade q β) p) :
      positiveCompletionShiftEquiv q β d 0 (shiftedToPositiveCompletion q β d p z) =
        d.shiftedCompletedInclusion (grade q β) p 0
          (by simpa only [sub_zero] using p.property) z :=
    (congrArg (positiveCompletionShiftEquiv q β d 0)
      (shiftedToPositiveCompletion_apply q β d p z)).trans
      ((positiveCompletionShiftEquiv q β d 0).apply_symm_apply _)
  apply (positiveCompletionShiftEquiv q β d 0).injective
  -- Compare at origin zero, where the shifted action is the positive algebra action.
  calc
    _ = _ := hi _
    _ = _ := shiftedCompletedInclusion_shiftedRayAction q β d n hn p 0
      (by simpa only [sub_zero] using p.property) H a
    _ = _ := congrArg (shiftedRayAction q β d n hn 0 H) (hi a).symm
    _ = _ := shiftedRayAction_zero q β d n hn H (shiftedToPositiveCompletion q β d p a)

/-- Reverse ray crossings also commute with inclusions of translated supports. -/
theorem shiftedCompletedInclusion_shiftedRayAction_symm
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (hps : p - s ∈ d.monoid)
    (H : (PowerSeries R)ˣ) (a : d.ShiftedCoefficients (grade q β) p) :
    d.shiftedCompletedInclusion (grade q β) p s hps
        ((shiftedRayAction q β d n hn p H).symm a) =
      (shiftedRayAction q β d n hn s H).symm
        (d.shiftedCompletedInclusion (grade q β) p s hps a) := by
  simpa only [shiftedRayAction_inv] using
    shiftedCompletedInclusion_shiftedRayAction q β d n hn p s hps (H⁻¹) a

/-- Reverse crossings intertwine the natural positive-completion inclusion as well. -/
theorem shiftedToPositiveCompletion_shiftedRayAction_symm
    (n : d.monoid) (hn : 0 < d.degree n) (p : d.monoid)
    (H : (PowerSeries R)ˣ) (a : d.ShiftedCoefficients (grade q β) p) :
    shiftedToPositiveCompletion q β d p ((shiftedRayAction q β d n hn p H).symm a) =
      (completedRayAction q β d.monoid d.degree (fun _ h => d.degree_nonneg h) n hn H).symm
        (shiftedToPositiveCompletion q β d p a) := by
  simpa only [shiftedRayAction_inv, map_inv, AlgEquiv.aut_inv, LinearEquiv.coe_inv] using
    shiftedToPositiveCompletion_shiftedRayAction q β d n hn p (H⁻¹) a

/-- At each common relative cutoff, finite ray actions commute with support inclusions. -/
@[simp]
theorem shiftedQuotientMap_shiftedRayQuotientAction
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (hps : p - s ∈ d.monoid)
    (k : ℕ) (H : (PowerSeries R)ˣ)
    (a : (d.shiftedFiltration (grade q β) p).quotient k) :
    d.shiftedQuotientMap (grade q β) p s hps k
        (shiftedRayQuotientAction q β d n hn p k H a) =
      shiftedRayQuotientAction q β d n hn s k H
        (d.shiftedQuotientMap (grade q β) p s hps k a) := by
  obtain ⟨b, rfl⟩ := (d.shiftedFiltration (grade q β) p).projection_surjective k a
  simp only [shiftedRayQuotientAction_projection, ← d.projection_shiftedCompletedInclusion,
    shiftedCompletedInclusion_shiftedRayAction q β d]

/-- Reverse finite ray crossings commute with inclusions at the same relative cutoff. -/
@[simp]
theorem shiftedQuotientMap_shiftedRayQuotientAction_symm
    (n : d.monoid) (hn : 0 < d.degree n) (p s : Γ) (hps : p - s ∈ d.monoid)
    (k : ℕ) (H : (PowerSeries R)ˣ)
    (a : (d.shiftedFiltration (grade q β) p).quotient k) :
    d.shiftedQuotientMap (grade q β) p s hps k
        ((shiftedRayQuotientAction q β d n hn p k H).symm a) =
      (shiftedRayQuotientAction q β d n hn s k H).symm
        (d.shiftedQuotientMap (grade q β) p s hps k a) := by
  simpa only [shiftedRayQuotientAction_inv] using
    shiftedQuotientMap_shiftedRayQuotientAction q β d n hn p s hps k (H⁻¹) a

end Mei.QuantumMonoidAlgebra
