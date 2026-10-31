/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Affine.FiniteRay.Basic

/-!
# Cutting off the final part of a finite affine ray

`FiniteAffineRay.truncate` makes a point of a ray its new endpoint. It retains
the incoming half-line, translates its parameters, and absorbs all later bends
into the new final direction. A cut at a bend uses its incoming direction.
The construction works for affine torsors, including stationary segments.

This is the geometric operation for cutting a broken line before its last
change of decoration. The hinge presentation and `directionAt` come from
`Mei.Geometry.Affine.FiniteRay.Basic`; filtering and translating finite bend
data use Mathlib's `Finsupp.filter` and `Finsupp.mapDomain`.
-/

public noncomputable section

open Set Filter

namespace Mei.FiniteAffineRay

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Retain the part of a ray before time `t`, with the new endpoint at parameter
zero. Bends at or after the cut are absorbed into the final direction. -/
def truncate (β : FiniteAffineRay V P) (t : ℝ) : FiniteAffineRay V P := by
  classical
  refine ⟨β t, β.directionAt t,
    (β.bends.filter (· < t)).mapDomain (fun b => b - t), ?_⟩
  intro b hb
  rw [Finsupp.mapDomain_support_of_injective (sub_left_injective),
    Finset.mem_image] at hb
  obtain ⟨s, hs, rfl⟩ := hb
  rw [Finsupp.support_filter, Finset.mem_filter] at hs
  exact sub_neg.mpr hs.2

/-- Cutting a ray makes its value at the cut the new endpoint. -/
@[simp]
theorem endpoint_truncate (β : FiniteAffineRay V P) (t : ℝ) :
    (β.truncate t).endpoint = β t := (rfl)

/-- The new final direction is the incoming direction at the cut. -/
@[simp]
theorem direction_truncate (β : FiniteAffineRay V P) (t : ℝ) :
    (β.truncate t).direction = β.directionAt t := (rfl)

/-- The retained bend increments have their times translated by the cut. -/
theorem bends_truncate (β : FiniteAffineRay V P) (t : ℝ) :
    (β.truncate t).bends = (β.bends.filter (· < t)).mapDomain (fun b => b - t) := (rfl)

/-- A bend survives exactly when its original time precedes the cut. -/
@[simp]
theorem bends_truncate_apply (β : FiniteAffineRay V P) (t s : ℝ) :
    (β.truncate t).bends s = if s < 0 then β.bends (s + t) else 0 := by
  classical
  rw [bends_truncate]
  have he : s = (s + t) - t := by abel
  conv_lhs => rw [he]
  rw [Finsupp.mapDomain_apply_of_injective sub_left_injective, Finsupp.filter_apply]
  simp only [add_lt_iff_neg_right]

private theorem sum_bends_truncate (β : FiniteAffineRay V P) (t : ℝ)
    (g : ℝ → V → V) (hzero : ∀ b, g b 0 = 0)
    (hadd : ∀ b x y, g b (x + y) = g b x + g b y) :
    (β.truncate t).bends.sum g =
      β.bends.sum (fun b w => if b < t then g (b - t) w else 0) := by
  classical
  rw [bends_truncate, Finsupp.sum_mapDomain_index hzero hadd,
    Finsupp.sum_filter_index, Finsupp.support_filter, Finset.sum_filter, Finsupp.sum]

/-- On the retained half-line, cutting translates time and preserves every
point of the original path, including the new endpoint. -/
@[simp]
theorem truncate_apply (β : FiniteAffineRay V P) (t : ℝ) {s : ℝ} (hs : s ≤ 0) :
    β.truncate t s = β (s + t) := by
  classical
  rw [eval_def, endpoint_truncate, direction_truncate,
    sum_bends_truncate β t _ (fun _ => smul_zero _)
      (fun _ _ _ => smul_add _ _ _), directionAt_def, eval_def β t,
    eval_def β (s + t), vadd_vadd]
  congr 1
  simp only [Finsupp.sum, smul_add, Finset.smul_sum]
  have hhinge (b : ℝ) (w : V) :
      (if b < t then max (b - t - s) 0 • w else 0) -
        s • (if t ≤ b then w else 0) + max (b - t) 0 • w =
          max (b - (s + t)) 0 • w := by
    by_cases hbt : b < t
    · simp only [hbt, hbt.not_ge, ite_true, ite_false, smul_zero,
        sub_zero, max_eq_right (sub_nonpos.mpr hbt.le), zero_smul, add_zero]
      congr 2
      ring
    · have htb : t ≤ b := le_of_not_gt hbt
      rw [ite_eq_right hbt, ite_eq_left htb, max_eq_left (sub_nonneg.mpr htb),
        max_eq_left (by linarith)]
      module
  have hsum := Finset.sum_congr (s₁ := β.bends.support) rfl
    (fun b _ => hhinge b (β.bends b))
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [← hsum]
  module

/-- Directions on the retained half-line are the original incoming directions
at the translated parameters. -/
@[simp]
theorem directionAt_truncate (β : FiniteAffineRay V P) (t : ℝ) {s : ℝ} (hs : s ≤ 0) :
    (β.truncate t).directionAt s = β.directionAt (s + t) := by
  classical
  rw [directionAt_def, direction_truncate,
    sum_bends_truncate β t _ (fun _ => by simp)
      (fun _ _ _ => by split_ifs <;> simp), directionAt_def, directionAt_def]
  rw [add_assoc, ← Finsupp.sum_add]
  congr 1
  apply Finsupp.sum_congr
  intro b _
  by_cases hbt : b < t
  · have hnot : ¬t ≤ b := hbt.not_ge
    simp only [hbt, hnot, ite_true, ite_false, zero_add]
    have he : (s ≤ b - t) ↔ (s + t ≤ b) := by constructor <;> intro h <;> linarith
    simp only [he]
  · have htb : t ≤ b := le_of_not_gt hbt
    simp [hbt, htb, show s + t ≤ b by linarith]

/-- Cutting preserves the direction of the incoming affine tail. -/
@[simp]
theorem incomingDirection_truncate (β : FiniteAffineRay V P) (t : ℝ) :
    (β.truncate t).incomingDirection = β.incomingDirection := by
  classical
  rw [incomingDirection_def, direction_truncate,
    sum_bends_truncate β t _ (fun _ => rfl) (fun _ _ _ => rfl),
    directionAt_def, incomingDirection_def, add_assoc, ← Finsupp.sum_add]
  congr 1
  apply Finsupp.sum_congr
  intro b _
  by_cases hbt : b < t <;> simp [hbt, le_of_not_gt, not_le.mpr] at *

/-- Cutting at the original endpoint leaves the ray unchanged. -/
@[simp]
theorem truncate_zero (β : FiniteAffineRay V P) : β.truncate 0 = β := by
  apply FiniteAffineRay.ext
  · exact β.eval_zero
  · rw [direction_truncate, directionAt_def]
    have hz : β.bends.sum (fun b w => if 0 ≤ b then w else 0) = 0 := by
      rw [Finsupp.sum]
      apply Finset.sum_eq_zero
      intro b hb
      simp only [ite_eq_right (β.bend_neg b hb).not_ge]
    rw [hz, add_zero]
  · ext s
    rw [bends_truncate_apply, add_zero]
    by_cases hs : s < 0
    · exact ite_eq_left hs
    · rw [ite_eq_right hs]
      exact (Finsupp.notMem_support_iff.mp (fun h => hs (β.bend_neg s h))).symm

/-- Cutting twice in the retained half-line is the same as cutting once at the
sum of the two parameters. -/
@[simp]
theorem truncate_truncate (β : FiniteAffineRay V P) (t : ℝ) {s : ℝ} (hs : s ≤ 0) :
    (β.truncate t).truncate s = β.truncate (s + t) := by
  apply FiniteAffineRay.ext
  · exact β.truncate_apply t hs
  · exact β.directionAt_truncate t hs
  · ext u
    simp only [bends_truncate_apply]
    by_cases hu : u < 0
    · simp [hu, show u + s < 0 by linarith, add_assoc]
    · simp [hu]

/-- Source admission of the incoming tail is preserved in both directions.
The source is an arbitrary subset of the affine space. -/
@[simp↓]
theorem eventually_truncate_mem_iff (β : FiniteAffineRay V P) (t : ℝ) (C : Set P) :
    (∀ᶠ s : ℝ in atBot, β.truncate t s ∈ C) ↔ ∀ᶠ s : ℝ in atBot, β s ∈ C := by
  simp only [eventually_atBot]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨min t (b + t), fun s hs => ?_⟩
    have hst : s - t ≤ 0 := by have := hs.trans (min_le_left _ _); linarith
    have hsb : s - t ≤ b := by have := hs.trans (min_le_right _ _); linarith
    simpa only [truncate_apply β t hst, sub_add_cancel] using hb (s - t) hsb
  · rintro ⟨b, hb⟩
    refine ⟨min 0 (b - t), fun s hs => ?_⟩
    rw [truncate_apply β t (hs.trans (min_le_left _ _))]
    exact hb (s + t) (by have := hs.trans (min_le_right _ _); linarith)

end Mei.FiniteAffineRay
