/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Sweep.Itinerary
public import Mei.Geometry.Affine.FiniteRay.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Realizing backward itineraries as finite affine rays

The elapsed times of a backward itinerary give negative path parameters, with
parameter zero at the endpoint. If all elapsed times are positive, inserting
the successive direction differences at these parameters gives a continuous
finite affine ray. Its finite segments pass through the computed encounter
points, and its incoming half-line starts at the last encounter with the
prescribed incoming direction. Equal consecutive directions retain the encounter
while contributing no geometric bend.

This connects `backwardPoint` and `backwardTime` with `FiniteAffineRay`; selected
support incidences can consequently be read on an actual continuous path.
Eventual source admission agrees on the incoming half-line and the realization
at negative infinity.
Avoidance and coefficient propagation remain separate conditions. The backward
parameterization follows Carl–Pumperla–Siebert, *A tropical view on
Landau–Ginzburg models*, §4 (arXiv:2205.07753v2).
-/

public noncomputable section

namespace Mei.Convex

open Set Filter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {n : ℕ} (f : Fin n → V →L[ℝ] ℝ) (c : Fin n → ℝ) (u : Fin n → V)

/-- Path parameters of successive backward encounters, obtained by subtracting
elapsed times from zero. Each parameter is affine in the endpoint. -/
def backwardParameter : Fin (n + 1) → V →ᴬ[ℝ] ℝ :=
  Fin.partialSum (fun j => -backwardTime f c u j)

/-- The endpoint is at parameter zero. -/
@[simp]
theorem backwardParameter_zero (Q : V) : backwardParameter f c u 0 Q = 0 := by
  simp [backwardParameter]

/-- The next encounter occurs one elapsed time earlier. -/
@[simp]
theorem backwardParameter_succ (j : Fin n) (Q : V) :
    backwardParameter f c u j.succ Q =
      backwardParameter f c u j.castSucc Q - backwardTime f c u j Q := by
  simp [backwardParameter, Fin.partialSum_succ, sub_eq_add_neg]

/-- Nonnegative elapsed times weakly order the encounters backwards. -/
theorem antitone_backwardParameter (Q : V)
    (hQ : ∀ j, 0 ≤ backwardTime f c u j Q) :
    Antitone (fun j => backwardParameter f c u j Q) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro j
  rw [backwardParameter_succ]
  exact sub_le_self _ (hQ j)

/-- Positive elapsed times strictly order the encounters backwards. -/
theorem strictAnti_backwardParameter (Q : V)
    (hpos : ∀ j, 0 < backwardTime f c u j Q) :
    StrictAnti (fun j => backwardParameter f c u j Q) := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro j
  rw [backwardParameter_succ]
  exact sub_lt_self _ (hpos j)

/-- Between encounters with a constant backward direction, propagation is one
straight segment whose elapsed time is the difference of cumulative parameters.
The formula also holds for zero or negative elapsed times. -/
theorem backwardPoint_eq_add_of_constant (Q : V) (a b : Fin (n + 1))
    (hab : a ≤ b) (w : V)
    (hw : ∀ j : Fin n, a ≤ j.castSucc → j.succ ≤ b → u j = w) :
    backwardPoint f c u b Q = backwardPoint f c u a Q +
      (backwardParameter f c u a Q - backwardParameter f c u b Q) • w := by
  induction b using Fin.induction with
  | zero =>
    have ha : a = 0 := le_antisymm hab (Fin.zero_le a)
    simp [ha]
  | succ j ih =>
    by_cases ha : a = j.succ
    · simp [ha]
    · have haj : a ≤ j.castSucc := by
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc,
          Fin.ext_iff] at hab ha ⊢
        omega
      rw [backwardPoint_succ_apply, hw j haj le_rfl,
        ih haj (fun l hl hl' => hw l hl (hl'.trans (Fin.castSucc_le_succ j))),
        backwardParameter_succ]
      module

variable (v : Fin (n + 1) → V) (Q : V)
  (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q)

include hpos in
private theorem parameter_neg (j : Fin n) :
    backwardParameter f c (fun j => v j.castSucc) j.succ Q < 0 := by
  simpa using strictAnti_backwardParameter f c (fun j => v j.castSucc) Q hpos
    (Fin.succ_pos j)

/-- Partial insertion of bends, specific to the selected backward itinerary. -/
private def realizationStage : Fin (n + 1) → FiniteAffineRay V V :=
  Fin.induction (FiniteAffineRay.straight Q (v 0)) fun j β =>
    β.insert (backwardParameter f c (fun j => v j.castSucc) j.succ Q)
      (v j.succ - v j.castSucc) (parameter_neg f c v Q hpos j)

private theorem stage_zero :
    realizationStage f c v Q hpos 0 = FiniteAffineRay.straight Q (v 0) := by
  simp [realizationStage]

private theorem stage_succ (j : Fin n) :
    realizationStage f c v Q hpos j.succ =
      (realizationStage f c v Q hpos j.castSucc).insert
        (backwardParameter f c (fun j => v j.castSucc) j.succ Q)
        (v j.succ - v j.castSucc) (parameter_neg f c v Q hpos j) := by
  simp [realizationStage, Fin.induction_succ]

private theorem stage_endpoint (j : Fin (n + 1)) :
    (realizationStage f c v Q hpos j).endpoint = Q := by
  induction j using Fin.induction with
  | zero => simp [stage_zero]
  | succ j ih => simpa [stage_succ] using ih

private theorem stage_direction (j : Fin (n + 1)) :
    (realizationStage f c v Q hpos j).direction = v 0 := by
  induction j using Fin.induction with
  | zero => simp [stage_zero]
  | succ j ih => simpa [stage_succ] using ih

private theorem stage_incomingDirection (j : Fin (n + 1)) :
    (realizationStage f c v Q hpos j).incomingDirection = v j := by
  induction j using Fin.induction with
  | zero => simp [stage_zero]
  | succ j ih => simp [stage_succ, ih]

private theorem stage_incomingReference (j : Fin (n + 1)) :
    (realizationStage f c v Q hpos j).incomingReference =
      backwardPoint f c (fun j => v j.castSucc) j Q +
        backwardParameter f c (fun j => v j.castSucc) j Q • v j := by
  induction j using Fin.induction with
  | zero => simp [stage_zero]
  | succ j ih =>
    rw [stage_succ, FiniteAffineRay.incomingReference_insert, ih,
      backwardPoint_succ_apply, backwardParameter_succ]
    simp only [vadd_eq_add]
    module

private theorem stage_bends_eq (j : Fin (n + 1)) :
    (realizationStage f c v Q hpos j).bends =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.val < j.val),
        Finsupp.single (backwardParameter f c (fun j => v j.castSucc) a.succ Q)
          (v a.succ - v a.castSucc) := by
  classical
  induction j using Fin.induction with
  | zero => simp [stage_zero]
  | succ j ih =>
    have he : Finset.univ.filter (fun a : Fin n => a.val < j.succ.val) =
        insert j (Finset.univ.filter (fun a : Fin n => a.val < j.castSucc.val)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
      omega
    rw [stage_succ, FiniteAffineRay.bends_insert, ih, he, Finset.sum_insert]
    · exact add_comm _ _
    · simp

private theorem stage_bends (j : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ (realizationStage f c v Q hpos j).bends.support) :
    ∃ a : Fin n, a.val < j.val ∧
      t = backwardParameter f c (fun j => v j.castSucc) a.succ Q := by
  rw [stage_bends_eq] at ht
  obtain ⟨a, ha, ht⟩ := Finsupp.mem_support_finsetSum t ht
  exact ⟨a, (Finset.mem_filter.mp ha).2,
    Finset.mem_singleton.mp (Finsupp.support_single_subset ht)⟩

private theorem stage_before (j : Fin (n + 1)) (t : ℝ)
    (ht : t ≤ backwardParameter f c (fun j => v j.castSucc) j Q) :
    realizationStage f c v Q hpos j t =
      backwardPoint f c (fun j => v j.castSucc) j Q +
        (backwardParameter f c (fun j => v j.castSucc) j Q - t) • v j := by
  rw [FiniteAffineRay.eval_of_le_bends, stage_incomingDirection, stage_incomingReference]
  · simp only [vadd_eq_add]
    module
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := stage_bends f c v Q hpos j hb
    exact ht.trans ((strictAnti_backwardParameter f c (fun j => v j.castSucc) Q hpos).antitone
      (by simpa only [Fin.le_iff_val_le_val, Fin.val_succ] using Nat.succ_le_iff.mpr ha))

private theorem stage_stable (j : Fin (n + 1)) (a : Fin (n + 1)) (haj : a ≤ j)
    (t : ℝ) (ht : backwardParameter f c (fun j => v j.castSucc) a Q ≤ t) :
    realizationStage f c v Q hpos j t = realizationStage f c v Q hpos a t := by
  induction j using Fin.induction with
  | zero =>
    have ha : a = 0 := le_antisymm haj (Fin.zero_le a)
    subst a
    rfl
  | succ j ih =>
    by_cases ha : a = j.succ
    · rw [ha]
    · have haj' : a ≤ j.castSucc := by
          simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc,
            Fin.ext_iff] at haj ha ⊢
          omega
      have hb : backwardParameter f c (fun j => v j.castSucc) j.succ Q ≤ t :=
        ((strictAnti_backwardParameter f c (fun j => v j.castSucc) Q hpos).antitone
          haj).trans ht
      rw [stage_succ, FiniteAffineRay.insert_apply, max_eq_right (sub_nonpos.mpr hb),
        zero_smul, zero_vadd]
      exact ih haj'

/-- The finite affine ray realizing a positive-time backward itinerary. The last
entry of `v` specifies the direction of the unbounded incoming segment. -/
def backwardRay : FiniteAffineRay V V :=
  realizationStage f c v Q hpos (Fin.last n)

/-- The realized ray ends at the selected endpoint. -/
@[simp]
theorem endpoint_backwardRay : (backwardRay f c v Q hpos).endpoint = Q :=
  stage_endpoint f c v Q hpos _

/-- The segment adjacent to the endpoint has the first prescribed direction. -/
@[simp]
theorem direction_backwardRay : (backwardRay f c v Q hpos).direction = v 0 :=
  stage_direction f c v Q hpos _

/-- The unbounded incoming segment has the last prescribed direction. -/
@[simp]
theorem incomingDirection_backwardRay :
    (backwardRay f c v Q hpos).incomingDirection = v (Fin.last n) :=
  stage_incomingDirection f c v Q hpos _

/-- The incoming affine reference is obtained from the last encounter by continuing
its incoming segment to time zero. -/
@[simp]
theorem incomingReference_backwardRay :
    (backwardRay f c v Q hpos).incomingReference =
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
        backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q • v (Fin.last n) :=
  stage_incomingReference f c v Q hpos _

/-- On a finite segment, the realization has prescribed direction `v j.castSucc`
and velocity `-v j.castSucc` as the parameter increases. It passes through the
computed encounter point at the segment's right endpoint. -/
theorem backwardRay_apply_segment (j : Fin n) (t : ℝ)
    (hlo : backwardParameter f c (fun j => v j.castSucc) j.succ Q ≤ t)
    (hhi : t ≤ backwardParameter f c (fun j => v j.castSucc) j.castSucc Q) :
    backwardRay f c v Q hpos t =
      backwardPoint f c (fun j => v j.castSucc) j.castSucc Q +
        (backwardParameter f c (fun j => v j.castSucc) j.castSucc Q - t) • v j.castSucc := by
  rw [backwardRay, stage_stable f c v Q hpos (Fin.last n) j.succ (Fin.le_last _) t hlo,
    stage_succ, FiniteAffineRay.insert_apply,
    max_eq_right (sub_nonpos.mpr hlo), zero_smul, zero_vadd]
  exact stage_before f c v Q hpos j.castSucc t hhi

/-- Before the last encounter, the realization is the prescribed incoming half-line. -/
theorem backwardRay_apply_incoming (t : ℝ)
    (ht : t ≤ backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q) :
    backwardRay f c v Q hpos t =
      backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
        (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - t) • v (Fin.last n) :=
  stage_before f c v Q hpos (Fin.last n) t ht

/-- Eventual source admission of the backward incoming ray is equivalent to
source admission of the realized path at negative infinity. The source may be
an arbitrary set. -/
theorem backwardRay_eventually_mem_iff (C : Set V) :
    (∀ᶠ t : ℝ in atBot, backwardRay f c v Q hpos t ∈ C) ↔
      ∀ᶠ s : ℝ in atTop,
        backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q + s • v (Fin.last n) ∈ C := by
  have htop : Tendsto
      (fun s : ℝ => backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - s)
      atTop atBot := by
    simpa only [sub_eq_add_neg] using
      tendsto_atBot_add_const_left atTop
        (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q) tendsto_neg_atTop_atBot
  have hbot : Tendsto
      (fun t : ℝ => backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - t)
      atBot atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_left atBot
        (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q) tendsto_neg_atBot_atTop
  have he : ∀ᶠ t : ℝ in atBot,
      backwardRay f c v Q hpos t =
        backwardPoint f c (fun j => v j.castSucc) (Fin.last n) Q +
          (backwardParameter f c (fun j => v j.castSucc) (Fin.last n) Q - t) • v (Fin.last n) :=
    (eventually_le_atBot _).mono fun t ht =>
      backwardRay_apply_incoming f c v Q hpos t ht
  constructor
  · intro h
    filter_upwards [htop.eventually h, htop.eventually he] with s hs he'
    rw [he'] at hs
    simpa only [sub_sub_cancel] using hs
  · intro h
    filter_upwards [hbot.eventually h, he] with t ht he'
    rwa [he']

/-- Every computed encounter is attained at its cumulative negative parameter. -/
@[simp]
theorem backwardRay_apply_parameter (j : Fin (n + 1)) :
    backwardRay f c v Q hpos (backwardParameter f c (fun j => v j.castSucc) j Q) =
      backwardPoint f c (fun j => v j.castSucc) j Q := by
  rw [backwardRay, stage_stable f c v Q hpos (Fin.last n) j (Fin.le_last _) _ le_rfl,
    stage_before f c v Q hpos j _ le_rfl, sub_self, zero_smul, add_zero]

/-- The bend data are the successive direction differences at the recorded
parameters. A crossing with equal adjacent directions contributes zero. -/
@[simp]
theorem bends_backwardRay :
    (backwardRay f c v Q hpos).bends =
      ∑ j : Fin n, Finsupp.single
        (backwardParameter f c (fun j => v j.castSucc) j.succ Q)
        (v j.succ - v j.castSucc) := by
  rw [backwardRay, stage_bends_eq]
  congr 1
  exact Finset.filter_true_of_mem fun j _ => by simp

/-- At each encounter parameter, the incoming direction is the corresponding
prescribed direction. This includes recorded encounters with no geometric bend. -/
@[simp]
theorem directionAt_backwardRay_parameter (j : Fin (n + 1)) :
    (backwardRay f c v Q hpos).directionAt
      (backwardParameter f c (fun j => v j.castSucc) j Q) = v j := by
  classical
  have hanti := strictAnti_backwardParameter f c (fun j => v j.castSucc) Q hpos
  let τ := fun j => backwardParameter f c (fun j => v j.castSucc) j Q
  rw [FiniteAffineRay.directionAt_def, direction_backwardRay, bends_backwardRay,
    ← Finsupp.sum_finsetSum_index (h := fun b x => if τ j ≤ b then x else 0)
      (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  simp only [Finsupp.sum_single_index, ite_self, τ, hanti.le_iff_ge]
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
    simp only [Fin.succ_le_succ_iff]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun a : Fin n => a ≤ j) = Finset.Iic j := by
      ext a
      simp
    rw [he, Fin.sum_Iic_sub]
    abel

/-- An empty itinerary realizes the straight ray with its prescribed direction. -/
@[simp]
theorem backwardRay_zero (f : Fin 0 → V →L[ℝ] ℝ) (c : Fin 0 → ℝ)
    (v : Fin 1 → V) (Q : V)
    (hpos : ∀ j, 0 < backwardTime f c (fun j => v j.castSucc) j Q) :
    backwardRay f c v Q hpos = FiniteAffineRay.straight Q (v 0) := by
  ext <;> simp

end Mei.Convex
