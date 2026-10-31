/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Module
import Mathlib.Tactic.FunProp

/-!
# Incoming rays with finitely many affine bends

A finite affine ray has an endpoint at time zero, a final direction, and a
finitely supported family of direction changes at negative times. Hinge
functions give its continuous realization without choices of interval charts.
Before all bends it agrees with one affine line.

These are the geometric paths underlying affine broken lines. Coefficient
decorations and wall-encounter conditions are additional data. The sign
convention is that the spatial velocity is the negative of the direction.
-/

public section

open Set Filter

namespace Mei

variable (V P : Type*) [AddCommGroup V]

/-- Finite direction changes at negative times, with a specified endpoint. -/
@[ext]
structure FiniteAffineRay where
  /-- Position at time zero. -/
  endpoint : P
  /-- Negative of the velocity after the final bend. -/
  direction : V
  /-- Direction increments when moving backwards across the bend times. -/
  bends : ℝ →₀ V
  /-- Every actual bend precedes the endpoint. -/
  bend_neg : ∀ t ∈ bends.support, t < 0

namespace FiniteAffineRay

variable {V P} [Module ℝ V] [AddTorsor V P]

/-- Realization of the finite ray, extended affinely past its endpoint. -/
def eval (β : FiniteAffineRay V P) (t : ℝ) : P :=
  (β.bends.sum (fun b v => max (b - t) 0 • v) - t • β.direction) +ᵥ β.endpoint

instance : CoeFun (FiniteAffineRay V P) (fun _ => ℝ → P) := ⟨eval⟩

/-- The hinge realization is the vector displacement applied to its endpoint. -/
theorem eval_def (β : FiniteAffineRay V P) (t : ℝ) :
    β t = (β.bends.sum (fun b v => max (b - t) 0 • v) - t • β.direction) +ᵥ β.endpoint := (rfl)

/-- The endpoint parameter reads the specified endpoint. -/
@[simp]
theorem eval_zero (β : FiniteAffineRay V P) : β 0 = β.endpoint := by
  classical
  rw [eval_def, zero_smul, sub_zero]
  have h : β.bends.sum (fun b v => max (b - 0) 0 • v) = 0 := by
    simp only [Finsupp.sum]
    apply Finset.sum_eq_zero
    intro b hb
    rw [sub_zero, max_eq_right (β.bend_neg b hb).le, zero_smul]
  rw [h, zero_vadd]

/-- The incoming direction is the final direction plus all direction increments. -/
def incomingDirection (β : FiniteAffineRay V P) : V :=
  β.direction + β.bends.sum (fun _ v => v)

/-- Reference position at zero of the incoming affine representative. -/
def incomingReference (β : FiniteAffineRay V P) : P :=
  β.bends.sum (fun b v => b • v) +ᵥ β.endpoint

omit [Module ℝ V] [AddTorsor V P] in
/-- The incoming direction is obtained by adding the finite increments. -/
theorem incomingDirection_def (β : FiniteAffineRay V P) :
    β.incomingDirection = β.direction + β.bends.sum (fun _ v => v) := (rfl)

/-- The incoming reference is the time-weighted vector displacement of the endpoint. -/
theorem incomingReference_def (β : FiniteAffineRay V P) :
    β.incomingReference = β.bends.sum (fun b v => b • v) +ᵥ β.endpoint := (rfl)

/-- A ray without bends, with its given endpoint and direction. -/
def straight (Q : P) (v : V) : FiniteAffineRay V P where
  endpoint := Q
  direction := v
  bends := 0
  bend_neg := by simp

omit [Module ℝ V] [AddTorsor V P] in
/-- An unbent ray has no direction increments. -/
@[simp]
theorem bends_straight (Q : P) (v : V) : (straight Q v).bends = 0 := (rfl)

omit [Module ℝ V] [AddTorsor V P] in
/-- An unbent ray has the specified endpoint. -/
@[simp]
theorem endpoint_straight (Q : P) (v : V) : (straight Q v).endpoint = Q := (rfl)

omit [Module ℝ V] [AddTorsor V P] in
/-- An unbent ray has the specified final direction. -/
@[simp]
theorem direction_straight (Q : P) (v : V) : (straight Q v).direction = v := (rfl)

omit [Module ℝ V] [AddTorsor V P] in
/-- A ray is the straight ray with its endpoint and direction exactly when it has no bends. -/
@[simp]
theorem eq_straight_iff (β : FiniteAffineRay V P) :
    β = straight β.endpoint β.direction ↔ β.bends = 0 := by
  constructor
  · intro h
    simpa only [bends_straight] using congrArg FiniteAffineRay.bends h
  · intro h
    apply FiniteAffineRay.ext <;> simp [h]

/-- The unbent ray is the affine half-line with negative velocity. -/
@[simp]
theorem straight_apply (Q : P) (v : V) (t : ℝ) : straight Q v t = (-t • v) +ᵥ Q := by
  simp [eval, straight]

omit [Module ℝ V] [AddTorsor V P] in
/-- An unbent ray retains its specified incoming direction. -/
@[simp]
theorem incomingDirection_straight (Q : P) (v : V) : (straight Q v).incomingDirection = v := by
  simp [incomingDirection, straight]

/-- The affine reference position of an unbent ray is its endpoint. -/
@[simp]
theorem incomingReference_straight (Q : P) (v : V) : (straight Q v).incomingReference = Q := by
  simp [incomingReference, straight]

/-- Add a direction increment at a negative time. Zero increments give artificial
subdivisions; increments at the same time combine in the existing finitely supported family. -/
noncomputable def insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) :
    FiniteAffineRay V P := by
  classical
  refine ⟨β.endpoint, β.direction, β.bends + Finsupp.single b δ, ?_⟩
  intro t ht
  rcases Finset.mem_union.mp (Finsupp.support_add ht) with h | h
  · exact β.bend_neg t h
  · have htb : t = b := Finset.mem_singleton.mp (Finsupp.support_single_subset h)
    exact htb ▸ hb

omit [Module ℝ V] [AddTorsor V P] in
/-- Insertion adds the increment to the finitely supported bend data. -/
@[simp]
theorem bends_insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).bends = β.bends + Finsupp.single b δ := (rfl)

omit [Module ℝ V] [AddTorsor V P] in
/-- A direction increment preserves the endpoint. -/
@[simp]
theorem endpoint_insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).endpoint = β.endpoint := (rfl)

omit [Module ℝ V] [AddTorsor V P] in
/-- A direction increment preserves the final direction. -/
@[simp]
theorem direction_insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).direction = β.direction := (rfl)

/-- A newly inserted bend contributes its hinge function to realization. -/
@[simp]
theorem insert_apply (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) (t : ℝ) :
    β.insert b δ hb t = max (b - t) 0 • δ +ᵥ β t := by
  classical
  dsimp [eval, insert]
  rw [Finsupp.sum_add_index' (fun b => smul_zero (max (b - t) 0))
    (fun b v w => smul_add (max (b - t) 0) v w),
    Finsupp.sum_single_index (h := fun b v => max (b - t) 0 • v)
      (smul_zero (max (b - t) 0)), vadd_vadd]
  congr 1
  abel

omit [Module ℝ V] [AddTorsor V P] in
/-- An artificial subdivision with unchanged velocity preserves the ray itself. -/
@[simp]
theorem insert_zero (β : FiniteAffineRay V P) (b : ℝ) (hb : b < 0) :
    β.insert b 0 hb = β := by
  ext <;> simp [insert]

omit [Module ℝ V] [AddTorsor V P] in
/-- Inserting a direction change adds it to the incoming direction. -/
@[simp]
theorem incomingDirection_insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).incomingDirection = β.incomingDirection + δ := by
  classical
  simp [incomingDirection, insert, Finsupp.sum_add_index', add_assoc]

/-- A bend at time `b` shifts the incoming affine reference position by `b • δ`. -/
@[simp]
theorem incomingReference_insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) :
    (β.insert b δ hb).incomingReference = b • δ +ᵥ β.incomingReference := by
  classical
  simp [incomingReference, insert, Finsupp.sum_add_index', smul_add, vadd_vadd, add_comm]

omit [Module ℝ V] [AddTorsor V P] in
/-- Direction increments at the same time combine into a single bend. -/
@[simp]
theorem insert_insert_same (β : FiniteAffineRay V P) (b : ℝ) (δ ε : V) (hb : b < 0) :
    (β.insert b δ hb).insert b ε hb = β.insert b (δ + ε) hb := by
  ext <;> simp [insert, Finsupp.single_add, add_assoc]

/-- Direction on an interval ending at `t`, including bends at its right endpoint. -/
noncomputable def directionAt (β : FiniteAffineRay V P) (t : ℝ) : V :=
  β.direction + β.bends.sum (fun b v => if t ≤ b then v else 0)

omit [Module ℝ V] [AddTorsor V P] in
/-- Interval direction includes exactly increments at or after its right endpoint. -/
theorem directionAt_def (β : FiniteAffineRay V P) (t : ℝ) :
    β.directionAt t = β.direction + β.bends.sum (fun b v => if t ≤ b then v else 0) := (rfl)

omit [Module ℝ V] [AddTorsor V P] in
/-- An unbent ray has the same direction on every interval. -/
@[simp]
theorem directionAt_straight (Q : P) (v : V) (t : ℝ) : (straight Q v).directionAt t = v := by
  simp [directionAt, straight]

omit [Module ℝ V] [AddTorsor V P] in
/-- A bend contributes to the direction on its incoming side, including at the bend. -/
@[simp]
theorem directionAt_insert (β : FiniteAffineRay V P) (b : ℝ) (δ : V) (hb : b < 0) (t : ℝ) :
    (β.insert b δ hb).directionAt t = β.directionAt t + if t ≤ b then δ else 0 := by
  classical
  dsimp [directionAt, insert]
  rw [Finsupp.sum_add_index' (fun _ => by split <;> rfl)
      (fun _ v w => by split <;> simp),
    Finsupp.sum_single_index (h := fun b v => if t ≤ b then v else 0) (by split <;> rfl)]
  abel

omit [Module ℝ V] [AddTorsor V P] in
/-- Before all bends, the interval direction is the incoming direction. -/
theorem directionAt_of_le_bends (β : FiniteAffineRay V P) (t : ℝ)
    (ht : ∀ b ∈ β.bends.support, t ≤ b) : β.directionAt t = β.incomingDirection := by
  rw [directionAt_def, incomingDirection_def]
  congr 1
  exact Finsupp.sum_congr fun b hb => ite_eq_left (ht b hb)

omit [Module ℝ V] [AddTorsor V P] in
/-- At and after the endpoint, the interval direction is the final direction. -/
@[simp]
theorem directionAt_of_nonneg (β : FiniteAffineRay V P) {u : ℝ} (hu : 0 ≤ u) :
    β.directionAt u = β.direction := by
  classical
  rw [directionAt_def]
  have h : β.bends.sum (fun b v => if u ≤ b then v else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    exact ite_eq_right ((β.bend_neg b hb).trans_le hu).not_ge
  rw [h, add_zero]

omit [Module ℝ V] [AddTorsor V P] in
/-- Across an interval with no interior bend, the change of direction is exactly
the increment at its left endpoint. A bend at the right endpoint is already
included in both incoming directions. -/
theorem directionAt_sub_eq_bends (β : FiniteAffineRay V P) {s t : ℝ} (hst : s < t)
    (hb : ∀ b ∈ β.bends.support, b ≤ s ∨ t ≤ b) :
    β.directionAt s - β.directionAt t = β.bends s := by
  classical
  have hterm : ∀ b ∈ β.bends.support, (if s ≤ b then β.bends b else 0) =
      (if t ≤ b then β.bends b else 0) + if b = s then β.bends b else 0 := by
    intro b hb'
    rcases hb b hb' with h | h
    · rcases h.lt_or_eq with h | rfl
      · simp [h.not_ge, (h.trans hst).not_ge, h.ne]
      · simp [hst.not_ge]
    · simp [hst.le.trans h, h, (hst.trans_le h).ne']
  have hsum : β.bends.sum (fun b w => if s ≤ b then w else 0) =
      β.bends.sum (fun b w => (if t ≤ b then w else 0) + if b = s then w else 0) :=
    Finsupp.sum_congr hterm
  rw [directionAt_def, directionAt_def, hsum,
    Finsupp.sum_add, Finsupp.sum_ite_self_eq']
  abel

/-- On any interval without an interior bend, realization has the stated constant velocity. -/
theorem eval_vsub_eval (β : FiniteAffineRay V P) {s t : ℝ} (hst : s ≤ t)
    (hb : ∀ b ∈ β.bends.support, b ≤ s ∨ t ≤ b) :
    β t -ᵥ β s = (s - t) • β.directionAt t := by
  classical
  have h : β.bends.sum (fun b v => max (b - t) 0 • v) -
      β.bends.sum (fun b v => max (b - s) 0 • v) =
        (s - t) • β.bends.sum (fun b v => if t ≤ b then v else 0) := by
    simp only [Finsupp.sum]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b hmem
    rcases hb b hmem with hbs | htb
    · by_cases htb : t ≤ b
      · have hst' : s = t := le_antisymm hst (htb.trans hbs)
        subst t
        simp
      · rw [max_eq_right (sub_nonpos.mpr (hbs.trans hst)),
          max_eq_right (sub_nonpos.mpr hbs), ite_eq_right htb]
        simp
    · rw [max_eq_left (sub_nonneg.mpr htb),
        max_eq_left (sub_nonneg.mpr (hst.trans htb)), ite_eq_left htb, ← sub_smul]
      congr 1
      abel
  calc
    β t -ᵥ β s = (s - t) • β.direction +
        (β.bends.sum (fun b v => max (b - t) 0 • v) -
          β.bends.sum (fun b v => max (b - s) 0 • v)) := by
      rw [eval_def, eval_def, vadd_vsub_vadd_cancel_right]
      simp only [sub_smul]
      module
    _ = (s - t) • β.directionAt t := by rw [h, directionAt, smul_add]

/-- Past the endpoint, realization continues in the final direction. -/
theorem eval_of_nonneg (β : FiniteAffineRay V P) {t : ℝ} (ht : 0 ≤ t) :
    β t = (-t • β.direction) +ᵥ β.endpoint := by
  have he := β.eval_vsub_eval ht (fun b hb => Or.inl (β.bend_neg b hb).le)
  rw [eval_zero, directionAt_of_nonneg β ht, zero_sub] at he
  rw [← he, vsub_vadd]

/-- Before all bends, realization is the incoming affine formula. -/
theorem eval_of_le_bends (β : FiniteAffineRay V P) (t : ℝ)
    (ht : ∀ b ∈ β.bends.support, t ≤ b) :
    β t = (-t • β.incomingDirection) +ᵥ β.incomingReference := by
  classical
  have h : β.bends.sum (fun b v => max (b - t) 0 • v) =
      β.bends.sum (fun b v => b • v) - t • β.bends.sum (fun _ v => v) := by
    simp only [Finsupp.sum]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [max_eq_left (sub_nonneg.mpr (ht b hb)), sub_smul]
  rw [eval, h, incomingReference, incomingDirection, smul_add, vadd_vadd]
  congr 1
  module

section Topology

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace P] [ContinuousVAdd V P]

/-- The hinge realization is continuous, including at every bend time. -/
theorem continuous (β : FiniteAffineRay V P) : Continuous β := by
  classical
  unfold eval
  simp only [Finsupp.sum]
  fun_prop

/-- The continuous path realizing the finite ray, including its affine continuation
past the endpoint. -/
def toContinuousMap (β : FiniteAffineRay V P) : C(ℝ, P) :=
  ⟨β, β.continuous⟩

/-- The bundled continuous path evaluates as the finite ray. -/
@[simp]
theorem toContinuousMap_apply (β : FiniteAffineRay V P) (t : ℝ) :
    β.toContinuousMap t = β t := (rfl)

/-- The affine line representing the incoming germ of the bent ray. -/
def incomingLine (β : FiniteAffineRay V P) : ℝ →ᴬ[ℝ] P :=
  ContinuousAffineMap.lineMap β.incomingReference (-β.incomingDirection +ᵥ β.incomingReference)

omit [IsTopologicalAddGroup V] in
/-- Evaluation of the canonical incoming line. -/
@[simp]
theorem incomingLine_apply (β : FiniteAffineRay V P) (t : ℝ) :
    β.incomingLine t = (-t • β.incomingDirection) +ᵥ β.incomingReference := by
  simp [incomingLine, ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply, neg_smul]

omit [IsTopologicalAddGroup V] in
/-- The finite realization agrees with its incoming affine line near negative infinity. -/
theorem eventuallyEq_incomingLine (β : FiniteAffineRay V P) :
    (β : ℝ → P) =ᶠ[atBot] β.incomingLine := by
  filter_upwards [(β.bends.support.eventually_all).mpr
    (fun b _ => eventually_le_atBot b)] with t ht
  exact (β.eval_of_le_bends t ht).trans (β.incomingLine_apply t).symm

omit [IsTopologicalAddGroup V] in
/-- The incoming affine line has the prescribed negative velocity. -/
@[simp]
theorem incomingLine_velocity (β : FiniteAffineRay V P) :
    β.incomingLine.linear 1 = -β.incomingDirection := by
  simp [incomingLine]

end Topology

section Proper

variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [TopologicalSpace P] [IsTopologicalAddTorsor P] [T2Space V]

/-- Every closed incoming half-line is proper when the incoming direction is nonzero.
Finitely many bends may include zero-velocity segments without affecting properness. -/
theorem isProperMap_restrict_Iic (β : FiniteAffineRay V P) (hv : β.incomingDirection ≠ 0)
    (b : ℝ) : IsProperMap (fun t : Iic b => β t) := by
  apply β.incomingLine.isProperMap_restrict_Iic_of_eventuallyEq β.continuous
    β.eventuallyEq_incomingLine _ b
  simpa only [ContinuousAffineMap.coe_contLinear, incomingLine_velocity, neg_ne_zero] using hv

end Proper

end FiniteAffineRay
end Mei
